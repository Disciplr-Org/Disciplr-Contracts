#![cfg(test)]

//! Coverage for the validated-blocks-redirect guard in `redirect_funds`.
//!
//! `redirect_funds` is the only lifecycle entry point that does **not** call
//! `require_auth` on anybody: after `end_timestamp` any address on the network
//! can invoke it. Its single defence against sweeping a validated vault into
//! `failure_destination` is the `vault.milestone_validated` check, which returns
//! `Error::NotAuthorized`.
//!
//! That makes this branch security critical: if it ever regressed, a stranger
//! could take funds that the verifier had already signed off as earned and send
//! them to the failure address. These tests pin the exact ordering
//! create -> validate -> past deadline -> redirect, and prove that the money
//! stays claimable through `release_funds`.

use soroban_sdk::{
    testutils::{Address as _, Ledger},
    token::{StellarAssetClient, TokenClient},
    Address, BytesN, Env,
};

use disciplr_vault::{DisciplrVault, DisciplrVaultClient, Error, VaultStatus, MIN_AMOUNT};

/// Fixed ledger time so every run is deterministic.
const NOW: u64 = 1_700_000_000;
/// Vault window used across these tests.
const WINDOW: u64 = 86_400;

struct Fixture {
    env: Env,
    client: DisciplrVaultClient<'static>,
    usdc: Address,
    token: TokenClient<'static>,
}

fn setup() -> Fixture {
    let env = Env::default();
    env.mock_all_auths();

    let contract_id = env.register(DisciplrVault, ());
    let client = DisciplrVaultClient::new(&env, &contract_id);

    let usdc_admin = Address::generate(&env);
    let usdc_token = env.register_stellar_asset_contract_v2(usdc_admin);
    let usdc = usdc_token.address();
    let token = TokenClient::new(&env, &usdc);

    env.ledger().set_timestamp(NOW);

    Fixture {
        env,
        client,
        usdc,
        token,
    }
}

/// Creates a funded, validated vault and returns
/// `(vault_id, success_destination, failure_destination)`.
///
/// The vault is left with the ledger clock still inside its window, so the
/// caller decides when to move past the deadline.
fn validated_vault(f: &Fixture, amount: i128) -> (u32, Address, Address) {
    let creator = Address::generate(&f.env);
    let verifier = Address::generate(&f.env);
    let success = Address::generate(&f.env);
    let failure = Address::generate(&f.env);

    let usdc_asset = StellarAssetClient::new(&f.env, &f.usdc);
    usdc_asset.mint(&creator, &amount);

    let vault_id = f.client.create_vault(
        &f.usdc,
        &creator,
        &amount,
        &NOW,
        &(NOW + WINDOW),
        &BytesN::from_array(&f.env, &[9u8; 32]),
        &Some(verifier),
        &success,
        &failure,
    );

    // Validate while still inside the window: validate_milestone rejects with
    // MilestoneExpired once now >= end_timestamp.
    f.env.ledger().set_timestamp(NOW + 3_600);
    f.client.validate_milestone(&vault_id);

    assert!(
        f.client
            .get_vault_state(&vault_id)
            .unwrap()
            .milestone_validated,
        "precondicion: el vault tiene que quedar validado"
    );

    (vault_id, success, failure)
}

/// The core guard: a validated vault cannot be redirected once past the
/// deadline, and the rejection leaves both the status and the failure
/// destination untouched.
#[test]
fn validated_vault_cannot_be_redirected_after_deadline() {
    let f = setup();
    let (vault_id, _success, failure) = validated_vault(&f, MIN_AMOUNT);

    // Move strictly past end_timestamp. redirect_funds rejects with
    // InvalidTimestamp while now <= end_timestamp, so this is what lets the
    // call reach the milestone_validated check at all.
    f.env.ledger().set_timestamp(NOW + WINDOW + 1);

    let failure_before = f.token.balance(&failure);

    let result = f.client.try_redirect_funds(&vault_id, &f.usdc);
    assert_eq!(
        result,
        Err(Ok(Error::NotAuthorized)),
        "un vault validado no puede redirigirse a failure_destination"
    );

    let state = f.client.get_vault_state(&vault_id).unwrap();
    assert_eq!(
        state.status,
        VaultStatus::Active,
        "el redirect rechazado no puede mover el vault fuera de Active"
    );
    assert!(
        state.milestone_validated,
        "el redirect rechazado no puede borrar la validacion"
    );
    assert_eq!(
        f.token.balance(&failure),
        failure_before,
        "failure_destination no puede recibir un solo stroop"
    );
}

/// After the redirect is rejected, the money must still be claimable: the whole
/// point of the guard is that a validated milestone pays success.
#[test]
fn release_still_works_after_redirect_is_rejected() {
    let f = setup();
    let (vault_id, success, failure) = validated_vault(&f, MIN_AMOUNT);

    f.env.ledger().set_timestamp(NOW + WINDOW + 1);

    assert_eq!(
        f.client.try_redirect_funds(&vault_id, &f.usdc),
        Err(Ok(Error::NotAuthorized))
    );

    // The vault is still Active, so release_funds is available. Past the
    // deadline the release path is open regardless of validation, but the
    // destination is what matters here.
    f.client.release_funds(&vault_id, &f.usdc);

    let state = f.client.get_vault_state(&vault_id).unwrap();
    assert_eq!(state.status, VaultStatus::Completed);
    assert_eq!(
        f.token.balance(&success),
        MIN_AMOUNT,
        "los fondos tienen que llegar enteros a success_destination"
    );
    assert_eq!(
        f.token.balance(&failure),
        0,
        "failure_destination sigue en cero despues del release"
    );
}

/// Redirecting twice must not become possible by repetition: the guard is not a
/// rate limit, it is a permanent property of a validated vault.
#[test]
fn repeated_redirect_attempts_keep_failing() {
    let f = setup();
    let (vault_id, _success, failure) = validated_vault(&f, MIN_AMOUNT);

    f.env.ledger().set_timestamp(NOW + WINDOW + 1);

    for attempt in 0..3 {
        assert_eq!(
            f.client.try_redirect_funds(&vault_id, &f.usdc),
            Err(Ok(Error::NotAuthorized)),
            "intento {attempt} deberia seguir rechazado"
        );
    }

    assert_eq!(f.token.balance(&failure), 0);
    assert_eq!(
        f.client.get_vault_state(&vault_id).unwrap().status,
        VaultStatus::Active
    );
}

/// The mirror image, to prove the guard is about validation and not about the
/// deadline: an unvalidated vault past its deadline *does* redirect. Without
/// this the tests above would also pass if redirect_funds were broken outright.
#[test]
fn unvalidated_vault_redirects_normally_after_deadline() {
    let f = setup();

    let creator = Address::generate(&f.env);
    let success = Address::generate(&f.env);
    let failure = Address::generate(&f.env);

    StellarAssetClient::new(&f.env, &f.usdc).mint(&creator, &MIN_AMOUNT);

    let vault_id = f.client.create_vault(
        &f.usdc,
        &creator,
        &MIN_AMOUNT,
        &NOW,
        &(NOW + WINDOW),
        &BytesN::from_array(&f.env, &[9u8; 32]),
        &None,
        &success,
        &failure,
    );

    f.env.ledger().set_timestamp(NOW + WINDOW + 1);
    f.client.redirect_funds(&vault_id, &f.usdc);

    let state = f.client.get_vault_state(&vault_id).unwrap();
    assert_eq!(state.status, VaultStatus::Failed);
    assert_eq!(f.token.balance(&failure), MIN_AMOUNT);
    assert_eq!(f.token.balance(&success), 0);
}

/// The guard has to hold at the first instant redirect becomes reachable, not
/// only comfortably past the deadline. `redirect_funds` rejects while
/// `now <= end_timestamp`, so `end_timestamp + 1` is the earliest moment the
/// milestone_validated check is evaluated at all.
#[test]
fn guard_holds_at_the_first_redirectable_timestamp() {
    let f = setup();
    let (vault_id, _success, failure) = validated_vault(&f, MIN_AMOUNT);

    // One second earlier the call is refused for being too early, which would
    // pass the assertion below for the wrong reason. Pin both.
    f.env.ledger().set_timestamp(NOW + WINDOW);
    assert_eq!(
        f.client.try_redirect_funds(&vault_id, &f.usdc),
        Err(Ok(Error::InvalidTimestamp)),
        "en end_timestamp exacto el rechazo es por tiempo, no por validacion"
    );

    f.env.ledger().set_timestamp(NOW + WINDOW + 1);
    assert_eq!(
        f.client.try_redirect_funds(&vault_id, &f.usdc),
        Err(Ok(Error::NotAuthorized)),
        "en el primer instante redirigible el rechazo ya es por validacion"
    );

    assert_eq!(f.token.balance(&failure), 0);
}
