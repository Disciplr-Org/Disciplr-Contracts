#![cfg(test)]

//! Negative authorization coverage for `validate_milestone`.
//!
//! `validate_milestone` gates on `verifier.require_auth()` when a verifier is
//! set, and on `creator.require_auth()` when it is `None`. The rest of the suite
//! runs under `env.mock_all_auths()`, which authorises everybody and therefore
//! can never observe a rejection: a regression that dropped the `require_auth`
//! call entirely would keep every existing test green.
//!
//! These tests use scoped auth (`env.mock_auths`) so that unauthorised calls
//! genuinely fail, and assert that a rejected call leaves `milestone_validated`
//! untouched.

use soroban_sdk::{
    testutils::{Address as _, Ledger, MockAuth, MockAuthInvoke},
    token::StellarAssetClient,
    Address, BytesN, Env, IntoVal,
};

use disciplr_vault::{DisciplrVault, DisciplrVaultClient, MIN_AMOUNT};

const NOW: u64 = 1_700_000_000;
const WINDOW: u64 = 86_400;

struct Fixture {
    env: Env,
    client: DisciplrVaultClient<'static>,
    contract_id: Address,
    usdc: Address,
}

fn setup() -> Fixture {
    let env = Env::default();
    // Broad auth only while we build the fixture. Every test narrows it before
    // the call under test.
    env.mock_all_auths();

    let contract_id = env.register(DisciplrVault, ());
    let client = DisciplrVaultClient::new(&env, &contract_id);

    let usdc_admin = Address::generate(&env);
    let usdc_token = env.register_stellar_asset_contract_v2(usdc_admin);
    let usdc = usdc_token.address();

    env.ledger().set_timestamp(NOW);

    Fixture {
        env,
        client,
        contract_id,
        usdc,
    }
}

/// Creates an active, unvalidated vault with the given verifier configuration.
fn make_vault(f: &Fixture, creator: &Address, verifier: &Option<Address>) -> u32 {
    StellarAssetClient::new(&f.env, &f.usdc).mint(creator, &MIN_AMOUNT);

    f.client.create_vault(
        &f.usdc,
        creator,
        &MIN_AMOUNT,
        &NOW,
        &(NOW + WINDOW),
        &BytesN::from_array(&f.env, &[3u8; 32]),
        verifier,
        &Address::generate(&f.env),
        &Address::generate(&f.env),
    )
}

/// Scopes auth to exactly one address authorising exactly this
/// `validate_milestone(vault_id)` invocation.
fn authorize_validate(f: &Fixture, who: &Address, vault_id: u32) {
    f.env.mock_auths(&[MockAuth {
        address: who,
        invoke: &MockAuthInvoke {
            contract: &f.contract_id,
            fn_name: "validate_milestone",
            args: (vault_id,).into_val(&f.env),
            sub_invokes: &[],
        },
    }]);
}

// ---------------------------------------------------------------------------
// verifier = Some(addr)
// ---------------------------------------------------------------------------

#[test]
fn designated_verifier_can_validate() {
    let f = setup();
    let creator = Address::generate(&f.env);
    let verifier = Address::generate(&f.env);
    let vault_id = make_vault(&f, &creator, &Some(verifier.clone()));

    authorize_validate(&f, &verifier, vault_id);
    f.client.validate_milestone(&vault_id);

    assert!(
        f.client
            .get_vault_state(&vault_id)
            .unwrap()
            .milestone_validated
    );
}

#[test]
fn stranger_cannot_validate_when_verifier_is_set() {
    let f = setup();
    let creator = Address::generate(&f.env);
    let verifier = Address::generate(&f.env);
    let stranger = Address::generate(&f.env);
    let vault_id = make_vault(&f, &creator, &Some(verifier));

    // The stranger authorises the call, but the contract demands the verifier.
    authorize_validate(&f, &stranger, vault_id);

    assert!(
        f.client.try_validate_milestone(&vault_id).is_err(),
        "un tercero no puede validar cuando hay verifier designado"
    );
    assert!(
        !f.client
            .get_vault_state(&vault_id)
            .unwrap()
            .milestone_validated,
        "la llamada rechazada no puede dejar el vault validado"
    );
}

/// The creator is not special when a verifier exists: delegating validation
/// means giving it away.
#[test]
fn creator_cannot_validate_when_verifier_is_set() {
    let f = setup();
    let creator = Address::generate(&f.env);
    let verifier = Address::generate(&f.env);
    let vault_id = make_vault(&f, &creator, &Some(verifier));

    authorize_validate(&f, &creator, vault_id);

    assert!(
        f.client.try_validate_milestone(&vault_id).is_err(),
        "el creador no puede validar si designo un verifier"
    );
    assert!(
        !f.client
            .get_vault_state(&vault_id)
            .unwrap()
            .milestone_validated
    );
}

// ---------------------------------------------------------------------------
// verifier = None
// ---------------------------------------------------------------------------

#[test]
fn creator_can_validate_when_verifier_is_none() {
    let f = setup();
    let creator = Address::generate(&f.env);
    let vault_id = make_vault(&f, &creator, &None);

    authorize_validate(&f, &creator, vault_id);
    f.client.validate_milestone(&vault_id);

    assert!(
        f.client
            .get_vault_state(&vault_id)
            .unwrap()
            .milestone_validated
    );
}

#[test]
fn non_creator_cannot_validate_when_verifier_is_none() {
    let f = setup();
    let creator = Address::generate(&f.env);
    let stranger = Address::generate(&f.env);
    let vault_id = make_vault(&f, &creator, &None);

    authorize_validate(&f, &stranger, vault_id);

    assert!(
        f.client.try_validate_milestone(&vault_id).is_err(),
        "sin verifier, solo el creador valida"
    );
    assert!(
        !f.client
            .get_vault_state(&vault_id)
            .unwrap()
            .milestone_validated
    );
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

/// With nobody authorised at all, the call must fail. This is the case that
/// catches an outright removal of `require_auth`: it would pass every other
/// test in this file, because those all authorise somebody.
#[test]
fn no_authorization_at_all_is_rejected() {
    let f = setup();
    let creator = Address::generate(&f.env);
    let verifier = Address::generate(&f.env);
    let vault_id = make_vault(&f, &creator, &Some(verifier));

    f.env.mock_auths(&[]);

    assert!(
        f.client.try_validate_milestone(&vault_id).is_err(),
        "sin ninguna autorizacion la llamada no puede pasar"
    );
    assert!(
        !f.client
            .get_vault_state(&vault_id)
            .unwrap()
            .milestone_validated
    );
}

/// When the creator names itself as verifier both branches point at the same
/// address, so the authorised call must succeed and a stranger must still fail.
#[test]
fn verifier_equal_to_creator_behaves_consistently() {
    let f = setup();
    let creator = Address::generate(&f.env);
    let stranger = Address::generate(&f.env);
    let vault_id = make_vault(&f, &creator, &Some(creator.clone()));

    authorize_validate(&f, &stranger, vault_id);
    assert!(
        f.client.try_validate_milestone(&vault_id).is_err(),
        "un tercero sigue sin poder validar aunque verifier == creator"
    );
    assert!(
        !f.client
            .get_vault_state(&vault_id)
            .unwrap()
            .milestone_validated
    );

    authorize_validate(&f, &creator, vault_id);
    f.client.validate_milestone(&vault_id);
    assert!(
        f.client
            .get_vault_state(&vault_id)
            .unwrap()
            .milestone_validated
    );
}

/// Authorising the right address for the wrong vault must not work either: the
/// scoped auth carries the arguments, so a signature for vault 0 cannot be
/// replayed against vault 1.
#[test]
fn authorization_is_scoped_to_the_vault_id() {
    let f = setup();
    let creator = Address::generate(&f.env);
    let verifier = Address::generate(&f.env);

    let first = make_vault(&f, &creator, &Some(verifier.clone()));
    let second = make_vault(&f, &creator, &Some(verifier.clone()));
    assert_ne!(first, second);

    // Authorise validation of the first vault, then try to validate the second.
    authorize_validate(&f, &verifier, first);

    assert!(
        f.client.try_validate_milestone(&second).is_err(),
        "una autorizacion para un vault no sirve para otro"
    );
    assert!(
        !f.client
            .get_vault_state(&second)
            .unwrap()
            .milestone_validated
    );

    // The vault the auth was actually for still validates.
    f.client.validate_milestone(&first);
    assert!(
        f.client
            .get_vault_state(&first)
            .unwrap()
            .milestone_validated
    );
}
