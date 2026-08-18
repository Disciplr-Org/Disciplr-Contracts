#![cfg(test)]

//! Isolation coverage across several concurrent vaults.
//!
//! Every vault lives in the same contract instance and its escrow sits in the
//! same contract balance. `test_create_vault_increments_id` proves IDs advance,
//! but nothing proved that money and status stay attached to the right ID once
//! several vaults are open at once and take different exits.
//!
//! These tests open four vaults with **different amounts** on purpose: if funds
//! ever bled between vaults the assertion fails on a wrong number rather than
//! silently passing because every vault happened to hold the same figure.

use soroban_sdk::{
    testutils::{Address as _, Ledger},
    token::{StellarAssetClient, TokenClient},
    Address, BytesN, Env,
};

use disciplr_vault::{DisciplrVault, DisciplrVaultClient, VaultStatus, MIN_AMOUNT};

const NOW: u64 = 1_700_000_000;
const WINDOW: u64 = 86_400;

/// Distinct amounts so any cross contamination shows up as a wrong balance.
const AMOUNT_RELEASED: i128 = MIN_AMOUNT;
const AMOUNT_REDIRECTED: i128 = MIN_AMOUNT * 3;
const AMOUNT_CANCELLED: i128 = MIN_AMOUNT * 7;
const AMOUNT_UNTOUCHED: i128 = MIN_AMOUNT * 11;

struct Fixture {
    env: Env,
    client: DisciplrVaultClient<'static>,
    contract_id: Address,
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
        contract_id,
        usdc,
        token,
    }
}

/// One vault plus the addresses that belong to it, so a test can assert against
/// the right destination without mixing them up.
struct Vault {
    id: u32,
    creator: Address,
    success: Address,
    failure: Address,
    amount: i128,
}

/// Creates a vault with its own creator and its own destinations, funded with
/// exactly `amount` and nothing more. Minting the exact escrow means a later
/// balance assertion cannot be satisfied by leftover funds.
fn open_vault(f: &Fixture, amount: i128, verifier: Option<Address>) -> Vault {
    let creator = Address::generate(&f.env);
    let success = Address::generate(&f.env);
    let failure = Address::generate(&f.env);

    StellarAssetClient::new(&f.env, &f.usdc).mint(&creator, &amount);

    let id = f.client.create_vault(
        &f.usdc,
        &creator,
        &amount,
        &NOW,
        &(NOW + WINDOW),
        &BytesN::from_array(&f.env, &[5u8; 32]),
        &verifier,
        &success,
        &failure,
    );

    Vault {
        id,
        creator,
        success,
        failure,
        amount,
    }
}

/// Four vaults, three different terminal states plus one left open, and every
/// balance lands exactly where its own vault said it should.
#[test]
fn concurrent_vaults_do_not_contaminate_each_other() {
    let f = setup();

    let verifier = Address::generate(&f.env);

    let released = open_vault(&f, AMOUNT_RELEASED, Some(verifier));
    let redirected = open_vault(&f, AMOUNT_REDIRECTED, None);
    let cancelled = open_vault(&f, AMOUNT_CANCELLED, None);
    let untouched = open_vault(&f, AMOUNT_UNTOUCHED, None);

    // IDs come from a single monotonic counter.
    assert_eq!(released.id, 0);
    assert_eq!(redirected.id, 1);
    assert_eq!(cancelled.id, 2);
    assert_eq!(untouched.id, 3);
    assert_eq!(f.client.vault_count(), 4);

    let total_escrow = AMOUNT_RELEASED + AMOUNT_REDIRECTED + AMOUNT_CANCELLED + AMOUNT_UNTOUCHED;
    assert_eq!(
        f.token.balance(&f.contract_id),
        total_escrow,
        "el contrato tiene que custodiar la suma exacta de los cuatro vaults"
    );

    // Vault 0 takes the success exit, validated inside the window.
    f.env.ledger().set_timestamp(NOW + 3_600);
    f.client.validate_milestone(&released.id);

    // Vault 2 is cancelled while still active.
    f.client.cancel_vault(&cancelled.id, &f.usdc);

    // Past the deadline, vault 1 is swept to failure and vault 0 is released.
    f.env.ledger().set_timestamp(NOW + WINDOW + 1);
    f.client.redirect_funds(&redirected.id, &f.usdc);
    f.client.release_funds(&released.id, &f.usdc);

    // ---- statuses stay independent ----
    assert_eq!(
        f.client.get_vault_state(&released.id).unwrap().status,
        VaultStatus::Completed
    );
    assert_eq!(
        f.client.get_vault_state(&redirected.id).unwrap().status,
        VaultStatus::Failed
    );
    assert_eq!(
        f.client.get_vault_state(&cancelled.id).unwrap().status,
        VaultStatus::Cancelled
    );
    assert_eq!(
        f.client.get_vault_state(&untouched.id).unwrap().status,
        VaultStatus::Active,
        "el cuarto vault no puede haberse movido por lo que paso en los otros"
    );

    // ---- money lands exactly where its own vault said ----
    assert_eq!(f.token.balance(&released.success), released.amount);
    assert_eq!(f.token.balance(&released.failure), 0);

    assert_eq!(f.token.balance(&redirected.failure), redirected.amount);
    assert_eq!(f.token.balance(&redirected.success), 0);

    assert_eq!(
        f.token.balance(&cancelled.creator),
        cancelled.amount,
        "cancel devuelve al creador de ESE vault, no a otro"
    );
    assert_eq!(f.token.balance(&cancelled.success), 0);
    assert_eq!(f.token.balance(&cancelled.failure), 0);

    assert_eq!(f.token.balance(&untouched.success), 0);
    assert_eq!(f.token.balance(&untouched.failure), 0);

    // ---- creators of the settled vaults got nothing back ----
    assert_eq!(
        f.token.balance(&released.creator),
        0,
        "el creador del vault liberado no recupera nada"
    );
    assert_eq!(f.token.balance(&redirected.creator), 0);

    // ---- the contract keeps exactly the escrow still open ----
    assert_eq!(
        f.token.balance(&f.contract_id),
        untouched.amount,
        "solo debe quedar en custodia el vault que sigue activo"
    );
}

/// Each vault's own fields survive independently: the verifier configuration of
/// one vault must not leak into another.
#[test]
fn vault_records_keep_their_own_configuration() {
    let f = setup();

    let verifier = Address::generate(&f.env);
    let with_verifier = open_vault(&f, AMOUNT_RELEASED, Some(verifier.clone()));
    let without_verifier = open_vault(&f, AMOUNT_REDIRECTED, None);

    let a = f.client.get_vault_state(&with_verifier.id).unwrap();
    let b = f.client.get_vault_state(&without_verifier.id).unwrap();

    assert_eq!(a.verifier, Some(verifier));
    assert_eq!(b.verifier, None);

    assert_eq!(a.amount, AMOUNT_RELEASED);
    assert_eq!(b.amount, AMOUNT_REDIRECTED);

    assert_eq!(a.creator, with_verifier.creator);
    assert_eq!(b.creator, without_verifier.creator);

    assert_eq!(a.success_destination, with_verifier.success);
    assert_eq!(b.success_destination, without_verifier.success);

    assert_ne!(a.creator, b.creator);
    assert_ne!(a.success_destination, b.success_destination);
}

/// Validating one vault must not validate its neighbours. This is the
/// per-vault flag equivalent of the balance isolation above.
#[test]
fn validating_one_vault_leaves_the_others_unvalidated() {
    let f = setup();

    let verifier = Address::generate(&f.env);
    let target = open_vault(&f, AMOUNT_RELEASED, Some(verifier));
    let neighbour_a = open_vault(&f, AMOUNT_REDIRECTED, None);
    let neighbour_b = open_vault(&f, AMOUNT_CANCELLED, None);

    f.env.ledger().set_timestamp(NOW + 3_600);
    f.client.validate_milestone(&target.id);

    assert!(
        f.client
            .get_vault_state(&target.id)
            .unwrap()
            .milestone_validated
    );
    assert!(
        !f.client
            .get_vault_state(&neighbour_a.id)
            .unwrap()
            .milestone_validated
    );
    assert!(
        !f.client
            .get_vault_state(&neighbour_b.id)
            .unwrap()
            .milestone_validated
    );

    // And the consequence: the neighbours can still be redirected, the target
    // cannot.
    f.env.ledger().set_timestamp(NOW + WINDOW + 1);
    f.client.redirect_funds(&neighbour_a.id, &f.usdc);
    assert_eq!(f.token.balance(&neighbour_a.failure), AMOUNT_REDIRECTED);

    assert!(
        f.client.try_redirect_funds(&target.id, &f.usdc).is_err(),
        "el vault validado sigue protegido aunque su vecino se haya redirigido"
    );
}

/// `vault_count` counts assignments, and settling a vault does not decrement it
/// or free its ID for reuse.
#[test]
fn vault_count_never_goes_backwards() {
    let f = setup();

    let first = open_vault(&f, AMOUNT_RELEASED, None);
    assert_eq!(f.client.vault_count(), 1);

    f.client.cancel_vault(&first.id, &f.usdc);
    assert_eq!(
        f.client.vault_count(),
        1,
        "cancelar no libera el id ni baja el contador"
    );

    let second = open_vault(&f, AMOUNT_REDIRECTED, None);
    assert_eq!(
        second.id, 1,
        "el id nuevo no reutiliza el del vault cancelado"
    );
    assert_eq!(f.client.vault_count(), 2);

    // The cancelled vault stays readable with its terminal status.
    assert_eq!(
        f.client.get_vault_state(&first.id).unwrap().status,
        VaultStatus::Cancelled
    );
    assert_eq!(
        f.client.get_vault_state(&second.id).unwrap().status,
        VaultStatus::Active
    );
}

/// An ID that was never assigned returns `None`, and that must not change just
/// because other vaults exist.
#[test]
fn unassigned_ids_return_none() {
    let f = setup();

    open_vault(&f, AMOUNT_RELEASED, None);
    open_vault(&f, AMOUNT_REDIRECTED, None);

    assert!(f.client.get_vault_state(&0).is_some());
    assert!(f.client.get_vault_state(&1).is_some());
    assert!(
        f.client.get_vault_state(&2).is_none(),
        "el id siguiente al ultimo asignado todavia no existe"
    );
    assert!(f.client.get_vault_state(&999).is_none());
}
