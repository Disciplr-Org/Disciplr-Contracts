#![cfg(test)]

use super::*;
use soroban_sdk::{
    testutils::{Address as _, Events, Ledger},
    vec, Env, IntoVal,
};

// ── helpers ──────────────────────────────────────────────────────────────

/// Bootstrap a test env with mock auths and common addresses.
fn setup() -> (
    Env,
    DisciplrVaultClient<'static>,
    Address,    // creator
    Address,    // verifier
    Address,    // success_dest
    Address,    // failure_dest
    BytesN<32>, // milestone_hash
) {
    let env = Env::default();
    env.mock_all_auths();

    let id = env.register(DisciplrVault, ());
    let client = DisciplrVaultClient::new(&env, &id);

    let creator = Address::generate(&env);
    let verifier = Address::generate(&env);
    let success = Address::generate(&env);
    let failure = Address::generate(&env);
    let hash = BytesN::from_array(&env, &[0u8; 32]);

    (env, client, creator, verifier, success, failure, hash)
}

/// Create a vault **with** a verifier.
fn create_verified_vault(
    client: &DisciplrVaultClient<'static>,
    creator: &Address,
    verifier: &Address,
    success: &Address,
    failure: &Address,
    hash: &BytesN<32>,
) -> u32 {
    client.create_vault(
        creator,
        &100_i128,
        &1_000_u64,
        &2_000_u64,
        hash,
        &Some(verifier.clone()),
        success,
        failure,
    )
}

/// Create a vault **without** a verifier (self-verified).
fn create_self_vault(
    client: &DisciplrVaultClient<'static>,
    creator: &Address,
    success: &Address,
    failure: &Address,
    hash: &BytesN<32>,
) -> u32 {
    client.create_vault(
        creator, &100_i128, &1_000_u64, &2_000_u64, hash, &None, success, failure,
    )
}

// ── create_vault ────────────────────────────────────────────────────────

#[test]
fn test_create_vault_emits_event_and_persists() {
    let (env, client, creator, verifier, success, failure, hash) = setup();
    let vault_id = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);
    assert_eq!(vault_id, 0);

    // Verify event immediately — before any other contract call that would
    // reset the invocation-metering event buffer.
    assert_eq!(
        env.events().all(),
        vec![
            &env,
            (
                client.address.clone(),
                (Symbol::new(&env, "vault_created"), 0u32).into_val(&env),
                VaultCreatedEvent {
                    vault_id: 0,
                    creator: creator.clone(),
                    amount: 100,
                    start_timestamp: 1_000,
                    end_timestamp: 2_000,
                    milestone_hash: hash.clone(),
                    verifier: Some(verifier.clone()),
                    success_destination: success.clone(),
                    failure_destination: failure.clone(),
                }
                .into_val(&env),
            ),
        ]
    );

    // Verify storage (separate call — happens after event check).
    let stored = client.get_vault_state(&vault_id).unwrap();
    assert_eq!(stored.status, VaultStatus::Active);
    assert_eq!(stored.amount, 100);
    assert_eq!(stored.creator, creator);
}

#[test]
fn test_vault_ids_increment() {
    let (_, client, creator, verifier, success, failure, hash) = setup();
    let id0 = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);
    let id1 = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);
    let id2 = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);

    assert_eq!(id0, 0);
    assert_eq!(id1, 1);
    assert_eq!(id2, 2);
}

#[test]
#[should_panic(expected = "amount must be positive")]
fn test_create_vault_zero_amount() {
    let (_, client, creator, _, success, failure, hash) = setup();
    client.create_vault(
        &creator, &0_i128, &1_000_u64, &2_000_u64, &hash, &None, &success, &failure,
    );
}

#[test]
#[should_panic(expected = "end_timestamp must be after start_timestamp")]
fn test_create_vault_invalid_timestamps() {
    let (_, client, creator, _, success, failure, hash) = setup();
    client.create_vault(
        &creator, &100_i128, &2_000_u64, &1_000_u64, &hash, &None, &success, &failure,
    );
}

// ── validate_milestone ──────────────────────────────────────────────────

#[test]
fn test_validate_milestone_emits_event() {
    let (env, client, creator, verifier, success, failure, hash) = setup();
    let vault_id = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);

    // Verify create event immediately after create_vault.
    assert_eq!(
        env.events().all(),
        vec![
            &env,
            (
                client.address.clone(),
                (Symbol::new(&env, "vault_created"), vault_id).into_val(&env),
                VaultCreatedEvent {
                    vault_id,
                    creator: creator.clone(),
                    amount: 100,
                    start_timestamp: 1_000,
                    end_timestamp: 2_000,
                    milestone_hash: hash.clone(),
                    verifier: Some(verifier.clone()),
                    success_destination: success.clone(),
                    failure_destination: failure.clone(),
                }
                .into_val(&env),
            ),
        ]
    );

    env.ledger().with_mut(|li| li.timestamp = 1_500);
    let ok = client.validate_milestone(&verifier, &vault_id);
    assert!(ok);

    // Verify validate event immediately after validate_milestone.
    assert_eq!(
        env.events().all(),
        vec![
            &env,
            (
                client.address.clone(),
                (Symbol::new(&env, "milestone_validated"), vault_id).into_val(&env),
                MilestoneValidatedEvent {
                    vault_id,
                    verifier: verifier.clone(),
                    destination: success.clone(),
                    amount: 100,
                    status: VaultStatus::Completed,
                }
                .into_val(&env),
            ),
        ]
    );

    // Verify state transitioned (storage check after event assertions).
    let stored = client.get_vault_state(&vault_id).unwrap();
    assert_eq!(stored.status, VaultStatus::Completed);
}

#[test]
#[should_panic(expected = "caller is not the designated verifier")]
fn test_validate_milestone_wrong_verifier() {
    let (env, client, creator, verifier, success, failure, hash) = setup();
    let vault_id = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);

    env.ledger().with_mut(|li| li.timestamp = 1_500);
    let impostor = Address::generate(&env);
    client.validate_milestone(&impostor, &vault_id);
}

#[test]
#[should_panic(expected = "past deadline")]
fn test_validate_milestone_past_deadline() {
    let (env, client, creator, verifier, success, failure, hash) = setup();
    let vault_id = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);

    env.ledger().with_mut(|li| li.timestamp = 3_000);
    client.validate_milestone(&verifier, &vault_id);
}

#[test]
#[should_panic(expected = "vault is not active")]
fn test_validate_milestone_already_completed() {
    let (env, client, creator, verifier, success, failure, hash) = setup();
    let vault_id = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);

    env.ledger().with_mut(|li| li.timestamp = 1_500);
    client.validate_milestone(&verifier, &vault_id);
    // Second call → vault already Completed
    client.validate_milestone(&verifier, &vault_id);
}

#[test]
#[should_panic(expected = "vault has no designated verifier")]
fn test_validate_milestone_no_verifier_set() {
    let (env, client, creator, verifier, success, failure, hash) = setup();
    let vault_id = create_self_vault(&client, &creator, &success, &failure, &hash);

    env.ledger().with_mut(|li| li.timestamp = 1_500);
    client.validate_milestone(&verifier, &vault_id);
}

// ── release_funds ───────────────────────────────────────────────────────

#[test]
fn test_release_funds_emits_event() {
    let (env, client, creator, _, success, failure, hash) = setup();
    let vault_id = create_self_vault(&client, &creator, &success, &failure, &hash);

    // Verify create event immediately after create_vault.
    assert_eq!(
        env.events().all(),
        vec![
            &env,
            (
                client.address.clone(),
                (Symbol::new(&env, "vault_created"), vault_id).into_val(&env),
                VaultCreatedEvent {
                    vault_id,
                    creator: creator.clone(),
                    amount: 100,
                    start_timestamp: 1_000,
                    end_timestamp: 2_000,
                    milestone_hash: hash.clone(),
                    verifier: None,
                    success_destination: success.clone(),
                    failure_destination: failure.clone(),
                }
                .into_val(&env),
            ),
        ]
    );

    let ok = client.release_funds(&creator, &vault_id);
    assert!(ok);

    // Verify release event immediately after release_funds.
    assert_eq!(
        env.events().all(),
        vec![
            &env,
            (
                client.address.clone(),
                (Symbol::new(&env, "funds_released"), vault_id).into_val(&env),
                FundsReleasedEvent {
                    vault_id,
                    destination: success.clone(),
                    amount: 100,
                    status: VaultStatus::Completed,
                }
                .into_val(&env),
            ),
        ]
    );

    // Verify state transitioned (storage check after event assertions).
    let stored = client.get_vault_state(&vault_id).unwrap();
    assert_eq!(stored.status, VaultStatus::Completed);
}

#[test]
#[should_panic(expected = "vault has a verifier; use validate_milestone")]
fn test_release_funds_with_verifier() {
    let (_, client, creator, verifier, success, failure, hash) = setup();
    let vault_id = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);
    client.release_funds(&creator, &vault_id);
}

#[test]
#[should_panic(expected = "caller is not the vault creator")]
fn test_release_funds_wrong_creator() {
    let (env, client, creator, _, success, failure, hash) = setup();
    let vault_id = create_self_vault(&client, &creator, &success, &failure, &hash);
    let stranger = Address::generate(&env);
    client.release_funds(&stranger, &vault_id);
}

// ── redirect_funds ──────────────────────────────────────────────────────

#[test]
fn test_redirect_funds_emits_event() {
    let (env, client, creator, verifier, success, failure, hash) = setup();
    let vault_id = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);

    // Verify create event immediately after create_vault.
    assert_eq!(
        env.events().all(),
        vec![
            &env,
            (
                client.address.clone(),
                (Symbol::new(&env, "vault_created"), vault_id).into_val(&env),
                VaultCreatedEvent {
                    vault_id,
                    creator: creator.clone(),
                    amount: 100,
                    start_timestamp: 1_000,
                    end_timestamp: 2_000,
                    milestone_hash: hash.clone(),
                    verifier: Some(verifier.clone()),
                    success_destination: success.clone(),
                    failure_destination: failure.clone(),
                }
                .into_val(&env),
            ),
        ]
    );

    env.ledger().with_mut(|li| li.timestamp = 3_000); // past deadline
    let ok = client.redirect_funds(&vault_id);
    assert!(ok);

    // Verify redirect event immediately after redirect_funds.
    assert_eq!(
        env.events().all(),
        vec![
            &env,
            (
                client.address.clone(),
                (Symbol::new(&env, "funds_redirected"), vault_id).into_val(&env),
                FundsRedirectedEvent {
                    vault_id,
                    destination: failure.clone(),
                    amount: 100,
                    status: VaultStatus::Failed,
                }
                .into_val(&env),
            ),
        ]
    );

    // Verify state transitioned (storage check after event assertions).
    let stored = client.get_vault_state(&vault_id).unwrap();
    assert_eq!(stored.status, VaultStatus::Failed);
}

#[test]
#[should_panic(expected = "deadline has not passed")]
fn test_redirect_funds_before_deadline() {
    let (env, client, creator, verifier, success, failure, hash) = setup();
    let vault_id = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);

    env.ledger().with_mut(|li| li.timestamp = 1_500);
    client.redirect_funds(&vault_id);
}

#[test]
#[should_panic(expected = "vault is not active")]
fn test_redirect_funds_already_failed() {
    let (env, client, creator, verifier, success, failure, hash) = setup();
    let vault_id = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);
    env.ledger().with_mut(|li| li.timestamp = 3_000);
    client.redirect_funds(&vault_id);
    // Second call → already Failed
    client.redirect_funds(&vault_id);
}

// ── cancel_vault ────────────────────────────────────────────────────────

#[test]
fn test_cancel_vault_emits_event() {
    let (env, client, creator, verifier, success, failure, hash) = setup();
    let vault_id = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);

    // Verify create event immediately after create_vault.
    assert_eq!(
        env.events().all(),
        vec![
            &env,
            (
                client.address.clone(),
                (Symbol::new(&env, "vault_created"), vault_id).into_val(&env),
                VaultCreatedEvent {
                    vault_id,
                    creator: creator.clone(),
                    amount: 100,
                    start_timestamp: 1_000,
                    end_timestamp: 2_000,
                    milestone_hash: hash.clone(),
                    verifier: Some(verifier.clone()),
                    success_destination: success.clone(),
                    failure_destination: failure.clone(),
                }
                .into_val(&env),
            ),
        ]
    );

    env.ledger().with_mut(|li| li.timestamp = 500); // before start
    let ok = client.cancel_vault(&creator, &vault_id);
    assert!(ok);

    // Verify cancel event immediately after cancel_vault.
    assert_eq!(
        env.events().all(),
        vec![
            &env,
            (
                client.address.clone(),
                (Symbol::new(&env, "vault_cancelled"), vault_id).into_val(&env),
                VaultCancelledEvent {
                    vault_id,
                    creator: creator.clone(),
                    amount: 100,
                    status: VaultStatus::Cancelled,
                }
                .into_val(&env),
            ),
        ]
    );

    // Verify state transitioned (storage check after event assertions).
    let stored = client.get_vault_state(&vault_id).unwrap();
    assert_eq!(stored.status, VaultStatus::Cancelled);
}

#[test]
#[should_panic(expected = "caller is not the vault creator")]
fn test_cancel_vault_wrong_creator() {
    let (env, client, creator, verifier, success, failure, hash) = setup();
    let vault_id = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);
    let stranger = Address::generate(&env);
    env.ledger().with_mut(|li| li.timestamp = 500);
    client.cancel_vault(&stranger, &vault_id);
}

#[test]
#[should_panic(expected = "cannot cancel after vault has started")]
fn test_cancel_vault_after_start() {
    let (env, client, creator, verifier, success, failure, hash) = setup();
    let vault_id = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);
    env.ledger().with_mut(|li| li.timestamp = 1_500);
    client.cancel_vault(&creator, &vault_id);
}

#[test]
#[should_panic(expected = "vault is not active")]
fn test_cancel_vault_already_cancelled() {
    let (env, client, creator, verifier, success, failure, hash) = setup();
    let vault_id = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);
    env.ledger().with_mut(|li| li.timestamp = 500);
    client.cancel_vault(&creator, &vault_id);
    client.cancel_vault(&creator, &vault_id);
}

// ── get_vault_state ─────────────────────────────────────────────────────

#[test]
fn test_get_vault_state_nonexistent() {
    let (_, client, ..) = setup();
    assert_eq!(client.get_vault_state(&999), None);
}

// ── cross-operation edge cases ──────────────────────────────────────────

#[test]
#[should_panic(expected = "vault is not active")]
fn test_cannot_redirect_after_completion() {
    let (env, client, creator, verifier, success, failure, hash) = setup();
    let vault_id = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);

    env.ledger().with_mut(|li| li.timestamp = 1_500);
    client.validate_milestone(&verifier, &vault_id);

    // Try redirect on Completed vault
    env.ledger().with_mut(|li| li.timestamp = 3_000);
    client.redirect_funds(&vault_id);
}

#[test]
#[should_panic(expected = "vault is not active")]
fn test_cannot_cancel_after_redirect() {
    let (env, client, creator, verifier, success, failure, hash) = setup();
    let vault_id = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);

    env.ledger().with_mut(|li| li.timestamp = 3_000);
    client.redirect_funds(&vault_id);
    client.cancel_vault(&creator, &vault_id);
}

#[test]
#[should_panic(expected = "vault not found")]
fn test_validate_nonexistent_vault() {
    let (env, client, _, verifier, ..) = setup();
    env.ledger().with_mut(|li| li.timestamp = 1_500);
    client.validate_milestone(&verifier, &42);
}

// ── storage persistence edge cases ──────────────────────────────────────

/// Verify that get_vault_state returns every field exactly as supplied to
/// create_vault — the full round-trip through persistent storage.
#[test]
fn test_get_vault_state_returns_all_fields() {
    let (_, client, creator, verifier, success, failure, hash) = setup();

    let vault_id = client.create_vault(
        &creator,
        &999_i128,
        &5_000_u64,
        &9_000_u64,
        &hash,
        &Some(verifier.clone()),
        &success,
        &failure,
    );

    let v = client.get_vault_state(&vault_id).unwrap();
    assert_eq!(v.creator, creator);
    assert_eq!(v.amount, 999);
    assert_eq!(v.start_timestamp, 5_000);
    assert_eq!(v.end_timestamp, 9_000);
    assert_eq!(v.milestone_hash, hash);
    assert_eq!(v.verifier, Some(verifier));
    assert_eq!(v.success_destination, success);
    assert_eq!(v.failure_destination, failure);
    assert_eq!(v.status, VaultStatus::Active);
}

/// Creating a second vault must not overwrite the first.
#[test]
fn test_create_vault_does_not_overwrite_existing() {
    let (_, client, creator, verifier, success, failure, hash) = setup();

    let id0 = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);
    let id1 = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);

    assert_ne!(id0, id1);

    // First vault still intact
    let v0 = client.get_vault_state(&id0).unwrap();
    assert_eq!(v0.status, VaultStatus::Active);
    assert_eq!(v0.amount, 100);

    // Second vault also present
    let v1 = client.get_vault_state(&id1).unwrap();
    assert_eq!(v1.status, VaultStatus::Active);
}

/// State transitions persist across subsequent contract calls.
#[test]
fn test_state_persists_across_calls() {
    let (env, client, creator, verifier, success, failure, hash) = setup();

    let id0 = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);
    let id1 = create_verified_vault(&client, &creator, &verifier, &success, &failure, &hash);

    // Validate milestone on vault 0
    env.ledger().with_mut(|li| li.timestamp = 1_500);
    client.validate_milestone(&verifier, &id0);

    // Redirect vault 1 after deadline
    env.ledger().with_mut(|li| li.timestamp = 3_000);
    client.redirect_funds(&id1);

    // Both vaults retain their independent states
    let v0 = client.get_vault_state(&id0).unwrap();
    let v1 = client.get_vault_state(&id1).unwrap();
    assert_eq!(v0.status, VaultStatus::Completed);
    assert_eq!(v1.status, VaultStatus::Failed);
}

/// release_funds panics with "vault not found" for a nonexistent vault.
#[test]
#[should_panic(expected = "vault not found")]
fn test_release_funds_nonexistent_vault() {
    let (_, client, creator, ..) = setup();
    client.release_funds(&creator, &999);
}

/// redirect_funds panics with "vault not found" for a nonexistent vault.
#[test]
#[should_panic(expected = "vault not found")]
fn test_redirect_funds_nonexistent_vault() {
    let (env, client, ..) = setup();
    env.ledger().with_mut(|li| li.timestamp = 9_999);
    client.redirect_funds(&999);
}

/// cancel_vault panics with "vault not found" for a nonexistent vault.
#[test]
#[should_panic(expected = "vault not found")]
fn test_cancel_vault_nonexistent_vault() {
    let (_, client, creator, ..) = setup();
    client.cancel_vault(&creator, &999);
}
