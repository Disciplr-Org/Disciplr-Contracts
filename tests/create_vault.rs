#![cfg(test)]

extern crate std;

use soroban_sdk::{
    testutils::{Address as _, Ledger},
    Address, BytesN, Env,
};

use disciplr_vault::{
    DisciplrVault,
    DisciplrVaultClient,
    MIN_AMOUNT,
    MAX_AMOUNT,
    MAX_VAULT_DURATION,
};

fn setup() -> (Env, DisciplrVaultClient<'static>) {
    let env = Env::default();
    env.mock_all_auths();

    let contract_id = env.register(DisciplrVault, ());
    let client = DisciplrVaultClient::new(&env, &contract_id);

    (env, client)
}

#[test]
fn test_create_vault_valid_boundary_values() {
    let (env, client) = setup();

    let creator = Address::generate(&env);
    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);

    let success = Address::generate(&env);
    let failure = Address::generate(&env);
    let milestone = BytesN::from_array(&env, &[0u8; 32]);

    let vault_id = client.create_vault(
        &creator,
        &MIN_AMOUNT,
        &now,
        &(now + MAX_VAULT_DURATION),
        &milestone,
        &None,
        &success,
        &failure,
    );

    assert_eq!(vault_id, 0u32);
}

#[test]
#[should_panic(expected = "Amount below minimum allowed")]
fn test_amount_below_minimum() {
    let (env, client) = setup();

    let creator = Address::generate(&env);
    let now = env.ledger().timestamp();

    client.create_vault(
        &creator,
        &(MIN_AMOUNT - 1),
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[0u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );
}

#[test]
#[should_panic(expected = "Amount exceeds maximum allowed")]
fn test_amount_above_maximum() {
    let (env, client) = setup();

    let creator = Address::generate(&env);
    let now = env.ledger().timestamp();

    client.create_vault(
        &creator,
        &(MAX_AMOUNT + 1),
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[0u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );
}

#[test]
#[should_panic(expected = "Vault duration exceeds maximum allowed")]
fn test_duration_exceeds_max() {
    let (env, client) = setup();

    let creator = Address::generate(&env);
    let now = env.ledger().timestamp();

    client.create_vault(
        &creator,
        &MIN_AMOUNT,
        &now,
        &(now + MAX_VAULT_DURATION + 1),
        &BytesN::from_array(&env, &[0u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );
}

#[test]
#[should_panic(expected = "Start cannot be in the past")]
fn test_start_timestamp_in_past() {
    let (env, client) = setup();

    let creator = Address::generate(&env);
    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);

    client.create_vault(
        &creator,
        &MIN_AMOUNT,
        &(now - 3_600),
        &(now + 86_400),
        &BytesN::from_array(&env, &[0u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );
}

#[test]
#[should_panic(expected = "End timestamp must be after start timestamp")]
fn test_end_before_or_equal_start() {
    let (env, client) = setup();

    let creator = Address::generate(&env);
    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);

    client.create_vault(
        &creator,
        &MIN_AMOUNT,
        &(now + 200),
        &(now + 100),
        &BytesN::from_array(&env, &[0u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );
}

#[test]
fn test_amount_exactly_max_allowed() {
    let (env, client) = setup();

    let creator = Address::generate(&env);
    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);

    let vault_id = client.create_vault(
        &creator,
        &MAX_AMOUNT,
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[0u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );

    assert_eq!(vault_id, 0u32);
}

#[test]
#[should_panic(expected = "Amount below minimum allowed")]
fn test_amount_zero() {
    let (env, client) = setup();

    let creator = Address::generate(&env);
    let now = env.ledger().timestamp();

    client.create_vault(
        &creator,
        &0_i128,
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[0u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );
}

#[test]
fn test_minimum_valid_duration() {
    let (env, client) = setup();

    let creator = Address::generate(&env);
    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);

    let vault_id = client.create_vault(
        &creator,
        &MIN_AMOUNT,
        &now,
        &(now + 1),
        &BytesN::from_array(&env, &[0u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );

    assert_eq!(vault_id, 0u32);
}

#[test]
fn test_valid_zero_verifier_and_normal_duration() {
    let (env, client) = setup();

    let creator = Address::generate(&env);
    let now = env.ledger().timestamp();

    client.create_vault(
        &creator,
        &5_000_000_000_i128,
        &now,
        &(now + 7 * 24 * 60 * 60),
        &BytesN::from_array(&env, &[1u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );
}