#![cfg(test)]

extern crate std;

use disciplr_vault::{DisciplrVault, DisciplrVaultClient, Error, MAX_AMOUNT, MIN_AMOUNT};
use proptest::prelude::*;
use soroban_sdk::{
    testutils::{Address as _, Ledger},
    token::StellarAssetClient,
    Address, BytesN, Env,
};

fn setup() -> (
    Env,
    DisciplrVaultClient<'static>,
    Address,
    StellarAssetClient<'static>,
) {
    let env = Env::default();
    env.mock_all_auths();

    let contract_id = env.register(DisciplrVault, ());
    let client = DisciplrVaultClient::new(&env, &contract_id);

    let usdc_admin = Address::generate(&env);
    let usdc_token = env.register_stellar_asset_contract_v2(usdc_admin.clone());
    let usdc_addr = usdc_token.address();
    let usdc_asset = StellarAssetClient::new(&env, &usdc_addr);

    (env, client, usdc_addr, usdc_asset)
}

fn assert_create_vault_invalid_amount(amount: i128, minted_amount: i128, hash_byte: u8) {
    let (env, client, usdc, usdc_asset) = setup();

    let creator = Address::generate(&env);
    let success = Address::generate(&env);
    let failure = Address::generate(&env);

    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);

    if minted_amount > 0 {
        usdc_asset.mint(&creator, &minted_amount);
    }

    let result = client.try_create_vault(
        &usdc,
        &creator,
        &amount,
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[hash_byte; 32]),
        &None,
        &success,
        &failure,
    );

    match result {
        Err(Ok(Error::InvalidAmount)) => {}
        other => panic!("expected InvalidAmount for amount {amount}, got {other:?}"),
    }
}

fn assert_create_vault_accepts_amount(amount: i128, hash_byte: u8) {
    let (env, client, usdc, usdc_asset) = setup();

    let creator = Address::generate(&env);
    let success = Address::generate(&env);
    let failure = Address::generate(&env);

    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);

    usdc_asset.mint(&creator, &amount);

    let id = client.create_vault(
        &usdc,
        &creator,
        &amount,
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[hash_byte; 32]),
        &None,
        &success,
        &failure,
    );

    let vault = client.get_vault_state(&id).unwrap();
    assert_eq!(vault.amount, amount);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    #[test]
    fn prop_amount_in_range_with_funding_succeeds(amount in MIN_AMOUNT..=MAX_AMOUNT) {
        let (env, client, usdc, usdc_asset) = setup();

        let creator = Address::generate(&env);
        let success = Address::generate(&env);
        let failure = Address::generate(&env);

        let now = 1_725_000_000u64;
        env.ledger().set_timestamp(now);

        usdc_asset.mint(&creator, &amount);

        let id = client.create_vault(
            &usdc,
            &creator,
            &amount,
            &now,
            &(now + 86_400),
            &BytesN::from_array(&env, &[7u8; 32]),
            &None,
            &success,
            &failure,
        );

        let vault = client.get_vault_state(&id).unwrap();
        prop_assert_eq!(vault.amount, amount);
    }

    #[test]
    fn prop_amount_in_range_underfunded_returns_error(amount in MIN_AMOUNT..=MAX_AMOUNT) {
        let (env, client, usdc, usdc_asset) = setup();

        let creator = Address::generate(&env);
        let success = Address::generate(&env);
        let failure = Address::generate(&env);

        let now = 1_725_000_000u64;
        env.ledger().set_timestamp(now);

        let minted = if amount > MIN_AMOUNT { amount - 1 } else { 0 };
        usdc_asset.mint(&creator, &minted);

        let result = client.try_create_vault(
            &usdc,
            &creator,
            &amount,
            &now,
            &(now + 86_400),
            &BytesN::from_array(&env, &[8u8; 32]),
            &None,
            &success,
            &failure,
        );

        prop_assert!(result.is_err());
    }
}

#[test]
fn edge_amount_min_succeeds() {
    assert_create_vault_accepts_amount(MIN_AMOUNT, 9);
}

#[test]
fn edge_amount_max_succeeds() {
    assert_create_vault_accepts_amount(MAX_AMOUNT, 10);
}

#[test]
fn edge_amount_just_inside_bounds_succeed() {
    assert_create_vault_accepts_amount(MIN_AMOUNT + 1, 11);
    assert_create_vault_accepts_amount(MAX_AMOUNT - 1, 12);
}

#[test]
fn edge_amount_just_outside_bounds_return_invalid_amount() {
    assert_create_vault_invalid_amount(MIN_AMOUNT - 1, MIN_AMOUNT, 13);
    assert_create_vault_invalid_amount(MAX_AMOUNT + 1, MAX_AMOUNT + 1, 14);
}

#[test]
fn edge_amount_zero_and_negative_return_invalid_amount() {
    assert_create_vault_invalid_amount(0, MIN_AMOUNT, 15);
    assert_create_vault_invalid_amount(-1, MIN_AMOUNT, 16);
}

#[test]
fn edge_amount_max_underfunded_errors() {
    let (env, client, usdc, usdc_asset) = setup();
    let creator = Address::generate(&env);
    env.ledger().set_timestamp(1_725_000_000u64);

    usdc_asset.mint(&creator, &(MAX_AMOUNT - 1));

    let result = client.try_create_vault(
        &usdc,
        &creator,
        &MAX_AMOUNT,
        &1_725_000_000u64,
        &(1_725_000_000u64 + 86_400),
        &BytesN::from_array(&env, &[11u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );

    assert!(result.is_err());
}
