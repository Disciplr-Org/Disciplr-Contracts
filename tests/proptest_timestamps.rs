#![cfg(test)]

extern crate std;

use disciplr_vault::{
    DisciplrVault, DisciplrVaultClient, Error, MAX_AMOUNT, MAX_VAULT_DURATION, MIN_AMOUNT,
};
use proptest::prelude::*;
use soroban_sdk::{
    testutils::{Address as _, Ledger},
    token::StellarAssetClient,
    Address, BytesN, Env, Vec,
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

fn single_milestone(env: &Env, byte: u8) -> Vec<BytesN<32>> {
    let mut milestones = Vec::new(env);
    milestones.push_back(BytesN::from_array(env, &[byte; 32]));
    milestones
}

fn assert_contract_error<T: core::fmt::Debug>(
    result: Result<T, Result<Error, soroban_sdk::InvokeError>>,
    expected: Error,
) {
    match result {
        Err(Ok(actual)) => assert_eq!(actual, expected),
        other => panic!("unexpected result: {other:?}"),
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    #[test]
    fn prop_create_vault_accepts_valid_ordering(
        now in 0u64..20_000_000_000u64,
        start_offset in 0u64..1_000_000_000,
        duration in 1u64..=MAX_VAULT_DURATION,
        amount in MIN_AMOUNT..=MAX_AMOUNT,
    ) {
        let (env, client, usdc, usdc_asset) = setup();

        let creator = Address::generate(&env);
        let success = Address::generate(&env);
        let failure = Address::generate(&env);
        let milestone = single_milestone(&env, 0);

        env.ledger().set_timestamp(now);

        // Bounded to avoid u64 overflow: now <= 20_000_000_000, start_offset <= 1_000_000_000, duration <= MAX_VAULT_DURATION.
        let start = now + start_offset;
        let end = start + duration;

        usdc_asset.mint(&creator, &amount);

        let vault_id = client.create_vault(
            &usdc,
            &creator,
            &amount,
            &start,
            &end,
            &milestone,
            &None,
            &success,
            &failure,
        );

        let vault = client.get_vault_state(&vault_id).expect("vault should exist");
        prop_assert_eq!(vault.start_timestamp, start);
        prop_assert_eq!(vault.end_timestamp, end);
        prop_assert_eq!(vault.end_timestamp - vault.start_timestamp, duration);
        prop_assert_eq!(vault.amount, amount);
    }

    #[test]
    fn prop_create_vault_rejects_start_gte_end(
        now in 0u64..20_000_000_000u64,
        start_offset in 0u64..1_000_000,
        backoff in 0u64..1_000_000,
        amount in MIN_AMOUNT..=MAX_AMOUNT,
    ) {
        let (env, client, usdc, usdc_asset) = setup();

        let creator = Address::generate(&env);
        let success = Address::generate(&env);
        let failure = Address::generate(&env);

        env.ledger().set_timestamp(now);

        let start = now + start_offset;
        let end = start.saturating_sub(backoff);

        usdc_asset.mint(&creator, &amount);

        let result = client.try_create_vault(
            &usdc,
            &creator,
            &amount,
            &start,
            &end,
            &single_milestone(&env, 1),
            &None,
            &success,
            &failure,
        );

        assert_contract_error(result, Error::InvalidTimestamps);
    }

    #[test]
    fn prop_create_vault_rejects_duration_above_max(
        now in 0u64..20_000_000_000u64,
        start_offset in 0u64..10_000,
        extra in 1u64..10_000,
        amount in MIN_AMOUNT..=MAX_AMOUNT,
    ) {
        let (env, client, usdc, usdc_asset) = setup();

        let creator = Address::generate(&env);
        let success = Address::generate(&env);
        let failure = Address::generate(&env);

        env.ledger().set_timestamp(now);

        let start = now + start_offset;
        let end = start + MAX_VAULT_DURATION + extra;

        usdc_asset.mint(&creator, &amount);

        let result = client.try_create_vault(
            &usdc,
            &creator,
            &amount,
            &start,
            &end,
            &single_milestone(&env, 2),
            &None,
            &success,
            &failure,
        );

        assert_contract_error(result, Error::DurationTooLong);
    }

    #[test]
    fn prop_duration_boundary(
        now in 0u64..20_000_000_000u64,
        start_offset in 0u64..1_000_000,
        amount in MIN_AMOUNT..=MAX_AMOUNT,
    ) {
        let (env, client, usdc, usdc_asset) = setup();

        let creator = Address::generate(&env);
        let success = Address::generate(&env);
        let failure = Address::generate(&env);
        let milestone = single_milestone(&env, 3);

        env.ledger().set_timestamp(now);

        let start = now + start_offset;

        // 1. Assert duration == MAX_VAULT_DURATION accepts
        {
            let end_valid = start + MAX_VAULT_DURATION;
            usdc_asset.mint(&creator, &amount);
            let vault_id = client.create_vault(
                &usdc,
                &creator,
                &amount,
                &start,
                &end_valid,
                &milestone,
                &None,
                &success,
                &failure,
            );
            let vault = client.get_vault_state(&vault_id).expect("vault should exist");
            prop_assert_eq!(vault.start_timestamp, start);
            prop_assert_eq!(vault.end_timestamp, end_valid);
            prop_assert_eq!(vault.end_timestamp - vault.start_timestamp, MAX_VAULT_DURATION);
        }

        // 2. Assert duration == MAX_VAULT_DURATION + 1 rejects with DurationTooLong
        {
            let end_invalid = start + MAX_VAULT_DURATION + 1;
            usdc_asset.mint(&creator, &amount);
            let result = client.try_create_vault(
                &usdc,
                &creator,
                &amount,
                &start,
                &end_invalid,
                &milestone,
                &None,
                &success,
                &failure,
            );
            assert_contract_error(result, Error::DurationTooLong);
        }
    }

    #[test]
    fn prop_past_start_rejected(
        now in 1_000_000u64..20_000_000_000u64,
        past_offset in 1u64..1_000_000,
        duration in 1u64..=MAX_VAULT_DURATION,
        amount in MIN_AMOUNT..=MAX_AMOUNT,
    ) {
        let (env, client, usdc, usdc_asset) = setup();

        let creator = Address::generate(&env);
        let success = Address::generate(&env);
        let failure = Address::generate(&env);
        let milestone = single_milestone(&env, 4);

        env.ledger().set_timestamp(now);

        let start = now - past_offset;
        let end = start + duration;

        usdc_asset.mint(&creator, &amount);

        let result = client.try_create_vault(
            &usdc,
            &creator,
            &amount,
            &start,
            &end,
            &milestone,
            &None,
            &success,
            &failure,
        );

        assert_contract_error(result, Error::InvalidTimestamp);
    }
}

#[test]
fn edge_start_eq_now_succeeds() {
    let (env, client, usdc, usdc_asset) = setup();
    let creator = Address::generate(&env);
    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);

    usdc_asset.mint(&creator, &MIN_AMOUNT);

    let start = now;
    let end = start + 1;

    let id = client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &start,
        &end,
        &single_milestone(&env, 6),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );

    let vault = client.get_vault_state(&id).unwrap();
    assert_eq!(vault.start_timestamp, start);
    assert_eq!(vault.end_timestamp, end);
}

#[test]
fn edge_start_eq_end_rejected() {
    let (env, client, usdc, usdc_asset) = setup();
    let creator = Address::generate(&env);
    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);

    usdc_asset.mint(&creator, &MIN_AMOUNT);

    let result = client.try_create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &now,
        &now,
        &single_milestone(&env, 3),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );

    assert_contract_error(result, Error::InvalidTimestamps);
}

#[test]
fn edge_zero_start_with_current_zero_succeeds() {
    let (env, client, usdc, usdc_asset) = setup();
    let creator = Address::generate(&env);
    env.ledger().set_timestamp(0);

    usdc_asset.mint(&creator, &MIN_AMOUNT);

    let id = client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &0,
        &1,
        &single_milestone(&env, 4),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );

    let vault = client.get_vault_state(&id).unwrap();
    assert_eq!(vault.start_timestamp, 0);
    assert_eq!(vault.end_timestamp, 1);
}

#[test]
fn edge_max_duration_boundary_succeeds() {
    let (env, client, usdc, usdc_asset) = setup();
    let creator = Address::generate(&env);
    let now = 100u64;
    env.ledger().set_timestamp(now);

    usdc_asset.mint(&creator, &MIN_AMOUNT);

    let start = now;
    let end = start + MAX_VAULT_DURATION;

    let id = client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &start,
        &end,
        &single_milestone(&env, 5),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );

    let vault = client.get_vault_state(&id).unwrap();
    assert_eq!(
        vault.end_timestamp - vault.start_timestamp,
        MAX_VAULT_DURATION
    );
}
