#![cfg(test)]

extern crate std;

use disciplr_vault::{
    DisciplrVault, DisciplrVaultClient, Error, MAX_AMOUNT, MAX_VAULT_DURATION, MIN_AMOUNT,
};
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
        grace_period in 0u64..=MAX_VAULT_DURATION,
        amount in MIN_AMOUNT..=MAX_AMOUNT,
    ) {
        let (env, client, usdc, usdc_asset) = setup();

        let creator = Address::generate(&env);
        let success = Address::generate(&env);
        let failure = Address::generate(&env);
        let milestone = BytesN::from_array(&env, &[0u8; 32]);

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
            &grace_period,
            &success,
            &failure,
        );

        let vault = client.get_vault_state(&vault_id).expect("vault should exist");
        prop_assert_eq!(vault.start_timestamp, start);
        prop_assert_eq!(vault.end_timestamp, end);
        prop_assert_eq!(vault.end_timestamp - vault.start_timestamp, duration);
        prop_assert_eq!(vault.grace_period, grace_period);
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
            &BytesN::from_array(&env, &[1u8; 32]),
            &None,
            &0,
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
            &BytesN::from_array(&env, &[2u8; 32]),
            &None,
            &0,
            &success,
            &failure,
        );

        assert_contract_error(result, Error::DurationTooLong);
    }

    #[test]
    fn prop_create_vault_rejects_grace_above_max(
        now in 0u64..20_000_000_000u64,
        start_offset in 0u64..10_000,
        duration in 1u64..=MAX_VAULT_DURATION,
        extra_grace in 1u64..10_000,
        amount in MIN_AMOUNT..=MAX_AMOUNT,
    ) {
        let (env, client, usdc, usdc_asset) = setup();

        let creator = Address::generate(&env);
        let success = Address::generate(&env);
        let failure = Address::generate(&env);

        env.ledger().set_timestamp(now);

        let start = now + start_offset;
        let end = start + duration;
        let grace_period = MAX_VAULT_DURATION + extra_grace;

        usdc_asset.mint(&creator, &amount);

        let result = client.try_create_vault(
            &usdc,
            &creator,
            &amount,
            &start,
            &end,
            &BytesN::from_array(&env, &[7u8; 32]),
            &None,
            &grace_period,
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
        let milestone = BytesN::from_array(&env, &[3u8; 32]);

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
                &0,
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
                &0,
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
        let milestone = BytesN::from_array(&env, &[4u8; 32]);

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
            &0,
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
        &BytesN::from_array(&env, &[6u8; 32]),
        &None,
        &0,
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
        &BytesN::from_array(&env, &[3u8; 32]),
        &None,
        &0,
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
        &BytesN::from_array(&env, &[4u8; 32]),
        &None,
        &0,
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
        &BytesN::from_array(&env, &[5u8; 32]),
        &None,
        &0,
        &Address::generate(&env),
        &Address::generate(&env),
    );

    let vault = client.get_vault_state(&id).unwrap();
    assert_eq!(
        vault.end_timestamp - vault.start_timestamp,
        MAX_VAULT_DURATION
    );
}
