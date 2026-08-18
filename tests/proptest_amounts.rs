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
    let (env, client, usdc, usdc_asset) = setup();
    let creator = Address::generate(&env);
    env.ledger().set_timestamp(1_725_000_000u64);

    usdc_asset.mint(&creator, &MIN_AMOUNT);

    let id = client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &1_725_000_000u64,
        &(1_725_000_000u64 + 86_400),
        &BytesN::from_array(&env, &[9u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );

    let vault = client.get_vault_state(&id).unwrap();
    assert_eq!(vault.amount, MIN_AMOUNT);
}

#[test]
fn edge_amount_max_succeeds() {
    let (env, client, usdc, usdc_asset) = setup();
    let creator = Address::generate(&env);
    env.ledger().set_timestamp(1_725_000_000u64);

    usdc_asset.mint(&creator, &MAX_AMOUNT);

    let id = client.create_vault(
        &usdc,
        &creator,
        &MAX_AMOUNT,
        &1_725_000_000u64,
        &(1_725_000_000u64 + 86_400),
        &BytesN::from_array(&env, &[10u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );

    let vault = client.get_vault_state(&id).unwrap();
    assert_eq!(vault.amount, MAX_AMOUNT);
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

// ---------------------------------------------------------------------------
// Boundary coverage for MIN_AMOUNT and MAX_AMOUNT
// ---------------------------------------------------------------------------
//
// The tests above assert `result.is_err()`, which cannot tell apart the two
// very different reasons `create_vault` can fail:
//
//   * the amount is outside [MIN_AMOUNT, MAX_AMOUNT], a contract rule that
//     returns `Error::InvalidAmount` before any token movement, and
//   * the creator does not hold the funds, which aborts inside the token
//     contract and never reaches a typed contract error.
//
// A regression that widened the bounds would keep every `is_err()` assertion
// green as long as the test happened to be underfunded. Everything below mints
// generously on purpose, so the only remaining reason to fail is the bound
// itself, and asserts the exact `Error::InvalidAmount`.

/// Funds the creator well past anything the test asks for, so a rejection can
/// only come from the amount check.
fn setup_funded(amount_hint: i128) -> (Env, DisciplrVaultClient<'static>, Address, Address) {
    let (env, client, usdc, usdc_asset) = setup();
    let creator = Address::generate(&env);

    // Never try to mint an absurd figure: the bound check runs before the
    // transfer, so MAX_AMOUNT of headroom is always enough to prove the point.
    let to_mint = if amount_hint > MAX_AMOUNT || amount_hint <= 0 {
        MAX_AMOUNT
    } else {
        amount_hint
    };
    usdc_asset.mint(&creator, &to_mint);

    (env, client, usdc, creator)
}

/// Attempts a vault with `amount` against a well funded creator and returns the
/// raw result, so each caller asserts the precise outcome it expects.
fn try_with_amount(
    env: &Env,
    client: &DisciplrVaultClient<'static>,
    usdc: &Address,
    creator: &Address,
    amount: i128,
) -> Result<Result<u32, soroban_sdk::ConversionError>, Result<Error, soroban_sdk::InvokeError>> {
    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);

    client.try_create_vault(
        usdc,
        creator,
        &amount,
        &now,
        &(now + 86_400),
        &BytesN::from_array(env, &[12u8; 32]),
        &None,
        &Address::generate(env),
        &Address::generate(env),
    )
}

/// Asserts the call was rejected specifically by the amount rule.
fn assert_invalid_amount(amount: i128) {
    let (env, client, usdc, creator) = setup_funded(amount);
    let result = try_with_amount(&env, &client, &usdc, &creator, amount);

    assert_eq!(
        result,
        Err(Ok(Error::InvalidAmount)),
        "amount {amount} tiene que rechazarse con InvalidAmount, no con otro error"
    );
}

/// Asserts the call was accepted and stored the amount verbatim.
fn assert_accepted(amount: i128) {
    let (env, client, usdc, creator) = setup_funded(amount);
    let result = try_with_amount(&env, &client, &usdc, &creator, amount);

    let id = result
        .unwrap_or_else(|e| panic!("amount {amount} deberia aceptarse, dio {e:?}"))
        .unwrap();

    assert_eq!(client.get_vault_state(&id).unwrap().amount, amount);
}

// ---- exact boundaries ----

#[test]
fn boundary_min_amount_is_accepted() {
    assert_accepted(MIN_AMOUNT);
}

#[test]
fn boundary_max_amount_is_accepted() {
    assert_accepted(MAX_AMOUNT);
}

#[test]
fn boundary_just_inside_minimum_is_accepted() {
    assert_accepted(MIN_AMOUNT + 1);
}

#[test]
fn boundary_just_inside_maximum_is_accepted() {
    assert_accepted(MAX_AMOUNT - 1);
}

// ---- neighbours just outside ----

#[test]
fn boundary_one_below_minimum_is_invalid_amount() {
    assert_invalid_amount(MIN_AMOUNT - 1);
}

#[test]
fn boundary_one_above_maximum_is_invalid_amount() {
    assert_invalid_amount(MAX_AMOUNT + 1);
}

// ---- zero and negatives ----

#[test]
fn zero_amount_is_invalid_amount() {
    assert_invalid_amount(0);
}

#[test]
fn negative_amount_is_invalid_amount() {
    assert_invalid_amount(-1);
}

#[test]
fn large_negative_amount_is_invalid_amount() {
    assert_invalid_amount(-MAX_AMOUNT);
}

#[test]
fn extreme_amounts_are_invalid_amount() {
    assert_invalid_amount(i128::MIN);
    assert_invalid_amount(i128::MAX);
}

// ---- the distinction the suite was missing ----

/// An in-range amount with an underfunded creator must fail for a different
/// reason than an out-of-range amount with a funded one. If both produced the
/// same error, the boundary assertions above would prove nothing.
#[test]
fn out_of_range_and_underfunded_fail_differently() {
    // Out of range, plenty of funds: typed contract error, no transfer attempted.
    let (env, client, usdc, creator) = setup_funded(MAX_AMOUNT + 1);
    let out_of_range = try_with_amount(&env, &client, &usdc, &creator, MAX_AMOUNT + 1);
    assert_eq!(out_of_range, Err(Ok(Error::InvalidAmount)));

    // In range, no funds: the failure comes from the token transfer, so it is
    // not InvalidAmount.
    let (env2, client2, usdc2, usdc_asset2) = setup();
    let broke = Address::generate(&env2);
    usdc_asset2.mint(&broke, &(MIN_AMOUNT - 1));
    let underfunded = try_with_amount(&env2, &client2, &usdc2, &broke, MIN_AMOUNT);

    assert!(
        underfunded.is_err(),
        "sin saldo la creacion tiene que fallar"
    );
    assert_ne!(
        underfunded,
        Err(Ok(Error::InvalidAmount)),
        "un fallo por saldo no puede confundirse con un fallo por monto: si esto \
         se rompe, las aserciones de borde dejan de probar nada"
    );
}

// ---- randomized sampling around the boundaries ----

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// Everything strictly below MIN_AMOUNT is rejected by the amount rule,
    /// including zero and negatives, with the creator holding funds.
    #[test]
    fn prop_below_minimum_is_invalid_amount(amount in (MIN_AMOUNT - 100_000)..MIN_AMOUNT) {
        let (env, client, usdc, creator) = setup_funded(MAX_AMOUNT);
        let result = try_with_amount(&env, &client, &usdc, &creator, amount);
        prop_assert_eq!(result, Err(Ok(Error::InvalidAmount)));
    }

    /// Everything strictly above MAX_AMOUNT is rejected by the amount rule.
    #[test]
    fn prop_above_maximum_is_invalid_amount(
        amount in (MAX_AMOUNT + 1)..=(MAX_AMOUNT + 1_000_000)
    ) {
        let (env, client, usdc, creator) = setup_funded(MAX_AMOUNT);
        let result = try_with_amount(&env, &client, &usdc, &creator, amount);
        prop_assert_eq!(result, Err(Ok(Error::InvalidAmount)));
    }

    /// Negative amounts of any magnitude are rejected the same way.
    #[test]
    fn prop_negative_is_invalid_amount(amount in i128::MIN..0i128) {
        let (env, client, usdc, creator) = setup_funded(MAX_AMOUNT);
        let result = try_with_amount(&env, &client, &usdc, &creator, amount);
        prop_assert_eq!(result, Err(Ok(Error::InvalidAmount)));
    }

    /// The interior of the valid interval is accepted and stored verbatim, with
    /// the creator funded to the exact figure.
    #[test]
    fn prop_interior_is_accepted_and_stored(amount in MIN_AMOUNT..=MAX_AMOUNT) {
        let (env, client, usdc, usdc_asset) = setup();
        let creator = Address::generate(&env);
        usdc_asset.mint(&creator, &amount);

        let result = try_with_amount(&env, &client, &usdc, &creator, amount);
        let id = result.unwrap().unwrap();
        prop_assert_eq!(client.get_vault_state(&id).unwrap().amount, amount);
    }
}
