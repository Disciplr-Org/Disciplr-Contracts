#![cfg(test)]

use soroban_sdk::{
    testutils::{Address as _, Ledger},
    token::{StellarAssetClient, TokenClient},
    Address, BytesN, Env,
};

use disciplr_vault::{DisciplrVault, DisciplrVaultClient, Error, VaultStatus, MIN_AMOUNT};

fn setup() -> (
    Env,
    DisciplrVaultClient<'static>,
    Address,
    StellarAssetClient<'static>,
    TokenClient<'static>,
) {
    let env = Env::default();
    env.mock_all_auths();

    let contract_id = env.register(DisciplrVault, ());
    let client = DisciplrVaultClient::new(&env, &contract_id);

    let usdc_admin = Address::generate(&env);
    let usdc_token = env.register_stellar_asset_contract_v2(usdc_admin.clone());
    let usdc_addr = usdc_token.address();
    let usdc_asset = StellarAssetClient::new(&env, &usdc_addr);
    let usdc_token_client = TokenClient::new(&env, &usdc_addr);

    (env, client, usdc_addr, usdc_asset, usdc_token_client)
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

#[test]
fn test_full_lifecycle_success() {
    let (env, client, usdc, usdc_asset, usdc_token) = setup();

    let creator = Address::generate(&env);
    let verifier = Address::generate(&env);
    let success_dest = Address::generate(&env);
    let failure_dest = Address::generate(&env);
    let now = 1_700_000_000u64;
    env.ledger().set_timestamp(now);

    usdc_asset.mint(&creator, &MIN_AMOUNT);

    let milestone = BytesN::from_array(&env, &[1u8; 32]);

    // 1. Create Vault
    let vault_id = client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &milestone,
        &Some(verifier.clone()),
        &success_dest,
        &failure_dest,
    );

    assert_eq!(
        client.get_vault_state(&vault_id).unwrap().status,
        VaultStatus::Active
    );

    // 2. Validate Milestone
    env.ledger().set_timestamp(now + 3_600);
    client.validate_milestone(&vault_id);
    assert!(
        client
            .get_vault_state(&vault_id)
            .unwrap()
            .milestone_validated
    );

    // 3. Release Funds
    client.release_funds(&vault_id, &usdc);
    let final_state = client.get_vault_state(&vault_id).unwrap();
    assert_eq!(final_state.status, VaultStatus::Completed);
    assert_eq!(usdc_token.balance(&success_dest), MIN_AMOUNT);
}

#[test]
fn test_full_lifecycle_failure_redirection() {
    let (env, client, usdc, usdc_asset, usdc_token) = setup();

    let creator = Address::generate(&env);
    let success_dest = Address::generate(&env);
    let failure_dest = Address::generate(&env);
    let now = 1_700_000_000u64;
    env.ledger().set_timestamp(now);

    usdc_asset.mint(&creator, &MIN_AMOUNT);

    let milestone = BytesN::from_array(&env, &[1u8; 32]);

    // 1. Create Vault
    let vault_id = client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &milestone,
        &None,
        &success_dest,
        &failure_dest,
    );

    // 2. Wait until deadline passes without validation
    env.ledger().set_timestamp(now + 86_401);

    // 3. Redirect Funds
    client.redirect_funds(&vault_id, &usdc);
    let final_state = client.get_vault_state(&vault_id).unwrap();
    assert_eq!(final_state.status, VaultStatus::Failed);
    assert_eq!(usdc_token.balance(&failure_dest), MIN_AMOUNT);
}

#[test]
fn test_cancel_vault_refunds_creator_and_empties_contract_escrow() {
    let (env, client, usdc, usdc_asset, usdc_token) = setup();

    let creator = Address::generate(&env);
    let success_dest = Address::generate(&env);
    let failure_dest = Address::generate(&env);
    let now = 1_700_000_000u64;
    env.ledger().set_timestamp(now);

    usdc_asset.mint(&creator, &MIN_AMOUNT);
    let creator_before_create = usdc_token.balance(&creator);
    let contract_before_create = usdc_token.balance(&client.address);

    let vault_id = client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[2u8; 32]),
        &None,
        &success_dest,
        &failure_dest,
    );

    assert_eq!(
        usdc_token.balance(&creator),
        creator_before_create - MIN_AMOUNT
    );
    assert_eq!(
        usdc_token.balance(&client.address),
        contract_before_create + MIN_AMOUNT
    );

    let creator_before_cancel = usdc_token.balance(&creator);
    let contract_before_cancel = usdc_token.balance(&client.address);

    let result = client.cancel_vault(&vault_id, &usdc);

    assert!(result);
    assert_eq!(
        usdc_token.balance(&creator),
        creator_before_cancel + MIN_AMOUNT
    );
    assert_eq!(
        usdc_token.balance(&client.address),
        contract_before_cancel - MIN_AMOUNT
    );
    assert_eq!(usdc_token.balance(&client.address), contract_before_create);
    assert_eq!(usdc_token.balance(&success_dest), 0);
    assert_eq!(usdc_token.balance(&failure_dest), 0);

    let final_state = client.get_vault_state(&vault_id).unwrap();
    assert_eq!(final_state.status, VaultStatus::Cancelled);
}

#[test]
fn test_cancel_vault_rejects_completed_failed_and_cancelled_vaults() {
    let (env, client, usdc, usdc_asset, _) = setup();
    let now = 1_700_000_000u64;
    env.ledger().set_timestamp(now);

    let completed_creator = Address::generate(&env);
    let failed_creator = Address::generate(&env);
    let cancelled_creator = Address::generate(&env);
    usdc_asset.mint(&completed_creator, &MIN_AMOUNT);
    usdc_asset.mint(&failed_creator, &MIN_AMOUNT);
    usdc_asset.mint(&cancelled_creator, &MIN_AMOUNT);

    let completed_id = client.create_vault(
        &usdc,
        &completed_creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[3u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );
    client.validate_milestone(&completed_id);
    client.release_funds(&completed_id, &usdc);
    assert_contract_error(
        client.try_cancel_vault(&completed_id, &usdc),
        Error::VaultNotActive,
    );

    let failed_id = client.create_vault(
        &usdc,
        &failed_creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[4u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );
    env.ledger().set_timestamp(now + 86_401);
    client.redirect_funds(&failed_id, &usdc);
    assert_contract_error(
        client.try_cancel_vault(&failed_id, &usdc),
        Error::VaultNotActive,
    );

    env.ledger().set_timestamp(now);
    let cancelled_id = client.create_vault(
        &usdc,
        &cancelled_creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[5u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );
    client.cancel_vault(&cancelled_id, &usdc);
    assert_contract_error(
        client.try_cancel_vault(&cancelled_id, &usdc),
        Error::VaultNotActive,
    );
}
