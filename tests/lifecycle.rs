#![cfg(test)]

use soroban_sdk::{
    testutils::{Address as _, Ledger},
    token::{StellarAssetClient, TokenClient},
    Address, BytesN, Env,
};

use disciplr_vault::{
    DisciplrVault, DisciplrVaultClient, Error, VaultStatus, MAX_VAULT_DURATION, MIN_AMOUNT,
};

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
        &0,
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
        &0,
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
fn test_redirect_respects_creator_grace_period() {
    let (env, client, usdc, usdc_asset, usdc_token) = setup();

    let creator = Address::generate(&env);
    let success_dest = Address::generate(&env);
    let failure_dest = Address::generate(&env);
    let now = 1_700_000_000u64;
    let grace_period = 3_600u64;
    env.ledger().set_timestamp(now);

    usdc_asset.mint(&creator, &MIN_AMOUNT);
    let milestone = BytesN::from_array(&env, &[2u8; 32]);

    let vault_id = client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &milestone,
        &None,
        &grace_period,
        &success_dest,
        &failure_dest,
    );

    let vault = client.get_vault_state(&vault_id).unwrap();
    assert_eq!(vault.grace_period, grace_period);

    env.ledger().set_timestamp(now + 86_400 + grace_period);
    let boundary_result = client.try_redirect_funds(&vault_id, &usdc);
    assert!(
        matches!(boundary_result, Err(Ok(Error::InvalidTimestamp))),
        "redirect at exact grace boundary must fail: {:?}",
        boundary_result
    );

    env.ledger().set_timestamp(now + 86_400 + grace_period + 1);
    assert!(client.redirect_funds(&vault_id, &usdc));
    assert_eq!(usdc_token.balance(&failure_dest), MIN_AMOUNT);
}

#[test]
fn test_create_vault_rejects_oversized_grace_period() {
    let (env, client, usdc, usdc_asset, _usdc_token) = setup();

    let creator = Address::generate(&env);
    let success_dest = Address::generate(&env);
    let failure_dest = Address::generate(&env);
    let now = 1_700_000_000u64;
    env.ledger().set_timestamp(now);

    usdc_asset.mint(&creator, &MIN_AMOUNT);
    let milestone = BytesN::from_array(&env, &[3u8; 32]);
    let oversized_grace = MAX_VAULT_DURATION + 1;

    let result = client.try_create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &milestone,
        &None,
        &oversized_grace,
        &success_dest,
        &failure_dest,
    );

    assert!(
        matches!(result, Err(Ok(Error::DurationTooLong))),
        "oversized grace period should be rejected: {:?}",
        result
    );
}

#[test]
fn test_redirect_rejects_grace_deadline_overflow() {
    let (env, client, usdc, usdc_asset, _usdc_token) = setup();

    let creator = Address::generate(&env);
    let success_dest = Address::generate(&env);
    let failure_dest = Address::generate(&env);
    let start = u64::MAX - MAX_VAULT_DURATION + 1;
    let end = start + 1;
    let grace_period = MAX_VAULT_DURATION;
    env.ledger().set_timestamp(start);

    usdc_asset.mint(&creator, &MIN_AMOUNT);
    let milestone = BytesN::from_array(&env, &[4u8; 32]);

    let vault_id = client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &start,
        &end,
        &milestone,
        &None,
        &grace_period,
        &success_dest,
        &failure_dest,
    );

    env.ledger().set_timestamp(u64::MAX);
    let result = client.try_redirect_funds(&vault_id, &usdc);
    assert!(
        matches!(result, Err(Ok(Error::InvalidTimestamp))),
        "overflowing grace deadline should be rejected: {:?}",
        result
    );
}
