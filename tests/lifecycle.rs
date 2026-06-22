#![cfg(test)]

use soroban_sdk::{
    testutils::{Address as _, Ledger},
    token::{StellarAssetClient, TokenClient},
    Address, BytesN, Env, Vec,
};

use disciplr_vault::{DisciplrVault, DisciplrVaultClient, VaultStatus, MIN_AMOUNT};

fn single_milestone(env: &Env, hash: BytesN<32>) -> Vec<BytesN<32>> {
    let mut milestones = Vec::new(env);
    milestones.push_back(hash);
    milestones
}

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
    let milestones = single_milestone(&env, milestone);

    // 1. Create Vault
    let vault_id = client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &milestones,
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
    client.validate_milestone(&vault_id, &0);
    assert!(client
        .get_vault_state(&vault_id)
        .unwrap()
        .milestone_validations
        .get_unchecked(0));

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
    let milestones = single_milestone(&env, milestone);

    // 1. Create Vault
    let vault_id = client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &milestones,
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
