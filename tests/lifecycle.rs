#![cfg(test)]

use soroban_sdk::{
    testutils::{Address as _, Ledger},
    token::{StellarAssetClient, TokenClient},
    Address, BytesN, Env, Symbol, TryIntoVal,
};

use disciplr_vault::{DisciplrVault, DisciplrVaultClient, VaultStatus, MIN_AMOUNT};

fn setup() -> (
    Env,
    DisciplrVaultClient<'static>,
    Address,
    StellarAssetClient<'static>,
    TokenClient<'static>,
    Address,
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

    (
        env,
        client,
        usdc_addr,
        usdc_asset,
        usdc_token_client,
        contract_id,
    )
}

#[test]
fn test_full_lifecycle_success() {
    let (env, client, usdc, usdc_asset, usdc_token, _contract_id) = setup();

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
    let (env, client, usdc, usdc_asset, usdc_token, _contract_id) = setup();

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
fn test_cancel_vault_refunds_creator_and_clears_contract_escrow() {
    let (env, client, usdc, usdc_asset, usdc_token, contract_id) = setup();

    let creator = Address::generate(&env);
    let verifier = Address::generate(&env);
    let success_dest = Address::generate(&env);
    let failure_dest = Address::generate(&env);
    let now = 1_700_000_000u64;
    env.ledger().set_timestamp(now);

    usdc_asset.mint(&creator, &MIN_AMOUNT);

    let creator_before_create = usdc_token.balance(&creator);
    let contract_before_create = usdc_token.balance(&contract_id);
    let milestone = BytesN::from_array(&env, &[1u8; 32]);

    let vault_id = client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &milestone,
        &Some(verifier),
        &success_dest,
        &failure_dest,
    );

    assert_eq!(
        creator_before_create - usdc_token.balance(&creator),
        MIN_AMOUNT
    );
    assert_eq!(
        usdc_token.balance(&contract_id) - contract_before_create,
        MIN_AMOUNT
    );

    let creator_before_cancel = usdc_token.balance(&creator);
    let result = client.cancel_vault(&vault_id, &usdc);

    assert!(result);
    assert_eq!(
        usdc_token.balance(&creator) - creator_before_cancel,
        MIN_AMOUNT
    );
    assert_eq!(usdc_token.balance(&contract_id), contract_before_create);
    assert_eq!(
        client.get_vault_state(&vault_id).unwrap().status,
        VaultStatus::Cancelled
    );

    let mut found_cancel_event = false;
    for (emitting_contract, topics, _) in env.events().all() {
        if emitting_contract != contract_id {
            continue;
        }

        let event_name: Symbol = topics.get(0).unwrap().try_into_val(&env).unwrap();
        if event_name == Symbol::new(&env, "vault_cancelled") {
            let event_vault_id: u32 = topics.get(1).unwrap().try_into_val(&env).unwrap();
            assert_eq!(event_vault_id, vault_id);
            found_cancel_event = true;
        }
    }

    assert!(found_cancel_event, "vault_cancelled event must be emitted");
}
