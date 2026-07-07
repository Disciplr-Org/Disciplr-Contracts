#![cfg(test)]

use soroban_sdk::{
    testutils::{Address as _, Ledger},
    token::{StellarAssetClient, TokenClient},
    Address, BytesN, Env,
};

use disciplr_vault::{DisciplrVault, DisciplrVaultClient, VaultStatus, MIN_AMOUNT};

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
fn partial_release_tracks_remaining_and_final_release_completes() {
    let (env, client, usdc, usdc_asset, usdc_token) = setup();

    let creator = Address::generate(&env);
    let verifier = Address::generate(&env);
    let success_dest = Address::generate(&env);
    let failure_dest = Address::generate(&env);
    let now = 1_700_000_000u64;
    env.ledger().set_timestamp(now);

    usdc_asset.mint(&creator, &MIN_AMOUNT);

    let milestone = BytesN::from_array(&env, &[7u8; 32]);
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

    env.ledger().set_timestamp(now + 3_600);
    client.validate_milestone(&vault_id);

    let first = MIN_AMOUNT / 4;
    let second = MIN_AMOUNT / 4;
    client.release_partial(&vault_id, &usdc, &first);
    client.release_partial(&vault_id, &usdc, &second);

    let active_state = client.get_vault_state(&vault_id).unwrap();
    assert_eq!(active_state.status, VaultStatus::Active);
    assert_eq!(active_state.amount, MIN_AMOUNT);
    assert_eq!(active_state.remaining, MIN_AMOUNT - first - second);
    assert_eq!(usdc_token.balance(&success_dest), first + second);

    client.release_funds(&vault_id, &usdc);

    let final_state = client.get_vault_state(&vault_id).unwrap();
    assert_eq!(final_state.status, VaultStatus::Completed);
    assert_eq!(final_state.remaining, 0);
    assert_eq!(usdc_token.balance(&success_dest), MIN_AMOUNT);
}
