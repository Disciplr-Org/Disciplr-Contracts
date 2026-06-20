#![cfg(test)]

use disciplr_vault::{DisciplrVault, DisciplrVaultClient, VaultStatus, MIN_AMOUNT};
use soroban_sdk::{
    testutils::{Address as _, Ledger},
    token::{StellarAssetClient, TokenClient},
    Address, BytesN, Env,
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
    let usdc_token = env.register_stellar_asset_contract_v2(usdc_admin);
    let usdc_addr = usdc_token.address();
    let usdc_asset = StellarAssetClient::new(&env, &usdc_addr);
    let usdc_client = TokenClient::new(&env, &usdc_addr);

    (env, client, usdc_addr, usdc_asset, usdc_client)
}

fn create_vault(
    env: &Env,
    client: &DisciplrVaultClient,
    usdc: &Address,
    creator: &Address,
    amount: i128,
    start: u64,
    end: u64,
    hash_byte: u8,
    success: &Address,
    failure: &Address,
) -> u32 {
    client.create_vault(
        usdc,
        creator,
        &amount,
        &start,
        &end,
        &BytesN::from_array(env, &[hash_byte; 32]),
        &None,
        success,
        failure,
    )
}

#[test]
fn multi_vault_lifecycle_outcomes_keep_ids_state_and_balances_isolated() {
    let (env, client, usdc, usdc_asset, usdc_client) = setup();

    let now = 1_725_000_000u64;
    let end = now + 86_400;
    env.ledger().set_timestamp(now);

    let release_creator = Address::generate(&env);
    let redirect_creator = Address::generate(&env);
    let cancel_creator = Address::generate(&env);

    let release_success = Address::generate(&env);
    let release_failure = Address::generate(&env);
    let redirect_success = Address::generate(&env);
    let redirect_failure = Address::generate(&env);
    let cancel_success = Address::generate(&env);
    let cancel_failure = Address::generate(&env);

    let release_amount = MIN_AMOUNT;
    let redirect_amount = MIN_AMOUNT * 2;
    let cancel_amount = MIN_AMOUNT * 3;

    usdc_asset.mint(&release_creator, &release_amount);
    usdc_asset.mint(&redirect_creator, &redirect_amount);
    usdc_asset.mint(&cancel_creator, &cancel_amount);

    let release_vault = create_vault(
        &env,
        &client,
        &usdc,
        &release_creator,
        release_amount,
        now,
        end,
        1,
        &release_success,
        &release_failure,
    );
    let redirect_vault = create_vault(
        &env,
        &client,
        &usdc,
        &redirect_creator,
        redirect_amount,
        now,
        end,
        2,
        &redirect_success,
        &redirect_failure,
    );
    let cancel_vault = create_vault(
        &env,
        &client,
        &usdc,
        &cancel_creator,
        cancel_amount,
        now,
        end,
        3,
        &cancel_success,
        &cancel_failure,
    );

    assert_eq!(release_vault, 0);
    assert_eq!(redirect_vault, 1);
    assert_eq!(cancel_vault, 2);
    assert_eq!(client.vault_count(), 3);

    assert_eq!(usdc_client.balance(&release_creator), 0);
    assert_eq!(usdc_client.balance(&redirect_creator), 0);
    assert_eq!(usdc_client.balance(&cancel_creator), 0);

    env.ledger().set_timestamp(end + 1);

    client.release_funds(&release_vault, &usdc);
    client.cancel_vault(&cancel_vault, &usdc);
    client.redirect_funds(&redirect_vault, &usdc);

    assert_eq!(
        client.get_vault_state(&release_vault).unwrap().status,
        VaultStatus::Completed
    );
    assert_eq!(
        client.get_vault_state(&redirect_vault).unwrap().status,
        VaultStatus::Failed
    );
    assert_eq!(
        client.get_vault_state(&cancel_vault).unwrap().status,
        VaultStatus::Cancelled
    );
    assert_eq!(client.vault_count(), 3);

    assert_eq!(usdc_client.balance(&release_success), release_amount);
    assert_eq!(usdc_client.balance(&redirect_failure), redirect_amount);
    assert_eq!(usdc_client.balance(&cancel_creator), cancel_amount);

    assert_eq!(usdc_client.balance(&release_failure), 0);
    assert_eq!(usdc_client.balance(&redirect_success), 0);
    assert_eq!(usdc_client.balance(&cancel_success), 0);
    assert_eq!(usdc_client.balance(&cancel_failure), 0);

    assert_eq!(usdc_client.balance(&release_creator), 0);
    assert_eq!(usdc_client.balance(&redirect_creator), 0);
}
