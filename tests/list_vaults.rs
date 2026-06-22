#![cfg(test)]

use disciplr_vault::{
    DisciplrVault, DisciplrVaultClient, Error, VaultStatus, MAX_LIST_VAULTS_LIMIT, MIN_AMOUNT,
};
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
    env.ledger().set_timestamp(1_700_000_000);

    let contract_id = env.register(DisciplrVault, ());
    let client = DisciplrVaultClient::new(&env, &contract_id);

    let usdc_admin = Address::generate(&env);
    let usdc_token = env.register_stellar_asset_contract_v2(usdc_admin.clone());
    let usdc_addr = usdc_token.address();
    let usdc_asset = StellarAssetClient::new(&env, &usdc_addr);

    (env, client, usdc_addr, usdc_asset)
}

fn create_vault(
    env: &Env,
    client: &DisciplrVaultClient<'_>,
    usdc: &Address,
    usdc_asset: &StellarAssetClient<'_>,
    start_offset: u64,
) -> u32 {
    let creator = Address::generate(env);
    let success = Address::generate(env);
    let failure = Address::generate(env);
    let now = env.ledger().timestamp();
    let start = now + start_offset;
    let end = start + 86_400;

    usdc_asset.mint(&creator, &MIN_AMOUNT);
    client.create_vault(
        usdc,
        &creator,
        &MIN_AMOUNT,
        &start,
        &end,
        &BytesN::from_array(env, &[start_offset as u8; 32]),
        &None,
        &success,
        &failure,
    )
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
fn list_vaults_empty_and_zero_limit_return_empty_pages() {
    let (_env, client, _usdc, _usdc_asset) = setup();

    assert_eq!(client.list_vaults(&0, &10).len(), 0);
    assert_eq!(client.list_vaults(&0, &0).len(), 0);
}

#[test]
fn list_vaults_returns_partial_window_with_ids() {
    let (env, client, usdc, usdc_asset) = setup();
    let first = create_vault(&env, &client, &usdc, &usdc_asset, 10);
    let second = create_vault(&env, &client, &usdc, &usdc_asset, 20);
    let third = create_vault(&env, &client, &usdc, &usdc_asset, 30);

    assert_eq!(first, 0);
    assert_eq!(second, 1);
    assert_eq!(third, 2);

    let page = client.list_vaults(&1, &2);
    assert_eq!(page.len(), 2);

    let (id_1, vault_1) = page.get(0).unwrap();
    let (id_2, vault_2) = page.get(1).unwrap();
    assert_eq!(id_1, second);
    assert_eq!(id_2, third);
    assert_eq!(vault_1.status, VaultStatus::Active);
    assert_eq!(vault_2.status, VaultStatus::Active);
}

#[test]
fn list_vaults_start_beyond_count_returns_empty_page() {
    let (env, client, usdc, usdc_asset) = setup();
    create_vault(&env, &client, &usdc, &usdc_asset, 10);

    assert_eq!(client.list_vaults(&99, &10).len(), 0);
}

#[test]
fn list_vaults_rejects_limit_over_cap() {
    let (_env, client, _usdc, _usdc_asset) = setup();
    let result = client.try_list_vaults(&0, &(MAX_LIST_VAULTS_LIMIT + 1));

    assert_contract_error(result, Error::LimitTooLarge);
}

#[test]
fn list_vaults_includes_terminal_vaults() {
    let (env, client, usdc, usdc_asset) = setup();
    let completed = create_vault(&env, &client, &usdc, &usdc_asset, 10);
    let failed = create_vault(&env, &client, &usdc, &usdc_asset, 20);
    let cancelled = create_vault(&env, &client, &usdc, &usdc_asset, 30);

    env.ledger().set_timestamp(1_700_000_000 + 30 + 86_401);
    client.release_funds(&completed, &usdc);
    client.redirect_funds(&failed, &usdc);
    client.cancel_vault(&cancelled, &usdc);

    let page = client.list_vaults(&0, &MAX_LIST_VAULTS_LIMIT);
    assert_eq!(page.len(), 3);
    assert_eq!(page.get(0).unwrap().1.status, VaultStatus::Completed);
    assert_eq!(page.get(1).unwrap().1.status, VaultStatus::Failed);
    assert_eq!(page.get(2).unwrap().1.status, VaultStatus::Cancelled);
}
