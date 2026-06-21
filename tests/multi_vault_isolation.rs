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

struct VaultActors {
    creator: Address,
    verifier: Address,
    success: Address,
    failure: Address,
}

impl VaultActors {
    fn generate(env: &Env) -> Self {
        Self {
            creator: Address::generate(env),
            verifier: Address::generate(env),
            success: Address::generate(env),
            failure: Address::generate(env),
        }
    }
}

#[test]
fn test_multi_vault_lifecycle_isolation_for_ids_states_and_balances() {
    let (env, client, usdc, usdc_asset, usdc_token) = setup();
    let now = 1_700_000_000u64;
    env.ledger().set_timestamp(now);

    let completed = VaultActors::generate(&env);
    let failed = VaultActors::generate(&env);
    let cancelled = VaultActors::generate(&env);

    usdc_asset.mint(&completed.creator, &MIN_AMOUNT);
    usdc_asset.mint(&failed.creator, &MIN_AMOUNT);
    usdc_asset.mint(&cancelled.creator, &MIN_AMOUNT);

    let completed_id = client.create_vault(
        &usdc,
        &completed.creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[1u8; 32]),
        &Some(completed.verifier.clone()),
        &completed.success,
        &completed.failure,
    );

    let failed_id = client.create_vault(
        &usdc,
        &failed.creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[2u8; 32]),
        &Some(failed.verifier.clone()),
        &failed.success,
        &failed.failure,
    );

    let cancelled_id = client.create_vault(
        &usdc,
        &cancelled.creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[3u8; 32]),
        &Some(cancelled.verifier.clone()),
        &cancelled.success,
        &cancelled.failure,
    );

    assert_eq!(completed_id, 0);
    assert_eq!(failed_id, 1);
    assert_eq!(cancelled_id, 2);
    assert_eq!(client.vault_count(), 3);

    env.ledger().set_timestamp(now + 3_600);
    client.validate_milestone(&completed_id);
    client.release_funds(&completed_id, &usdc);

    env.ledger().set_timestamp(now + 86_401);
    client.redirect_funds(&failed_id, &usdc);

    env.ledger().set_timestamp(now + 7_200);
    client.cancel_vault(&cancelled_id, &usdc);

    let completed_state = client.get_vault_state(&completed_id).unwrap();
    let failed_state = client.get_vault_state(&failed_id).unwrap();
    let cancelled_state = client.get_vault_state(&cancelled_id).unwrap();

    assert_eq!(completed_state.status, VaultStatus::Completed);
    assert_eq!(failed_state.status, VaultStatus::Failed);
    assert_eq!(cancelled_state.status, VaultStatus::Cancelled);

    assert_eq!(usdc_token.balance(&completed.success), MIN_AMOUNT);
    assert_eq!(usdc_token.balance(&completed.failure), 0);
    assert_eq!(usdc_token.balance(&completed.creator), 0);

    assert_eq!(usdc_token.balance(&failed.success), 0);
    assert_eq!(usdc_token.balance(&failed.failure), MIN_AMOUNT);
    assert_eq!(usdc_token.balance(&failed.creator), 0);

    assert_eq!(usdc_token.balance(&cancelled.success), 0);
    assert_eq!(usdc_token.balance(&cancelled.failure), 0);
    assert_eq!(usdc_token.balance(&cancelled.creator), MIN_AMOUNT);

    assert_eq!(client.vault_count(), 3);
}
