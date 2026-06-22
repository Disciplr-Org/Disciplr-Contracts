#![cfg(test)]

use soroban_sdk::{
    testutils::{Address as _, Ledger},
    token::{StellarAssetClient, TokenClient},
    Address, BytesN, Env,
};

use disciplr_vault::{DisciplrVault, DisciplrVaultClient, VaultStatus, MIN_AMOUNT};

struct Setup {
    env: Env,
    client: DisciplrVaultClient<'static>,
    usdc: Address,
    token: TokenClient<'static>,
    asset: StellarAssetClient<'static>,
    creator: Address,
    verifier: Address,
    success: Address,
    failure: Address,
    now: u64,
}

impl Setup {
    fn new() -> Self {
        let env = Env::default();
        env.mock_all_auths();
        let now = 1_700_100_000u64;
        env.ledger().set_timestamp(now);

        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);

        let usdc_admin = Address::generate(&env);
        let usdc_contract = env.register_stellar_asset_contract_v2(usdc_admin);
        let usdc = usdc_contract.address();
        let asset = StellarAssetClient::new(&env, &usdc);
        let token = TokenClient::new(&env, &usdc);

        let creator = Address::generate(&env);
        let verifier = Address::generate(&env);
        let success = Address::generate(&env);
        let failure = Address::generate(&env);

        Self {
            env,
            client,
            usdc,
            token,
            asset,
            creator,
            verifier,
            success,
            failure,
            now,
        }
    }

    fn create_vault(&self, amount: i128) -> u32 {
        self.asset.mint(&self.creator, &amount);
        self.client.create_vault(
            &self.usdc,
            &self.creator,
            &amount,
            &self.now,
            &(self.now + 86_400),
            &BytesN::from_array(&self.env, &[21u8; 32]),
            &Some(self.verifier.clone()),
            &self.success,
            &self.failure,
        )
    }
}

#[test]
fn partial_release_keeps_vault_active_and_tracks_remaining_balance() {
    let setup = Setup::new();
    let amount = MIN_AMOUNT * 3;
    let vault_id = setup.create_vault(amount);

    setup.env.ledger().set_timestamp(setup.now + 3_600);
    setup.client.validate_milestone(&vault_id);

    let first_tranche = MIN_AMOUNT;
    setup
        .client
        .release_partial(&vault_id, &setup.usdc, &first_tranche);

    let vault = setup.client.get_vault_state(&vault_id).unwrap();
    assert_eq!(vault.status, VaultStatus::Active);
    assert_eq!(vault.amount, amount);
    assert_eq!(vault.remaining_amount, amount - first_tranche);
    assert_eq!(setup.token.balance(&setup.success), first_tranche);
}

#[test]
fn final_partial_release_completes_vault() {
    let setup = Setup::new();
    let amount = MIN_AMOUNT * 2;
    let vault_id = setup.create_vault(amount);

    setup.env.ledger().set_timestamp(setup.now + 3_600);
    setup.client.validate_milestone(&vault_id);

    setup
        .client
        .release_partial(&vault_id, &setup.usdc, &MIN_AMOUNT);
    setup
        .client
        .release_partial(&vault_id, &setup.usdc, &MIN_AMOUNT);

    let vault = setup.client.get_vault_state(&vault_id).unwrap();
    assert_eq!(vault.status, VaultStatus::Completed);
    assert_eq!(vault.remaining_amount, 0);
    assert_eq!(setup.token.balance(&setup.success), amount);
}

#[test]
fn release_funds_drains_remaining_after_partial_release() {
    let setup = Setup::new();
    let amount = MIN_AMOUNT * 4;
    let vault_id = setup.create_vault(amount);

    setup.env.ledger().set_timestamp(setup.now + 3_600);
    setup.client.validate_milestone(&vault_id);

    let first_tranche = MIN_AMOUNT;
    setup
        .client
        .release_partial(&vault_id, &setup.usdc, &first_tranche);
    setup.client.release_funds(&vault_id, &setup.usdc);

    let vault = setup.client.get_vault_state(&vault_id).unwrap();
    assert_eq!(vault.status, VaultStatus::Completed);
    assert_eq!(vault.remaining_amount, 0);
    assert_eq!(setup.token.balance(&setup.success), amount);
}

#[test]
fn invalid_partial_amounts_are_rejected() {
    let setup = Setup::new();
    let amount = MIN_AMOUNT * 2;
    let vault_id = setup.create_vault(amount);

    setup.env.ledger().set_timestamp(setup.now + 3_600);
    setup.client.validate_milestone(&vault_id);

    assert!(setup
        .client
        .try_release_partial(&vault_id, &setup.usdc, &0)
        .is_err());
    assert!(setup
        .client
        .try_release_partial(&vault_id, &setup.usdc, &(amount + 1))
        .is_err());
}

#[test]
fn partial_release_requires_same_authorization_gate_as_full_release() {
    let setup = Setup::new();
    let vault_id = setup.create_vault(MIN_AMOUNT * 2);

    assert!(setup
        .client
        .try_release_partial(&vault_id, &setup.usdc, &MIN_AMOUNT)
        .is_err());
}

#[test]
fn redirect_after_validated_partial_release_is_rejected() {
    let setup = Setup::new();
    let amount = MIN_AMOUNT * 3;
    let vault_id = setup.create_vault(amount);

    setup.env.ledger().set_timestamp(setup.now + 3_600);
    setup.client.validate_milestone(&vault_id);
    setup
        .client
        .release_partial(&vault_id, &setup.usdc, &MIN_AMOUNT);

    let result = setup.client.try_redirect_funds(&vault_id, &setup.usdc);
    assert!(result.is_err());
}

#[test]
fn redirect_after_deadline_partial_release_sends_only_remaining_balance() {
    let setup = Setup::new();
    let amount = MIN_AMOUNT * 3;
    let vault_id = setup.create_vault(amount);

    setup.env.ledger().set_timestamp(setup.now + 86_401);
    setup
        .client
        .release_partial(&vault_id, &setup.usdc, &MIN_AMOUNT);
    setup.client.redirect_funds(&vault_id, &setup.usdc);

    let vault = setup.client.get_vault_state(&vault_id).unwrap();
    assert_eq!(vault.status, VaultStatus::Failed);
    assert_eq!(vault.remaining_amount, 0);
    assert_eq!(setup.token.balance(&setup.success), MIN_AMOUNT);
    assert_eq!(setup.token.balance(&setup.failure), amount - MIN_AMOUNT);
}

#[test]
fn cancel_after_partial_release_refunds_only_remaining_balance() {
    let setup = Setup::new();
    let amount = MIN_AMOUNT * 3;
    let vault_id = setup.create_vault(amount);

    setup.env.ledger().set_timestamp(setup.now + 3_600);
    setup.client.validate_milestone(&vault_id);
    setup
        .client
        .release_partial(&vault_id, &setup.usdc, &MIN_AMOUNT);

    let creator_before = setup.token.balance(&setup.creator);
    setup.client.cancel_vault(&vault_id, &setup.usdc);

    let vault = setup.client.get_vault_state(&vault_id).unwrap();
    assert_eq!(vault.status, VaultStatus::Cancelled);
    assert_eq!(vault.remaining_amount, 0);
    assert_eq!(
        setup.token.balance(&setup.creator) - creator_before,
        amount - MIN_AMOUNT
    );
}
