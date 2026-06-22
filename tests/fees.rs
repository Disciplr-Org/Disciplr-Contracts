#![cfg(test)]

use disciplr_vault::{
    DisciplrVault, DisciplrVaultClient, Error, ProtocolFeeConfig, MAX_FEE_BPS, MIN_AMOUNT,
};
use soroban_sdk::{
    testutils::{Address as _, Ledger},
    token::{StellarAssetClient, TokenClient},
    Address, BytesN, Env,
};

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
    fee_recipient: Address,
}

impl Setup {
    fn new() -> Self {
        let env = Env::default();
        env.mock_all_auths();
        env.ledger().set_timestamp(1_700_000_000);

        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);

        let usdc_admin = Address::generate(&env);
        let usdc_token = env.register_stellar_asset_contract_v2(usdc_admin);
        let usdc = usdc_token.address();
        let asset = StellarAssetClient::new(&env, &usdc);
        let token = TokenClient::new(&env, &usdc);

        Self {
            creator: Address::generate(&env),
            verifier: Address::generate(&env),
            success: Address::generate(&env),
            failure: Address::generate(&env),
            fee_recipient: Address::generate(&env),
            env,
            client,
            usdc,
            token,
            asset,
        }
    }

    fn create_vault(&self, amount: i128, fee_bps: u32) -> u32 {
        self.asset.mint(&self.creator, &amount);
        let now = self.env.ledger().timestamp();
        self.client.create_vault(
            &self.usdc,
            &self.creator,
            &amount,
            &now,
            &(now + 86_400),
            &BytesN::from_array(&self.env, &[9u8; 32]),
            &Some(self.verifier.clone()),
            &self.success,
            &self.failure,
            &ProtocolFeeConfig {
                fee_bps,
                fee_recipient: self.fee_recipient.clone(),
            },
        )
    }
}

#[test]
fn zero_fee_release_preserves_existing_destination_amount() {
    let setup = Setup::new();
    let vault_id = setup.create_vault(MIN_AMOUNT, 0);

    setup.client.validate_milestone(&vault_id);
    setup.client.release_funds(&vault_id, &setup.usdc);

    assert_eq!(setup.token.balance(&setup.success), MIN_AMOUNT);
    assert_eq!(setup.token.balance(&setup.fee_recipient), 0);
}

#[test]
fn max_fee_release_routes_fee_and_net_amount() {
    let setup = Setup::new();
    let amount = MIN_AMOUNT * 10;
    let vault_id = setup.create_vault(amount, MAX_FEE_BPS);
    let fee = amount * i128::from(MAX_FEE_BPS) / 10_000;

    setup.client.validate_milestone(&vault_id);
    setup.client.release_funds(&vault_id, &setup.usdc);

    assert_eq!(setup.token.balance(&setup.fee_recipient), fee);
    assert_eq!(setup.token.balance(&setup.success), amount - fee);
}

#[test]
fn redirect_uses_same_fee_split_as_release() {
    let setup = Setup::new();
    let amount = MIN_AMOUNT * 5;
    let vault_id = setup.create_vault(amount, 250);
    let fee = amount * 250 / 10_000;

    setup.env.ledger().set_timestamp(1_700_086_401);
    setup.client.redirect_funds(&vault_id, &setup.usdc);

    assert_eq!(setup.token.balance(&setup.fee_recipient), fee);
    assert_eq!(setup.token.balance(&setup.failure), amount - fee);
    assert_eq!(setup.token.balance(&setup.success), 0);
}

#[test]
fn fee_rounds_up_in_protocol_favor() {
    let setup = Setup::new();
    let amount = MIN_AMOUNT + 1;
    let vault_id = setup.create_vault(amount, 1);

    setup.client.validate_milestone(&vault_id);
    setup.client.release_funds(&vault_id, &setup.usdc);

    assert_eq!(setup.token.balance(&setup.fee_recipient), 1_001);
    assert_eq!(setup.token.balance(&setup.success), amount - 1_001);
}

#[test]
fn create_vault_rejects_fee_above_cap_before_transfer() {
    let setup = Setup::new();
    setup.asset.mint(&setup.creator, &MIN_AMOUNT);
    let now = setup.env.ledger().timestamp();

    let result = setup.client.try_create_vault(
        &setup.usdc,
        &setup.creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &BytesN::from_array(&setup.env, &[7u8; 32]),
        &None,
        &setup.success,
        &setup.failure,
        &ProtocolFeeConfig {
            fee_bps: MAX_FEE_BPS + 1,
            fee_recipient: setup.fee_recipient.clone(),
        },
    );

    assert_eq!(result, Err(Ok(Error::InvalidFee)));
    assert_eq!(setup.token.balance(&setup.creator), MIN_AMOUNT);
}
