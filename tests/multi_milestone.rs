#![cfg(test)]

use soroban_sdk::{
    testutils::{Address as _, Ledger},
    token::StellarAssetClient,
    Address, BytesN, Env, Vec,
};

use disciplr_vault::{DisciplrVault, DisciplrVaultClient, VaultStatus, MIN_AMOUNT};

struct Setup {
    env: Env,
    client: DisciplrVaultClient<'static>,
    usdc: Address,
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
        let now = 1_700_200_000u64;
        env.ledger().set_timestamp(now);

        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);
        let usdc_admin = Address::generate(&env);
        let usdc_contract = env.register_stellar_asset_contract_v2(usdc_admin);
        let usdc = usdc_contract.address();
        let asset = StellarAssetClient::new(&env, &usdc);

        Self {
            creator: Address::generate(&env),
            verifier: Address::generate(&env),
            success: Address::generate(&env),
            failure: Address::generate(&env),
            env,
            client,
            usdc,
            asset,
            now,
        }
    }

    fn milestones(&self, count: u8) -> Vec<BytesN<32>> {
        let mut milestones = Vec::new(&self.env);
        let mut index = 0;
        while index < count {
            milestones.push_back(BytesN::from_array(&self.env, &[index + 1; 32]));
            index += 1;
        }
        milestones
    }

    fn create_vault(&self, count: u8) -> u32 {
        self.asset.mint(&self.creator, &MIN_AMOUNT);
        self.client.create_vault(
            &self.usdc,
            &self.creator,
            &MIN_AMOUNT,
            &self.now,
            &(self.now + 86_400),
            &self.milestones(count),
            &Some(self.verifier.clone()),
            &self.success,
            &self.failure,
        )
    }
}

#[test]
fn create_vault_stores_ordered_milestones_with_false_validation_flags() {
    let setup = Setup::new();
    let vault_id = setup.create_vault(3);

    let vault = setup.client.get_vault_state(&vault_id).unwrap();
    assert_eq!(vault.milestones.len(), 3);
    assert_eq!(
        vault.milestones.get_unchecked(1),
        BytesN::from_array(&setup.env, &[2u8; 32])
    );
    assert_eq!(vault.milestone_validations.len(), 3);
    assert!(!vault.milestone_validations.get_unchecked(0));
    assert!(!vault.milestone_validations.get_unchecked(1));
    assert!(!vault.milestone_validations.get_unchecked(2));
}

#[test]
fn validate_milestone_marks_only_requested_index() {
    let setup = Setup::new();
    let vault_id = setup.create_vault(3);

    setup.env.ledger().set_timestamp(setup.now + 10);
    setup.client.validate_milestone(&vault_id, &1);

    let vault = setup.client.get_vault_state(&vault_id).unwrap();
    assert!(!vault.milestone_validations.get_unchecked(0));
    assert!(vault.milestone_validations.get_unchecked(1));
    assert!(!vault.milestone_validations.get_unchecked(2));
    assert_eq!(vault.status, VaultStatus::Active);
}

#[test]
fn release_before_deadline_requires_all_milestones_validated() {
    let setup = Setup::new();
    let vault_id = setup.create_vault(2);

    setup.env.ledger().set_timestamp(setup.now + 10);
    setup.client.validate_milestone(&vault_id, &0);
    assert!(setup
        .client
        .try_release_funds(&vault_id, &setup.usdc)
        .is_err());

    setup.client.validate_milestone(&vault_id, &1);
    setup.client.release_funds(&vault_id, &setup.usdc);

    let vault = setup.client.get_vault_state(&vault_id).unwrap();
    assert_eq!(vault.status, VaultStatus::Completed);
}

#[test]
fn out_of_range_milestone_index_is_rejected() {
    let setup = Setup::new();
    let vault_id = setup.create_vault(2);

    setup.env.ledger().set_timestamp(setup.now + 10);
    assert!(setup.client.try_validate_milestone(&vault_id, &2).is_err());
}

#[test]
fn duplicate_milestone_validation_is_rejected() {
    let setup = Setup::new();
    let vault_id = setup.create_vault(2);

    setup.env.ledger().set_timestamp(setup.now + 10);
    setup.client.validate_milestone(&vault_id, &0);
    assert!(setup.client.try_validate_milestone(&vault_id, &0).is_err());
}

#[test]
fn create_vault_rejects_empty_milestone_vector() {
    let setup = Setup::new();
    setup.asset.mint(&setup.creator, &MIN_AMOUNT);
    let empty = Vec::<BytesN<32>>::new(&setup.env);

    let result = setup.client.try_create_vault(
        &setup.usdc,
        &setup.creator,
        &MIN_AMOUNT,
        &setup.now,
        &(setup.now + 86_400),
        &empty,
        &Some(setup.verifier.clone()),
        &setup.success,
        &setup.failure,
    );

    assert!(result.is_err());
}
