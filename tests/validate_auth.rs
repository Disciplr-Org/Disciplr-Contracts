#![cfg(test)]

extern crate std;

use disciplr_vault::{DisciplrVault, DisciplrVaultClient, VaultStatus, MIN_AMOUNT};
use soroban_sdk::{
    testutils::{Address as _, Ledger, MockAuth, MockAuthInvoke},
    token::StellarAssetClient,
    Address, BytesN, Env, IntoVal,
};

struct ValidateAuthSetup {
    env: Env,
    client: DisciplrVaultClient<'static>,
    usdc: Address,
    creator: Address,
    verifier: Address,
    stranger: Address,
    success: Address,
    failure: Address,
    start: u64,
    end: u64,
}

impl ValidateAuthSetup {
    fn new() -> Self {
        let env = Env::default();
        env.mock_all_auths();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);

        let usdc_admin = Address::generate(&env);
        let usdc_contract = env.register_stellar_asset_contract_v2(usdc_admin);
        let usdc = usdc_contract.address();
        let usdc_asset = StellarAssetClient::new(&env, &usdc);

        let creator = Address::generate(&env);
        let verifier = Address::generate(&env);
        let stranger = Address::generate(&env);
        let success = Address::generate(&env);
        let failure = Address::generate(&env);

        let start = 1_725_000_000u64;
        let end = start + 86_400;
        env.ledger().set_timestamp(start);
        usdc_asset.mint(&creator, &MIN_AMOUNT);

        Self {
            env,
            client,
            usdc,
            creator,
            verifier,
            stranger,
            success,
            failure,
            start,
            end,
        }
    }

    fn create_vault(&self, verifier: Option<Address>) -> u32 {
        self.client.mock_all_auths().create_vault(
            &self.usdc,
            &self.creator,
            &MIN_AMOUNT,
            &self.start,
            &self.end,
            &BytesN::from_array(&self.env, &[22u8; 32]),
            &verifier,
            &self.success,
            &self.failure,
        )
    }

    fn validate_with_auth(&self, signer: &Address, vault_id: u32) -> bool {
        self.client
            .mock_auths(&[MockAuth {
                address: signer,
                invoke: &MockAuthInvoke {
                    contract: &self.client.address,
                    fn_name: "validate_milestone",
                    args: (&vault_id,).into_val(&self.env),
                    sub_invokes: &[],
                },
            }])
            .validate_milestone(&vault_id)
    }
}

fn assert_active_unvalidated(setup: &ValidateAuthSetup, vault_id: u32) {
    let vault = setup.client.get_vault_state(&vault_id).unwrap();
    assert_eq!(vault.status, VaultStatus::Active);
    assert!(!vault.milestone_validated);
}

#[test]
fn verifier_configuration_rejects_stranger_and_preserves_state() {
    let setup = ValidateAuthSetup::new();
    let vault_id = setup.create_vault(Some(setup.verifier.clone()));

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        setup.validate_with_auth(&setup.stranger, vault_id);
    }));

    assert!(
        result.is_err(),
        "stranger auth must not satisfy verifier auth"
    );
    assert_active_unvalidated(&setup, vault_id);
}

#[test]
fn verifier_configuration_accepts_designated_verifier() {
    let setup = ValidateAuthSetup::new();
    let vault_id = setup.create_vault(Some(setup.verifier.clone()));

    assert!(setup.validate_with_auth(&setup.verifier, vault_id));

    let vault = setup.client.get_vault_state(&vault_id).unwrap();
    assert_eq!(vault.status, VaultStatus::Active);
    assert!(vault.milestone_validated);
}

#[test]
fn no_verifier_configuration_rejects_non_creator_and_preserves_state() {
    let setup = ValidateAuthSetup::new();
    let vault_id = setup.create_vault(None);

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        setup.validate_with_auth(&setup.stranger, vault_id);
    }));

    assert!(
        result.is_err(),
        "stranger auth must not satisfy creator auth"
    );
    assert_active_unvalidated(&setup, vault_id);
}

#[test]
fn no_verifier_configuration_accepts_creator() {
    let setup = ValidateAuthSetup::new();
    let vault_id = setup.create_vault(None);

    assert!(setup.validate_with_auth(&setup.creator, vault_id));

    let vault = setup.client.get_vault_state(&vault_id).unwrap();
    assert_eq!(vault.status, VaultStatus::Active);
    assert!(vault.milestone_validated);
}

#[test]
fn creator_as_explicit_verifier_rejects_stranger() {
    let setup = ValidateAuthSetup::new();
    let vault_id = setup.create_vault(Some(setup.creator.clone()));

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        setup.validate_with_auth(&setup.stranger, vault_id);
    }));

    assert!(
        result.is_err(),
        "stranger auth must not satisfy creator-as-verifier auth"
    );
    assert_active_unvalidated(&setup, vault_id);
}

#[test]
fn expired_vault_requires_authorized_validator_before_expiry_error() {
    let setup = ValidateAuthSetup::new();
    let vault_id = setup.create_vault(Some(setup.verifier.clone()));
    setup.env.ledger().set_timestamp(setup.end);

    let unauthorized = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        setup.validate_with_auth(&setup.stranger, vault_id);
    }));
    assert!(unauthorized.is_err());
    assert_active_unvalidated(&setup, vault_id);

    let authorized = setup
        .client
        .mock_auths(&[MockAuth {
            address: &setup.verifier,
            invoke: &MockAuthInvoke {
                contract: &setup.client.address,
                fn_name: "validate_milestone",
                args: (&vault_id,).into_val(&setup.env),
                sub_invokes: &[],
            },
        }])
        .try_validate_milestone(&vault_id);
    assert!(
        authorized.is_err(),
        "authorized expired validation should fail"
    );
    assert_active_unvalidated(&setup, vault_id);
}
