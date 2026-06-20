#![cfg(test)]

use disciplr_vault::{DisciplrVault, DisciplrVaultClient, Error, VaultStatus, MIN_AMOUNT};
use soroban_sdk::{
    testutils::{Address as _, Events, Ledger},
    token::{StellarAssetClient, TokenClient},
    Address, BytesN, Env, Symbol, TryIntoVal,
};

struct RedirectSetup {
    env: Env,
    contract_id: Address,
    client: DisciplrVaultClient<'static>,
    usdc: Address,
    usdc_token: TokenClient<'static>,
    creator: Address,
    verifier: Address,
    success_destination: Address,
    failure_destination: Address,
    start: u64,
    end: u64,
}

impl RedirectSetup {
    fn new() -> Self {
        let env = Env::default();
        env.mock_all_auths();

        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);

        let usdc_admin = Address::generate(&env);
        let usdc_contract = env.register_stellar_asset_contract_v2(usdc_admin.clone());
        let usdc = usdc_contract.address();
        let usdc_asset = StellarAssetClient::new(&env, &usdc);
        let usdc_token = TokenClient::new(&env, &usdc);

        let creator = Address::generate(&env);
        let verifier = Address::generate(&env);
        let success_destination = Address::generate(&env);
        let failure_destination = Address::generate(&env);
        let start = 1_700_000_000u64;
        let end = start + 86_400;

        env.ledger().set_timestamp(start);
        usdc_asset.mint(&creator, &MIN_AMOUNT);

        Self {
            env,
            contract_id,
            client,
            usdc,
            usdc_token,
            creator,
            verifier,
            success_destination,
            failure_destination,
            start,
            end,
        }
    }

    fn create_vault(&self) -> u32 {
        self.client.create_vault(
            &self.usdc,
            &self.creator,
            &MIN_AMOUNT,
            &self.start,
            &self.end,
            &BytesN::from_array(&self.env, &[0x27; 32]),
            &Some(self.verifier.clone()),
            &self.success_destination,
            &self.failure_destination,
        )
    }
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

fn has_contract_event(env: &Env, contract_id: &Address, name: &str, vault_id: u32) -> bool {
    for (emitting_contract, topics, _) in env.events().all() {
        if emitting_contract != contract_id.clone() || topics.len() < 2 {
            continue;
        }

        let event_name: Symbol = topics.get(0).unwrap().try_into_val(env).unwrap();
        let event_vault_id: u32 = topics.get(1).unwrap().try_into_val(env).unwrap();

        if event_name == Symbol::new(env, name) && event_vault_id == vault_id {
            return true;
        }
    }

    false
}

#[test]
fn validated_vault_cannot_redirect_after_deadline_and_can_release() {
    let setup = RedirectSetup::new();
    let vault_id = setup.create_vault();

    setup.client.validate_milestone(&vault_id);
    setup.env.ledger().set_timestamp(setup.end + 1);

    let failure_before = setup.usdc_token.balance(&setup.failure_destination);
    let redirect_result = setup.client.try_redirect_funds(&vault_id, &setup.usdc);

    assert_contract_error(redirect_result, Error::NotAuthorized);
    assert_eq!(
        setup.usdc_token.balance(&setup.failure_destination),
        failure_before,
        "rejected redirect must not credit failure destination"
    );

    let vault_after_redirect = setup.client.get_vault_state(&vault_id).unwrap();
    assert_eq!(vault_after_redirect.status, VaultStatus::Active);
    assert!(vault_after_redirect.milestone_validated);

    let success_before = setup.usdc_token.balance(&setup.success_destination);
    assert!(setup.client.release_funds(&vault_id, &setup.usdc));

    assert_eq!(
        setup.usdc_token.balance(&setup.success_destination) - success_before,
        MIN_AMOUNT
    );
    assert_eq!(
        setup.usdc_token.balance(&setup.failure_destination),
        failure_before
    );

    let final_vault = setup.client.get_vault_state(&vault_id).unwrap();
    assert_eq!(final_vault.status, VaultStatus::Completed);
    assert!(has_contract_event(
        &setup.env,
        &setup.contract_id,
        "funds_released",
        vault_id
    ));
}
