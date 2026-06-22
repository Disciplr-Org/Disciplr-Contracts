#![cfg(test)]

use soroban_sdk::{
    testutils::{Address as _, Events, Ledger},
    token::StellarAssetClient,
    Address, BytesN, Env, Symbol, TryIntoVal,
};

use disciplr_vault::{
    DisciplrVault, DisciplrVaultClient, VaultLifecycleEventData, VaultStatus, MIN_AMOUNT,
};

struct TestSetup {
    env: Env,
    contract_id: Address,
    client: DisciplrVaultClient<'static>,
    usdc: Address,
    creator: Address,
    verifier: Address,
    success_dest: Address,
    failure_dest: Address,
    milestone: BytesN<32>,
    now: u64,
}

impl TestSetup {
    fn new() -> Self {
        let env = Env::default();
        env.mock_all_auths();

        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);
        let usdc_admin = Address::generate(&env);
        let usdc_token = env.register_stellar_asset_contract_v2(usdc_admin);
        let usdc = usdc_token.address();
        let usdc_asset = StellarAssetClient::new(&env, &usdc);

        let creator = Address::generate(&env);
        let verifier = Address::generate(&env);
        let success_dest = Address::generate(&env);
        let failure_dest = Address::generate(&env);
        let milestone = BytesN::from_array(&env, &[7u8; 32]);
        let now = 1_700_000_000u64;

        env.ledger().set_timestamp(now);
        usdc_asset.mint(&creator, &MIN_AMOUNT);

        Self {
            env,
            contract_id,
            client,
            usdc,
            creator,
            verifier,
            success_dest,
            failure_dest,
            milestone,
            now,
        }
    }

    fn create_vault(&self) -> u32 {
        self.client.create_vault(
            &self.usdc,
            &self.creator,
            &MIN_AMOUNT,
            &self.now,
            &(self.now + 86_400),
            &self.milestone,
            &Some(self.verifier.clone()),
            &self.success_dest,
            &self.failure_dest,
        )
    }
}

fn assert_lifecycle_event(
    setup: &TestSetup,
    event_name: &str,
    vault_id: u32,
    expected_destination: Option<Address>,
    expected_status: VaultStatus,
) {
    let expected_name = Symbol::new(&setup.env, event_name);
    let all_events = setup.env.events().all();

    for (emitting_contract, topics, data) in all_events {
        if emitting_contract != setup.contract_id {
            continue;
        }

        let actual_name: Symbol = topics.get(0).unwrap().try_into_val(&setup.env).unwrap();
        if actual_name != expected_name {
            continue;
        }

        let actual_vault_id: u32 = topics.get(1).unwrap().try_into_val(&setup.env).unwrap();
        let actual_creator: Address = topics.get(2).unwrap().try_into_val(&setup.env).unwrap();
        let payload: VaultLifecycleEventData = data.try_into_val(&setup.env).unwrap();

        assert_eq!(actual_vault_id, vault_id);
        assert_eq!(actual_creator, setup.creator);
        assert_eq!(payload.amount, MIN_AMOUNT);
        assert_eq!(payload.destination, expected_destination);
        assert_eq!(payload.status, expected_status);
        return;
    }

    panic!("expected {event_name} lifecycle event for vault {vault_id}");
}

#[test]
fn lifecycle_events_use_indexed_topics_and_typed_payloads() {
    let setup = TestSetup::new();

    let vault_id = setup.create_vault();
    assert_lifecycle_event(&setup, "vault_created", vault_id, None, VaultStatus::Active);

    setup.env.ledger().set_timestamp(setup.now + 3_600);
    setup.client.validate_milestone(&vault_id);
    assert_lifecycle_event(
        &setup,
        "milestone_validated",
        vault_id,
        None,
        VaultStatus::Active,
    );

    setup.client.release_funds(&vault_id, &setup.usdc);
    assert_lifecycle_event(
        &setup,
        "funds_released",
        vault_id,
        Some(setup.success_dest.clone()),
        VaultStatus::Completed,
    );
}

#[test]
fn redirect_event_uses_failure_destination_payload() {
    let setup = TestSetup::new();

    let vault_id = setup.create_vault();
    setup.env.ledger().set_timestamp(setup.now + 86_401);

    setup.client.redirect_funds(&vault_id, &setup.usdc);

    assert_lifecycle_event(
        &setup,
        "funds_redirected",
        vault_id,
        Some(setup.failure_dest.clone()),
        VaultStatus::Failed,
    );
}

#[test]
fn cancel_event_uses_creator_refund_payload() {
    let setup = TestSetup::new();

    let vault_id = setup.create_vault();

    setup.client.cancel_vault(&vault_id, &setup.usdc);

    assert_lifecycle_event(
        &setup,
        "vault_cancelled",
        vault_id,
        Some(setup.creator.clone()),
        VaultStatus::Cancelled,
    );
}
