#![cfg(test)]

use soroban_sdk::{
    testutils::{Address as _, AuthorizedFunction, Events, Ledger, MockAuth, MockAuthInvoke},
    token::StellarAssetClient,
    Address, BytesN, Env, IntoVal, Symbol, TryIntoVal,
};

use disciplr_vault::{DisciplrVault, DisciplrVaultClient, Error, MIN_AMOUNT};

struct TestSetup {
    env: Env,
    client: DisciplrVaultClient<'static>,
    usdc: Address,
    admin: Address,
    creator: Address,
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

        let admin = Address::generate(&env);
        let creator = Address::generate(&env);
        let success_dest = Address::generate(&env);
        let failure_dest = Address::generate(&env);
        let milestone = BytesN::from_array(&env, &[9u8; 32]);
        let now = 1_700_000_000u64;

        env.ledger().set_timestamp(now);
        let funded_amount = MIN_AMOUNT * 2;
        usdc_asset.mint(&creator, &funded_amount);

        Self {
            env,
            client,
            usdc,
            admin,
            creator,
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
            &None,
            &self.success_dest,
            &self.failure_dest,
        )
    }

    fn try_create_vault(
        &self,
    ) -> Result<Result<u32, soroban_sdk::ConversionError>, Result<Error, soroban_sdk::InvokeError>>
    {
        self.client.try_create_vault(
            &self.usdc,
            &self.creator,
            &MIN_AMOUNT,
            &self.now,
            &(self.now + 86_400),
            &self.milestone,
            &None,
            &self.success_dest,
            &self.failure_dest,
        )
    }
}

fn assert_pause_event(env: &Env, event_name: &str, admin: &Address, paused: bool) {
    let events = env.events().all();
    let (_, topics, data) = events.last().expect("pause event should be emitted");
    let actual_name: Symbol = topics.get(0).unwrap().try_into_val(env).unwrap();
    let actual_admin: Address = topics.get(1).unwrap().try_into_val(env).unwrap();
    let actual_paused: bool = data.try_into_val(env).unwrap();

    assert_eq!(actual_name, Symbol::new(env, event_name));
    assert_eq!(actual_admin, *admin);
    assert_eq!(actual_paused, paused);
}

#[test]
fn pause_blocks_create_and_unpause_restores_flow() {
    let setup = TestSetup::new();

    assert!(setup.client.initialize(&setup.admin));
    assert!(setup.client.set_paused(&true));
    assert_pause_event(&setup.env, "paused", &setup.admin, true);

    let paused_result = setup.try_create_vault();
    assert!(
        matches!(paused_result, Err(Ok(Error::ContractPaused))),
        "paused create should reject: {:?}",
        paused_result
    );

    assert!(setup.client.set_paused(&false));
    assert_pause_event(&setup.env, "unpaused", &setup.admin, false);
    let vault_id = setup.create_vault();
    assert_eq!(vault_id, 0);
}

#[test]
fn pause_blocks_existing_mutating_entrypoints_but_reads_stay_open() {
    let setup = TestSetup::new();
    let vault_id = setup.create_vault();

    assert!(setup.client.initialize(&setup.admin));
    assert!(setup.client.set_paused(&true));

    assert_eq!(setup.client.vault_count(), 1);
    assert!(setup.client.get_vault_state(&vault_id).is_some());

    let validate_result = setup.client.try_validate_milestone(&vault_id);
    assert!(matches!(validate_result, Err(Ok(Error::ContractPaused))));

    let release_result = setup.client.try_release_funds(&vault_id, &setup.usdc);
    assert!(matches!(release_result, Err(Ok(Error::ContractPaused))));

    setup.env.ledger().set_timestamp(setup.now + 86_401);
    let redirect_result = setup.client.try_redirect_funds(&vault_id, &setup.usdc);
    assert!(matches!(redirect_result, Err(Ok(Error::ContractPaused))));

    let cancel_result = setup.client.try_cancel_vault(&vault_id, &setup.usdc);
    assert!(matches!(cancel_result, Err(Ok(Error::ContractPaused))));
}

#[test]
fn initialize_is_one_time() {
    let setup = TestSetup::new();
    let second_admin = Address::generate(&setup.env);

    assert!(setup.client.initialize(&setup.admin));
    let result = setup.client.try_initialize(&second_admin);

    assert!(
        matches!(result, Err(Ok(Error::AlreadyInitialized))),
        "second initialize should reject: {:?}",
        result
    );
}

#[test]
fn set_paused_requires_initialization() {
    let setup = TestSetup::new();

    let result = setup.client.try_set_paused(&true);

    assert!(
        matches!(result, Err(Ok(Error::NotInitialized))),
        "set_paused before initialize should reject: {:?}",
        result
    );
}

#[test]
#[should_panic]
fn non_admin_auth_cannot_pause() {
    let env = Env::default();
    let contract_id = env.register(DisciplrVault, ());
    let client = DisciplrVaultClient::new(&env, &contract_id);
    let admin = Address::generate(&env);
    let attacker = Address::generate(&env);

    env.mock_auths(&[MockAuth {
        address: &admin,
        invoke: &MockAuthInvoke {
            contract: &contract_id,
            fn_name: "initialize",
            args: (admin.clone(),).into_val(&env),
            sub_invokes: &[],
        },
    }]);
    client.initialize(&admin);

    env.mock_auths(&[MockAuth {
        address: &attacker,
        invoke: &MockAuthInvoke {
            contract: &contract_id,
            fn_name: "set_paused",
            args: (true,).into_val(&env),
            sub_invokes: &[],
        },
    }]);

    client.set_paused(&true);

    let auths = env.auths();
    assert!(auths.iter().any(|(address, invocation)| {
        *address == attacker
            && matches!(
                &invocation.function,
                AuthorizedFunction::Contract((contract, function_name, _))
                    if *contract == contract_id
                        && *function_name == Symbol::new(&env, "set_paused")
            )
    }));
}
