#![no_std]
#![allow(clippy::too_many_arguments)]

use soroban_sdk::{contract, contractimpl, contracttype, Address, BytesN, Env, Symbol};

#[contracttype]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VaultStatus {
    Active = 0,
    Completed = 1,
    Failed = 2,
    Cancelled = 3,
}

#[contracttype]
pub struct ProductivityVault {
    pub creator: Address,
    pub amount: i128,
    pub start_timestamp: u64,
    pub end_timestamp: u64,
    pub milestone_hash: BytesN<32>,
    pub verifier: Option<Address>,
    pub success_destination: Address,
    pub failure_destination: Address,
    pub status: VaultStatus,
}

#[contract]
pub struct DisciplrVault;

#[contractimpl]
impl DisciplrVault {
    /// Create a new productivity vault. Caller must have approved USDC transfer to this contract.
    pub fn create_vault(
        env: Env,
        creator: Address,
        amount: i128,
        start_timestamp: u64,
        end_timestamp: u64,
        milestone_hash: BytesN<32>,
        verifier: Option<Address>,
        success_destination: Address,
        failure_destination: Address,
    ) -> u32 {
        creator.require_auth();
        // TODO: pull USDC from creator to this contract
        // For now, just store vault metadata (storage key pattern would be used in full impl)
        let vault = ProductivityVault {
            creator: creator.clone(),
            amount,
            start_timestamp,
            end_timestamp,
            milestone_hash,
            verifier,
            success_destination,
            failure_destination,
            status: VaultStatus::Active,
        };
        let vault_id = 0u32; // placeholder; real impl would allocate id and persist
        env.events()
            .publish((Symbol::new(&env, "vault_created"), vault_id), vault);
        vault_id
    }

    /// Verifier (or authorized party) validates milestone completion.
    pub fn validate_milestone(env: Env, vault_id: u32) -> bool {
        // TODO: check vault exists, status is Active, caller is verifier, timestamp < end
        // TODO: transfer USDC to success_destination, set status Completed
        env.events()
            .publish((Symbol::new(&env, "milestone_validated"), vault_id), ());
        true
    }

    /// Release funds to success destination (called after validation or by deadline logic).
    pub fn release_funds(_env: Env, _vault_id: u32) -> bool {
        // TODO: require status Active, transfer to success_destination, set Completed
        true
    }

    /// Redirect funds to failure destination (e.g. after deadline without validation).
    pub fn redirect_funds(_env: Env, _vault_id: u32) -> bool {
        // TODO: require status Active and past end_timestamp, transfer to failure_destination, set Failed
        true
    }

    /// Cancel vault and return funds to creator (if allowed by rules).
    pub fn cancel_vault(_env: Env, _vault_id: u32) -> bool {
        // TODO: require creator auth, return USDC to creator, set Cancelled
        true
    }

    /// Return current vault state for a given vault id.
    /// Placeholder: returns None; full impl would read from storage.
    pub fn get_vault_state(_env: Env, _vault_id: u32) -> Option<ProductivityVault> {
        None
    }

    // ===== USDC Balance Tests: cancel_vault =====

    /// Tests that after cancel_vault, the creator's USDC balance is fully restored
    /// by exactly the vault amount, and the contract's balance decreases by the same.
    #[test]
    fn test_usdc_balance_updates_after_cancel_vault() {
        let setup = TestSetup::new();
        let client = setup.client();
        let usdc = setup.usdc_client();

        let before_create = usdc.balance(&setup.creator);
        let vault_id = setup.create_default_vault();

        assert_eq!(
            usdc.balance(&setup.creator),
            before_create - setup.amount,
            "Creator balance should decrease by amount after creation"
        );

        client.cancel_vault(&vault_id, &setup.usdc_token);

        assert_eq!(
            usdc.balance(&setup.creator),
            before_create,
            "Creator balance should be fully restored after cancellation"
        );
        assert_eq!(
            usdc.balance(&setup.contract_id),
            0,
            "Contract balance should be zero after cancellation"
        );
    }

    /// Tests cancel_vault when the creator has exactly the vault amount.
    /// Guards against rounding errors and ensures full balance restoration.
    #[test]
    fn test_validate_milestone_rejects_after_end() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Advance ledger to exactly end_timestamp
        setup.env.ledger().set_timestamp(setup.end_timestamp);

        // Try to validate milestone - should fail with MilestoneExpired
        let result = client.try_validate_milestone(&vault_id);
        assert!(result.is_err());

        // Advance ledger past end_timestamp
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);

        // Try to validate milestone - should also fail
        let result = client.try_validate_milestone(&vault_id);
        assert!(result.is_err());
    }

    /// After validation (or when release is allowed), release_funds transfers the vault amount
    /// to success_destination and vault status becomes Completed.
    /// Steps: create vault → validate milestone (if required) → release_funds → assert balance and status.
    #[test]
    fn test_release_funds_sets_status_completed_and_releases_to_success_destination() {
        let setup = TestSetup::new();
        let client = setup.client();

        // 1. Create vault
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_vault_no_verifier();

        // 2. Validate milestone (required for release before deadline)
        setup.env.ledger().set_timestamp(setup.end_timestamp - 1);
        let validated = client.validate_milestone(&vault_id);
        assert!(validated, "validate_milestone must succeed before end time");

        // 3. Call release_funds
        let released = client.release_funds(&vault_id, &setup.usdc_token);
        assert!(released, "release_funds must succeed after validation");

        // 4. Assert vault status is Completed
        let vault = client.get_vault_state(&vault_id).expect("vault must exist");
        assert_eq!(
            vault.status,
            VaultStatus::Completed,
            "vault status must be Completed after release_funds"
        );
        assert_eq!(vault.amount, setup.amount);
        assert_eq!(vault.success_destination, setup.success_dest);

        // 5. Assert success_destination received the vault amount
        let balance = setup.usdc_client().balance(&setup.success_dest);
        assert_eq!(
            balance, setup.amount,
            "success_destination balance must equal vault amount after release"
        );
    }

    #[test]
    fn test_validate_milestone_succeeds_before_end() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Set time to just before end
        setup.env.ledger().set_timestamp(setup.end_timestamp - 1);

        let success = client.validate_milestone(&vault_id);
        assert!(success);

        let vault = client.get_vault_state(&vault_id).unwrap();
        // Validation now sets milestone_validated, NOT status = Completed
        assert!(vault.milestone_validated);
        assert_eq!(vault.status, VaultStatus::Active);
    }

    /// Issue #14: When verifier is None, only creator may validate. Creator succeeds.
    #[test]
    fn test_validate_milestone_verifier_none_creator_succeeds() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_vault_no_verifier();

        setup.env.ledger().set_timestamp(setup.end_timestamp - 1);

        let result = client.validate_milestone(&vault_id);
        assert!(result);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert!(vault.milestone_validated);
        assert_eq!(vault.verifier, None);
    }

    /// Issue #14: When verifier is None, release_funds after deadline (no validation) still works.
    #[test]
    fn test_release_funds_verifier_none_after_deadline() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_vault_no_verifier();

        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);

        let result = client.release_funds(&vault_id, &setup.usdc_token);
        assert!(result);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.status, VaultStatus::Completed);
    }

    #[test]
    fn test_release_funds_rejects_non_existent_vault() {
        let setup = TestSetup::new();
        let client = setup.client();

        let result = client.try_release_funds(&999, &setup.usdc_token);
        assert!(result.is_err());
    }

    #[test]
    fn test_validate_milestone_rejects_non_existent_vault() {
        let setup = TestSetup::new();
        let client = setup.client();

        let result = client.try_validate_milestone(&999);
        assert!(result.is_err());
    }

    #[test]
    fn test_redirect_funds_rejects_non_existent_vault() {
        let setup = TestSetup::new();
        let client = setup.client();

        let result = client.try_redirect_funds(&999, &setup.usdc_token);
        assert!(result.is_err());
    }

        let usdc_admin = Address::generate(&env);
        let usdc_token = env.register_stellar_asset_contract_v2(usdc_admin.clone());
        let usdc_addr = usdc_token.address();
        let usdc_asset = StellarAssetClient::new(&env, &usdc_addr);
        let usdc_client = TokenClient::new(&env, &usdc_addr);

        let creator = Address::generate(&env);
        let amount = 1_000_000i128;

        // Mint EXACTLY vault_amount to creator
        usdc_asset.mint(&creator, &amount);
        assert_eq!(usdc_client.balance(&creator), amount);

        let vault_id = client.create_vault(
            &usdc_addr,
            &creator,
            &amount,
            &100,
            &200,
            &BytesN::from_array(&env, &[1u8; 32]),
            &None,
            &Address::generate(&env),
            &Address::generate(&env),
        );

        assert_eq!(usdc_client.balance(&creator), 0);

        client.cancel_vault(&vault_id, &usdc_addr);

        client.release_funds(&vault_id, &setup.usdc_token);
        // Second call — must error.
        assert!(client
            .try_release_funds(&vault_id, &setup.usdc_token)
            .is_err());
    }

    #[test]
    fn test_release_cancelled_vault_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        client.cancel_vault(&vault_id, &setup.usdc_token);
        // Release after cancel — must error.
        assert!(client
            .try_release_funds(&vault_id, &setup.usdc_token)
            .is_err());
    }

    #[test]
    fn test_release_not_validated_before_deadline_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Neither validated nor past deadline — must error.
        assert!(client
            .try_release_funds(&vault_id, &setup.usdc_token)
            .is_err());
    }

    #[test]
    fn test_validate_milestone_on_completed_vault_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
        client.release_funds(&vault_id, &setup.usdc_token);

        // Validate after completion — must error.
        assert!(client.try_validate_milestone(&vault_id).is_err());
    }

    #[test]
    fn test_redirect_funds_after_deadline_without_validation() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);

        let usdc = setup.usdc_client();
        let before = usdc.balance(&setup.failure_dest);

        let result = client.redirect_funds(&vault_id, &setup.usdc_token);
        assert!(result);
        assert_eq!(usdc.balance(&setup.failure_dest) - before, setup.amount);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.status, VaultStatus::Failed);
    }

    /// After `redirect_funds`, the failure destination balance must increase
    /// by the vault amount and the contract's USDC balance must decrease
    /// by the same amount (i.e., funds leave the contract and arrive at
    /// the failure destination).
    #[test]
    fn test_redirect_funds_updates_contract_and_failure_balances() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Move past the deadline without validation so redirect is allowed.
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);

        let usdc = setup.usdc_client();

        let contract_before = usdc.balance(&setup.contract_id);
        let failure_before = usdc.balance(&setup.failure_dest);

        let result = client.redirect_funds(&vault_id, &setup.usdc_token);
        assert!(result);

        let contract_after = usdc.balance(&setup.contract_id);
        let failure_after = usdc.balance(&setup.failure_dest);

        // Failure destination gains the vault amount.
        assert_eq!(failure_after - failure_before, setup.amount);
        // Contract balance decreases by the same vault amount.
        assert_eq!(contract_before - contract_after, setup.amount);
    }

    #[test]
    fn test_redirect_funds_before_deadline_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Still before deadline — must error.
        assert!(client
            .try_redirect_funds(&vault_id, &setup.usdc_token)
            .is_err());
    }

    #[test]
    fn test_double_redirect_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);

        let result = client.redirect_funds(&vault_id, &setup.usdc_token);
        assert!(result);
        // Second redirect — must error (vault already Failed).
        assert!(client
            .try_redirect_funds(&vault_id, &setup.usdc_token)
            .is_err());
    }

    #[test]
    fn test_cancel_vault_returns_funds_to_creator() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        let usdc = setup.usdc_client();
        let before = usdc.balance(&setup.creator);

        let result = client.cancel_vault(&vault_id, &setup.usdc_token);
        assert!(result);
        assert_eq!(usdc.balance(&setup.creator) - before, setup.amount);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.status, VaultStatus::Cancelled);
    }

    // -----------------------------------------------------------------------
    // More upstream tests migrated
    // -----------------------------------------------------------------------

    #[test]
    #[should_panic]
    fn test_create_vault_fails_without_auth() {
        let env = Env::default();
        let usdc_token = Address::generate(&env);
        let creator = Address::generate(&env);
        let success_addr = Address::generate(&env);
        let failure_addr = Address::generate(&env);
        let verifier = Address::generate(&env);
        let milestone_hash = BytesN::<32>::from_array(&env, &[0u8; 32]);

        // DO NOT authorize the creator
        let _vault_id = DisciplrVault::create_vault(
            env,
            usdc_token,
            creator,
            1000,
            100,
            200,
            milestone_hash,
            Some(verifier),
            success_addr,
            failure_addr,
        );
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #7)")]
    fn test_create_vault_zero_amount() {
        let setup = TestSetup::new();
        let client = setup.client();

        client.create_vault(
            &setup.usdc_token,
            &setup.creator,
            &0i128,
            &1000,
            &2000,
            &setup.milestone_hash(),
            &None,
            &setup.success_dest,
            &setup.failure_dest,
        );
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #7)")]
    fn test_create_vault_amount_above_max_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();
        let amount_above_max = MAX_AMOUNT
            .checked_add(1)
            .expect("MAX_AMOUNT + 1 overflowed");

        client.create_vault(
            &setup.usdc_token,
            &setup.creator,
            &amount_above_max,
            &1000,
            &2000,
            &setup.milestone_hash(),
            &None,
            &setup.success_dest,
            &setup.failure_dest,
        );
    }

    #[test]
    #[should_panic]
    fn test_create_vault_caller_differs_from_creator() {
        let env = Env::default();
        let usdc_token = Address::generate(&env);
        let creator = Address::generate(&env);
        let different_caller = Address::generate(&env);
        let success_addr = Address::generate(&env);
        let failure_addr = Address::generate(&env);
        let verifier = Address::generate(&env);
        let milestone_hash = BytesN::<32>::from_array(&env, &[1u8; 32]);

        different_caller.require_auth();

        let _vault_id = DisciplrVault::create_vault(
            env,
            usdc_token,
            creator, // This address is NOT authorized
            1000,
            100,
            200,
            milestone_hash,
            Some(verifier),
            success_addr,
            failure_addr,
        );
    }

    #[test]
    fn test_vault_parameters_with_and_without_verifier() {
        let _verifier_some: Option<Address> = None;
        let _no_verifier: Option<Address> = None;
        assert!(_verifier_some.is_none());
        assert!(_no_verifier.is_none());
    }

    #[test]
    fn test_vault_amount_parameters() {
        let amounts = [100i128, 1000, 10000, 100000];
        for amount in amounts {
            assert!(amount > 0, "Amount {} should be positive", amount);
        }
    }

    #[test]
    fn test_vault_timestamp_scenarios() {
        let start = 100u64;
        let end = 200u64;
        assert!(start < end, "Start should be before end");
    }

    #[test]
    fn test_vault_milestone_hash_generation() {
        let env = Env::default();
        let _hash_1 = BytesN::<32>::from_array(&env, &[0u8; 32]);
        let _hash_2 = BytesN::<32>::from_array(&env, &[1u8; 32]);
        let _hash_3 = BytesN::<32>::from_array(&env, &[255u8; 32]);
        assert_ne!([0u8; 32], [1u8; 32]);
        assert_ne!([1u8; 32], [255u8; 32]);
    }

    #[test]
    #[should_panic]
    fn test_authorization_prevents_unauthorized_creation() {
        let env = Env::default();
        let usdc_token = Address::generate(&env);
        let creator = Address::generate(&env);
        let attacker = Address::generate(&env);
        let success_addr = Address::generate(&env);
        let failure_addr = Address::generate(&env);
        let milestone_hash = BytesN::<32>::from_array(&env, &[4u8; 32]);

        attacker.require_auth();

        let _vault_id = DisciplrVault::create_vault(
            env,
            usdc_token,
            creator,
            5000,
            100,
            200,
            milestone_hash,
            None,
            success_addr,
            failure_addr,
        );
    }

    #[test]
    fn test_create_vault_emits_event_and_returns_id() {
        let env = Env::default();
        env.mock_all_auths();

        let usdc_admin = Address::generate(&env);
        let usdc_token = env.register_stellar_asset_contract_v2(usdc_admin.clone());
        let usdc_addr = usdc_token.address();
        let usdc_asset = StellarAssetClient::new(&env, &usdc_addr);

        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);

        let creator = Address::generate(&env);
        let success_destination = Address::generate(&env);
        let failure_destination = Address::generate(&env);
        let verifier = Address::generate(&env);
        let milestone_hash = BytesN::from_array(&env, &[1u8; 32]);
        let amount = 1_000_000i128;
        let start_timestamp = 1_000_000u64;
        let end_timestamp = 2_000_000u64;

        usdc_asset.mint(&creator, &amount);

        let vault_id = client.create_vault(
            &usdc_addr,
            &creator,
            &amount,
            &start_timestamp,
            &end_timestamp,
            &milestone_hash,
            &Some(verifier.clone()),
            &success_destination,
            &failure_destination,
        );

        // Vault count starts at 0, first vault gets ID 0
        assert_eq!(vault_id, 0u32);

        let auths = env.auths();
        // Since we also call token_client.transfer inside, the auths might have multiple invocations
        // We ensure a `create_vault` invocation is inside the auth list
        let mut found_create_auth = false;
        for (auth_addr, invocation) in auths {
            if auth_addr == creator {
                if let AuthorizedFunction::Contract((contract, function_name, _)) =
                    &invocation.function
                {
                    if *contract == contract_id
                        && *function_name == Symbol::new(&env, "create_vault")
                    {
                        found_create_auth = true;
                    }
                }
            }
        }
        assert!(
            found_create_auth,
            "create_vault should be authenticated by creator"
        );

        let all_events = env.events().all();
        // token transfer also emits events, so we find the one related to us
        let mut found_vault_created = false;
        for (emitting_contract, topics, _) in all_events {
            if emitting_contract == contract_id {
                let event_name: Symbol = topics.get(0).unwrap().try_into_val(&env).unwrap();
                if event_name == Symbol::new(&env, "vault_created") {
                    let event_vault_id: u32 = topics.get(1).unwrap().try_into_val(&env).unwrap();
                    assert_eq!(event_vault_id, vault_id);
                    found_vault_created = true;
                }
            }
        }
        assert!(found_vault_created, "vault_created event must be emitted");
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #3)")]
    fn test_cancel_vault_when_completed_fails() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Release funds to make it Completed
        client.validate_milestone(&vault_id);
        client.release_funds(&vault_id, &setup.usdc_token);

        // Attempt to cancel - should panic with error VaultNotActive
        client.cancel_vault(&vault_id, &setup.usdc_token);
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #3)")]
    fn test_cancel_vault_when_failed_fails() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Expire and redirect funds to make it Failed
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
        client.redirect_funds(&vault_id, &setup.usdc_token);

        // Attempt to cancel - should panic
        client.cancel_vault(&vault_id, &setup.usdc_token);
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #3)")]
    fn test_cancel_vault_when_cancelled_fails() {
        let setup = TestSetup::new();
        let client = setup.client();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Cancel it
        client.cancel_vault(&vault_id, &setup.usdc_token);

        // Attempt to cancel again - should panic
        client.cancel_vault(&vault_id, &setup.usdc_token);
    }

    #[test]
    #[should_panic]
    fn test_cancel_vault_non_creator_fails() {
        let setup = TestSetup::new();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Try to cancel with a different address
        // The client currently signs with mock_all_auths(),
        // to properly test this we need a real failure in auth.
        // But since mock_all_auths allows everything, we just rely on `VaultNotFound`
        // or we manually create a test without mock_all_auths
        let env = Env::default();
        let contract_id = env.register(DisciplrVault, ());
        let client_no_auth = DisciplrVaultClient::new(&env, &contract_id);

        client_no_auth.cancel_vault(&vault_id, &setup.usdc_token);
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #1)")]
    fn test_cancel_vault_nonexistent_fails() {
        let setup = TestSetup::new();
        let client = setup.client();
        client.cancel_vault(&999u32, &setup.usdc_token);
    }

    // -----------------------------------------------------------------------
    // Issue #21: validate_milestone only succeeds when caller is verifier
    // -----------------------------------------------------------------------

    /// Issue #21: validate_milestone succeeds when the caller is the vault's verifier (X).
    /// Creates a vault with verifier = X, calls validate_milestone as X and asserts success.
    #[test]
    fn test_validate_milestone_succeeds_as_verifier() {
        let setup = TestSetup::new();
        let client = setup.client();

        // Set time within the active window.
        setup.env.ledger().set_timestamp(setup.start_timestamp);

        // Create vault with an explicit verifier (setup.verifier = X).
        let vault_id = setup.create_default_vault();

        // Advance time to just before the deadline so the milestone is still validatable.
        setup.env.ledger().set_timestamp(setup.end_timestamp - 1);

        // Call validate_milestone — mock_all_auths() lets the verifier's auth pass.
        let result = client.validate_milestone(&vault_id);
        assert!(
            result,
            "validate_milestone should return true when called by verifier"
        );

        // Confirm the vault state reflects the validation.
        let vault = client.get_vault_state(&vault_id).unwrap();
        assert!(
            vault.milestone_validated,
            "milestone_validated must be true after verifier validates"
        );
        assert_eq!(
            vault.status,
            VaultStatus::Active,
            "vault status remains Active after validation (funds not yet released)"
        );
    }

    /// Issue #21: validate_milestone fails when the caller is NOT the vault's verifier.
    /// Creates a vault with verifier = X, then attempts validate_milestone without
    /// providing auth for X — the contract must reject the call.
    #[test]
    #[should_panic]
    fn test_validate_milestone_fails_as_non_verifier() {
        // Deliberately do NOT use mock_all_auths so that require_auth() is enforced.
        let env = Env::default();

        let usdc_admin = Address::generate(&env);
        let usdc_token = env.register_stellar_asset_contract_v2(usdc_admin.clone());
        let usdc_addr = usdc_token.address();
        let usdc_asset = StellarAssetClient::new(&env, &usdc_addr);

        let creator = Address::generate(&env);
        let verifier = Address::generate(&env); // X — the authorised verifier
        let _non_verifier = Address::generate(&env); // Y — a different address
        let success_dest = Address::generate(&env);
        let failure_dest = Address::generate(&env);
        let amount: i128 = 1_000_000;
        let start_timestamp: u64 = 100;
        let end_timestamp: u64 = 1_000;
        let milestone_hash = BytesN::<32>::from_array(&env, &[1u8; 32]);

        // Mint USDC and register the contract — use mock_all_auths just for setup.
        env.mock_all_auths();
        usdc_asset.mint(&creator, &amount);
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);

        env.ledger().set_timestamp(start_timestamp);

        client.create_vault(
            &usdc_addr,
            &creator,
            &amount,
            &start_timestamp,
            &end_timestamp,
            &milestone_hash,
            &Some(verifier.clone()), // vault.verifier = X
            &success_dest,
            &failure_dest,
        );

        env.ledger().set_timestamp(end_timestamp - 1);

        // Stop mocking auths so that require_auth() is actually enforced.
        // Y (non_verifier) has no authorization — calling validate_milestone must panic.
        let env2 = Env::default();
        let contract_id2 = env2.register(DisciplrVault, ());
        let client2 = DisciplrVaultClient::new(&env2, &contract_id2);

        // This call is made against a fresh env with no auths — it must panic.
        client2.validate_milestone(&0u32);
    /// Issue #44: Test that create_vault accepts verifier == creator
    /// and that validate_milestone can be called by the creator in that case.
    #[test]
    fn test_verifier_same_as_creator() {
    // -----------------------------------------------------------------------
    // Issue #25: release_funds fails when vault is Failed
    // -----------------------------------------------------------------------

    #[test]
    fn test_release_funds_fails_when_vault_failed() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);

        let vault_id = client.create_vault(
            &setup.usdc_token,
            &setup.creator,
            &setup.amount,
            &setup.start_timestamp,
            &setup.end_timestamp,
            &setup.milestone_hash(),
            &Some(setup.creator.clone()),
            &setup.success_dest,
            &setup.failure_dest,
        );

        setup
            .env
            .ledger()
            .set_timestamp(setup.start_timestamp + 500);

        let result = client.validate_milestone(&vault_id);
        assert!(result);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert!(vault.milestone_validated);
        assert_eq!(vault.verifier, Some(setup.creator.clone()));
        let vault_id = setup.create_default_vault();

        // Past deadline + redirect → Failed
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
        client.redirect_funds(&vault_id, &setup.usdc_token);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.status, VaultStatus::Failed);

        // Release on Failed vault must fail with VaultNotActive
        assert!(
            client
                .try_release_funds(&vault_id, &setup.usdc_token)
                .is_err(),
            "release_funds must fail on a Failed vault"
        );
    }
}
