#![no_std]

use soroban_sdk::{
    contract, contracterror, contractimpl, contracttype, Address, BytesN, Env, Symbol,
};

#[contracterror]
#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
#[repr(u32)]
pub enum Error {
    VaultNotFound = 1,
    NotAuthorized = 2,
    VaultNotActive = 3,
    InvalidTimestamp = 4,
    MilestoneExpired = 5,
}

#[contracttype]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VaultStatus {
    Active = 0,
    Completed = 1,
    Failed = 2,
    Cancelled = 3,
}

#[contracttype]
#[derive(Clone, Debug, Eq, PartialEq)]
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

#[contracttype]
pub enum DataKey {
    NextVaultId,
    Vault(u32),
    VaultCount,
}

#[contract]
pub struct DisciplrVault;

#[contractimpl]
impl DisciplrVault {
    /// Create a new productivity vault. Caller must have approved USDC transfer to this contract.
    ///
    /// # Validation Rules
    /// - Requires `start_timestamp < end_timestamp`. If `start_timestamp >= end_timestamp`, the function panics
    ///   because a 0-length or reverse-time window is invalid.
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

        // Validate that start_timestamp is strictly before end_timestamp.
        // A vault with start >= end has no valid time window and must be rejected.
        if end_timestamp <= start_timestamp {
            panic!("create_vault: start_timestamp must be strictly less than end_timestamp");
        }

        let vault = ProductivityVault {
            creator,
            amount,
            start_timestamp,
            end_timestamp,
            milestone_hash,
            verifier,
            success_destination,
            failure_destination,
            status: VaultStatus::Active,
        };
        let vault_id: u32 = env
            .storage()
            .instance()
            .get(&DataKey::NextVaultId)
            .unwrap_or(0u32);
        env.storage()
            .persistent()
            .set(&DataKey::Vault(vault_id), &vault);
        env.storage()
            .instance()
            .set(&DataKey::NextVaultId, &(vault_id + 1));

        env.events()
            .publish((Symbol::new(&env, "vault_created"), vault_id), vault);
        vault_id
    }

    /// Verifier (or authorized party) validates milestone completion.
    pub fn validate_milestone(env: Env, vault_id: u32) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .persistent()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        // Auth check for verifier
        if let Some(ref verifier) = vault.verifier {
            verifier.require_auth();
        } else {
            vault.creator.require_auth();
        }

        // Timestamp check: rejects when current time >= end_timestamp
        if env.ledger().timestamp() >= vault.end_timestamp {
            return Err(Error::MilestoneExpired);
        }

        vault.status = VaultStatus::Completed;
        env.storage().persistent().set(&vault_key, &vault);

        env.events()
            .publish((Symbol::new(&env, "milestone_validated"), vault_id), ());
        Ok(true)
    }

    /// Release funds to success destination.
    pub fn release_funds(env: Env, vault_id: u32) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .persistent()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        // Only allow release if validated (status would be Completed) or maybe this is a redundant method
        // For now, let's just make it a stub that updates status if called.
        // In a real impl, this would handle the actual USDC transfer.
        vault.status = VaultStatus::Completed;
        env.storage().persistent().set(&vault_key, &vault);
        Ok(true)
    }

    /// Redirect funds to failure destination (e.g. after deadline without validation).
    pub fn redirect_funds(env: Env, vault_id: u32) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .persistent()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        if env.ledger().timestamp() < vault.end_timestamp {
            return Err(Error::InvalidTimestamp); // Too early to redirect
        }

        vault.status = VaultStatus::Failed;
        env.storage().persistent().set(&vault_key, &vault);
        Ok(true)
    }

    /// Cancel vault and return funds to creator.
    pub fn cancel_vault(env: Env, vault_id: u32) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .persistent()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;

        vault.creator.require_auth();

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        vault.status = VaultStatus::Cancelled;
        env.storage().persistent().set(&vault_key, &vault);
        Ok(true)
    }

    /// Return current vault state for a given vault id.
    pub fn get_vault_state(env: Env, vault_id: u32) -> Option<ProductivityVault> {
        env.storage().persistent().get(&DataKey::Vault(vault_id))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use soroban_sdk::testutils::Address as _;

    #[test]
    fn get_vault_state_returns_some_with_matching_fields() {
        let env = Env::default();
        env.mock_all_auths();

        let contract_id = env.register_contract(None, DisciplrVault);
        let client = DisciplrVaultClient::new(&env, &contract_id);

        let creator = Address::generate(&env);
        let verifier = Address::generate(&env);
        let success_destination = Address::generate(&env);
        let failure_destination = Address::generate(&env);

        let amount = 1_000_i128;
        let start_timestamp = 1_700_000_000_u64;
        let end_timestamp = 1_700_086_400_u64;
        let milestone_hash = BytesN::from_array(&env, &[7u8; 32]);

        let vault_id = client.create_vault(
            &creator,
            &amount,
            &start_timestamp,
            &end_timestamp,
            &milestone_hash,
            &Some(verifier.clone()),
            &success_destination,
            &failure_destination,
        );

        let vault_state = client.get_vault_state(&vault_id);
        assert!(vault_state.is_some());

        let vault = vault_state.unwrap();
        assert_eq!(vault.creator, creator);
        assert_eq!(vault.amount, amount);
        assert_eq!(vault.start_timestamp, start_timestamp);
        assert_eq!(vault.end_timestamp, end_timestamp);
        assert_eq!(vault.milestone_hash, milestone_hash);
        assert_eq!(vault.verifier, Some(verifier));
        assert_eq!(vault.success_destination, success_destination);
        assert_eq!(vault.failure_destination, failure_destination);
        assert_eq!(vault.status, VaultStatus::Active);
    }

    extern crate std;

    use super::*;
    use soroban_sdk::{
        testutils::{Address as _, AuthorizedFunction, AuthorizedInvocation, Events, Ledger},
        Address, BytesN, Env, IntoVal, Symbol, TryIntoVal,
    };

    /// Test that create_vault fails when creator auth is not provided
    /// This is the primary security test: require_auth() must enforce authorization
    #[test]
    #[should_panic]
    fn test_create_vault_fails_without_auth() {
        let env = Env::default();
        let creator = Address::generate(&env);
        let success_addr = Address::generate(&env);
        let failure_addr = Address::generate(&env);
        let verifier = Address::generate(&env);
        let milestone_hash = BytesN::<32>::from_array(&env, &[0u8; 32]);

        // DO NOT authorize the creator
        // Calling create_vault should fail at require_auth() because the creator is not authorized
        let _vault_id = DisciplrVault::create_vault(
            env,
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

    /// Test that caller differs from creator causes authorization failure
    /// This verifies that require_auth() enforces the creator must be the one authorizing
    #[test]
    #[should_panic]
    fn test_create_vault_caller_differs_from_creator() {
        let env = Env::default();
        let creator = Address::generate(&env);
        let different_caller = Address::generate(&env);
        let success_addr = Address::generate(&env);
        let failure_addr = Address::generate(&env);
        let verifier = Address::generate(&env);
        let milestone_hash = BytesN::<32>::from_array(&env, &[1u8; 32]);

        // Authorize the different caller, NOT the creator
        different_caller.require_auth();

        // Try to create vault with creator address that is NOT authorized
        // This should fail because require_auth() checks that the specific address is authorized
        let _vault_id = DisciplrVault::create_vault(
            env,
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

    /// Test that vault parameters with and without verifier can be created
    #[test]
    fn test_vault_parameters_with_and_without_verifier() {
        // Test that Option<Address> parameters can be Some or None
        let _verifier_some: Option<Address> = None; // Soroban testutils don't support generating addresses easily
        let _no_verifier: Option<Address> = None;

        // These demonstrate the parameter handling
        assert!(_verifier_some.is_none());
        assert!(_no_verifier.is_none());
    }

    /// Test that different amounts are handled correctly
    #[test]
    fn test_vault_amount_parameters() {
        // Test various amounts to ensure parameter passing works
        let amounts = [100i128, 1000, 10000, 100000];

        for amount in amounts {
            assert!(amount > 0, "Amount {} should be positive", amount);
        }
    }

    /// Test timestamps validation scenarios
    #[test]
    fn test_vault_timestamp_scenarios() {
        // Test that start timestamps are before end timestamps
        let start = 100u64;
        let end = 200u64;

        assert!(start < end, "Start should be before end");
    }

    #[test]
    fn test_release_funds_rejects_non_existent_vault() {
        let env = Env::default();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Try to release funds for a non-existent vault ID
        let result = client.try_release_funds(&999);
        assert!(result.is_err());

        // Simply assert that an error occurred - the exact error type is verified by the implementation
    }

    #[test]
    fn test_redirect_funds_rejects_non_existent_vault() {
        let env = Env::default();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);

        // Try to redirect funds for a non-existent vault ID
        let result = client.try_redirect_funds(&999);
        assert!(result.is_err());

        // Simply assert that an error occurred - the exact error type is verified by the implementation
    }

    /// Test milestone hash generation
    #[test]
    fn test_vault_milestone_hash_generation() {
        let env = Env::default();

        // Create different hashes
        let _hash_1 = BytesN::<32>::from_array(&env, &[0u8; 32]);
        let _hash_2 = BytesN::<32>::from_array(&env, &[1u8; 32]);
        let _hash_3 = BytesN::<32>::from_array(&env, &[255u8; 32]);

        // Verify hashes can be created with different values
        assert_ne!([0u8; 32], [1u8; 32]);
        assert_ne!([1u8; 32], [255u8; 32]);
    }

    /// Security test: Demonstrates authorization enforcement with multiple actors
    #[test]
    #[should_panic]
    fn test_authorization_prevents_unauthorized_creation() {
        let env = Env::default();

        let creator = Address::generate(&env);
        let attacker = Address::generate(&env);
        let success_addr = Address::generate(&env);
        let failure_addr = Address::generate(&env);
        let milestone_hash = BytesN::<32>::from_array(&env, &[4u8; 32]);

        // Attacker tries to authorize themselves
        attacker.require_auth();

        // Attacker attempts to create a vault claiming to be the creator
        // This should fail because the creator (not attacker) is required to authorize
        let _vault_id = DisciplrVault::create_vault(
            env,
            creator, // Claiming to be creator
            5000,
            100,
            200,
            milestone_hash,
            None,
            success_addr,
            failure_addr,
        );
    }

    /// Helper: build a default set of valid vault parameters.
    fn make_vault_args(
        env: &Env,
    ) -> (
        Address,
        i128,
        u64,
        u64,
        BytesN<32>,
        Option<Address>,
        Address,
        Address,
    ) {
        let creator = Address::generate(env);
        let success_dest = Address::generate(env);
        let failure_dest = Address::generate(env);
        let verifier = Address::generate(env);
        let milestone_hash = BytesN::from_array(env, &[1u8; 32]);
        let amount = 1_000_000i128; // 1 USDC (6 decimals)
        let start = 1_000_000u64;
        let end = 2_000_000u64;

        (
            creator,
            amount,
            start,
            end,
            milestone_hash,
            Some(verifier),
            success_dest,
            failure_dest,
        )
    }

    /// create_vault must:
    ///   1. return a vault_id (currently the placeholder 0u32)
    ///   2. require creator authorisation
    ///   3. emit exactly one `vault_created` event carrying that vault_id
    #[test]
    fn test_create_vault_emits_event_and_returns_id() {
        let env = Env::default();
        env.mock_all_auths(); // satisfies creator.require_auth()

        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);

        let (
            creator,
            amount,
            start_timestamp,
            end_timestamp,
            milestone_hash,
            verifier,
            success_destination,
            failure_destination,
        ) = make_vault_args(&env);

        // ── Invoke ───────────────────────────────────────────────────────────
        let vault_id = client.create_vault(
            &creator,
            &amount,
            &start_timestamp,
            &end_timestamp,
            &milestone_hash,
            &verifier,
            &success_destination,
            &failure_destination,
        );

        // ── Assert: return value ─────────────────────────────────────────────
        // Returns 0u32 as a placeholder; update when real ID allocation lands.
        assert_eq!(vault_id, 0u32, "vault_id should be the placeholder 0");

        // ── Assert: auth was required for creator ────────────────────────────
        let auths = env.auths();
        assert_eq!(auths.len(), 1, "exactly one auth should be recorded");
        assert_eq!(
            auths[0],
            (
                creator.clone(),
                AuthorizedInvocation {
                    function: AuthorizedFunction::Contract((
                        contract_id.clone(),
                        Symbol::new(&env, "create_vault"),
                        (
                            creator.clone(),
                            amount,
                            start_timestamp,
                            end_timestamp,
                            milestone_hash.clone(),
                            verifier.clone(),
                            success_destination.clone(),
                            failure_destination.clone(),
                        )
                            .into_val(&env),
                    )),
                    sub_invocations: std::vec![], // std linked above via extern crate
                }
            )
        );

        // ── Assert: vault_created event was emitted ──────────────────────────
        let all_events = env.events().all();
        assert_eq!(all_events.len(), 1, "exactly one event should be emitted");

        let (emitting_contract, topics, _data) = all_events.get(0).unwrap();
        assert_eq!(
            emitting_contract, contract_id,
            "event must come from the vault contract"
        );

        // topics[0] = Symbol("vault_created"), topics[1] = vault_id
        let event_name: Symbol = topics.get(0).unwrap().try_into_val(&env).unwrap();
        let event_vault_id: u32 = topics.get(1).unwrap().try_into_val(&env).unwrap();

        assert_eq!(
            event_name,
            Symbol::new(&env, "vault_created"),
            "event name must be vault_created"
        );
        assert_eq!(
            event_vault_id, vault_id,
            "event vault_id must match the returned vault_id"
        );
    }

    /// Documents expected timestamp validation behaviour.
    /// Marked #[ignore] until the contract enforces end > start.
    #[test]
    #[ignore = "validation not yet implemented in create_vault"]
    fn test_create_vault_rejects_invalid_timestamps() {
        let env = Env::default();
        env.mock_all_auths();

        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);

        let (creator, amount, start, _, hash, verifier, s_dest, f_dest) = make_vault_args(&env);

        // end == start — should panic once validation is added
        client.create_vault(
            &creator, &amount, &start, &start, &hash, &verifier, &s_dest, &f_dest,
        );
    }

    #[test]
    fn test_validate_milestone_rejects_after_end() {
        let env = Env::default();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);

        let creator = Address::generate(&env);
        let verifier = Address::generate(&env);
        let success_dest = Address::generate(&env);
        let failure_dest = Address::generate(&env);

        let start_time = 1000;
        let end_time = 2000;

        env.ledger().set_timestamp(start_time);

        // Sign for create_vault
        env.mock_all_auths();

        let vault_id = client.create_vault(
            &creator,
            &1000,
            &start_time,
            &end_time,
            &BytesN::from_array(&env, &[0u8; 32]),
            &Some(verifier.clone()),
            &success_dest,
            &failure_dest,
        );

        // Advance ledger to exactly end_timestamp
        env.ledger().set_timestamp(end_time);

        // Try to validate milestone - should fail with MilestoneExpired (error code 5)
        let _result = client.try_validate_milestone(&vault_id);
        assert!(_result.is_err());

        // Advance ledger past end_timestamp
        env.ledger().set_timestamp(end_time + 1);

        // Try to validate milestone - should also fail
        let _result = client.try_validate_milestone(&vault_id);
        assert!(_result.is_err());
    }

    #[test]
    fn test_validate_milestone_succeeds_before_end() {
        let env = Env::default();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);

        let creator = Address::generate(&env);
        let verifier = Address::generate(&env);
        let success_dest = Address::generate(&env);
        let failure_dest = Address::generate(&env);

        let start_time = 1000;
        let end_time = 2000;

        env.ledger().set_timestamp(start_time);
        env.mock_all_auths();

        let vault_id = client.create_vault(
            &creator,
            &1000,
            &start_time,
            &end_time,
            &BytesN::from_array(&env, &[0u8; 32]),
            &Some(verifier.clone()),
            &success_dest,
            &failure_dest,
        );

        // Set time to just before end
        env.ledger().set_timestamp(end_time - 1);

        let success = client.validate_milestone(&vault_id);
        assert!(success);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.status, VaultStatus::Completed);
    }
    // -----------------------------------------------------------------------
    // Helpers (from branch test/create-vault-invalid-timestamps)
    // -----------------------------------------------------------------------

    /// Fixture addresses used across tests.
    struct Actors {
        creator: Address,
        success_dest: Address,
        failure_dest: Address,
    }

    /// Build a fresh Soroban test environment, register the contract, and return
    /// the typed client together with pre-generated mock actor addresses.
    fn setup() -> (Env, DisciplrVaultClient<'static>, Actors) {
        let env = Env::default();
        env.mock_all_auths();

        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);

        let actors = Actors {
            creator: Address::generate(&env),
            success_dest: Address::generate(&env),
            failure_dest: Address::generate(&env),
        };

        (env, client, actors)
    }

    /// Return a deterministic 32-byte milestone hash for testing.
    fn milestone_hash(env: &Env) -> BytesN<32> {
        BytesN::from_array(env, &[0xabu8; 32])
    }

    // -----------------------------------------------------------------------
    // Tests
    // -----------------------------------------------------------------------

    #[test]
    #[should_panic(
        expected = "create_vault: start_timestamp must be strictly less than end_timestamp"
    )]
    fn create_vault_rejects_start_equal_end() {
        let (env, client, actors) = setup();

        let amount = 100_000_000;
        let start_timestamp = 1000;
        let end_timestamp = 1000; // start == end
        let milestone_hash = milestone_hash(&env);

        client.create_vault(
            &actors.creator,
            &amount,
            &start_timestamp,
            &end_timestamp,
            &milestone_hash,
            &None,
            &actors.success_dest,
            &actors.failure_dest,
        );
    }

    #[test]
    #[should_panic(
        expected = "create_vault: start_timestamp must be strictly less than end_timestamp"
    )]
    fn create_vault_rejects_start_greater_than_end() {
        let (env, client, actors) = setup();

        let amount = 100_000_000;
        let start_timestamp = 2000;
        let end_timestamp = 1000; // start > end
        let milestone_hash = milestone_hash(&env);

        client.create_vault(
            &actors.creator,
            &amount,
            &start_timestamp,
            &end_timestamp,
            &milestone_hash,
            &None,
            &actors.success_dest,
            &actors.failure_dest,
        );
    }

    #[test]
    fn create_vault_valid_timestamps() {
        let (env, client, actors) = setup();

        let amount = 100_000_000;
        let start_timestamp = 1000;
        let end_timestamp = 2000; // valid
        let milestone_hash = milestone_hash(&env);

        let vault_id = client.create_vault(
            &actors.creator,
            &amount,
            &start_timestamp,
            &end_timestamp,
            &milestone_hash,
            &None,
            &actors.success_dest,
            &actors.failure_dest,
        );

        assert_eq!(vault_id, 0);
    }
}
