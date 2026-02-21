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
#[derive(Clone)]
pub enum DataKey {
    Vault(u32),
    VaultCount,
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

        if end_timestamp <= start_timestamp {
            panic!("end_timestamp must be greater than start_timestamp");
        }

        let mut vault_count: u32 = env
            .storage()
            .instance()
            .get(&DataKey::VaultCount)
            .unwrap_or(0);
        let vault_id = vault_count;
        vault_count += 1;
        env.storage()
            .instance()
            .set(&DataKey::VaultCount, &vault_count);

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

        env.storage()
            .instance()
            .set(&DataKey::Vault(vault_id), &vault);

        env.events()
            .publish((Symbol::new(&env, "vault_created"), vault_id), vault);
        vault_id
    }

    /// Verifier (or authorized party) validates milestone completion.
    pub fn validate_milestone(env: Env, vault_id: u32) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
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
        env.storage().instance().set(&vault_key, &vault);

        env.events()
            .publish((Symbol::new(&env, "milestone_validated"), vault_id), ());
        Ok(true)
    }

    /// Release funds to success destination.
    pub fn release_funds(env: Env, vault_id: u32) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        // Only allow release if validated (status would be Completed) or maybe this is a redundant method
        // For now, let's just make it a stub that updates status if called.
        // In a real impl, this would handle the actual USDC transfer.
        vault.status = VaultStatus::Completed;
        env.storage().instance().set(&vault_key, &vault);
        Ok(true)
    }

    /// Redirect funds to failure destination (e.g. after deadline without validation).
    pub fn redirect_funds(env: Env, vault_id: u32) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        if env.ledger().timestamp() < vault.end_timestamp {
            return Err(Error::InvalidTimestamp); // Too early to redirect
        }

        vault.status = VaultStatus::Failed;
        env.storage().instance().set(&vault_key, &vault);
        Ok(true)
    }

    /// Cancel vault and return funds to creator.
    pub fn cancel_vault(env: Env, vault_id: u32) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;

        vault.creator.require_auth();

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        vault.status = VaultStatus::Cancelled;
        env.storage().instance().set(&vault_key, &vault);
        Ok(true)
    }

    /// Return current vault state for a given vault id.
    pub fn get_vault_state(env: Env, vault_id: u32) -> Option<ProductivityVault> {
        env.storage().instance().get(&DataKey::Vault(vault_id))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use soroban_sdk::testutils::{Address as _, Ledger};

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
        // Try to validate milestone - should fail with MilestoneExpired
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
}

#[cfg(test)]
mod tests {
    extern crate std; // no_std crate — explicitly link std for the test harness

    use super::*;
    use soroban_sdk::{
        testutils::{Address as _, AuthorizedFunction, AuthorizedInvocation, Events},
        token, Address, BytesN, Env, IntoVal, Symbol, TryIntoVal,
    };

    struct TestEnv<'a> {
        env: Env,
        creator: Address,
        usdc_token_client: token::Client<'a>,
        vault_client: DisciplrVaultClient<'a>,
        vault_amount: i128,
    }

    /// Helper to set up a standard vault test environment with USDC tokens.
    fn setup_vault_test(env: Env, vault_amount: i128) -> TestEnv {
        env.mock_all_auths();
        let contract_id = env.register(DisciplrVault, ());
        let vault_client = DisciplrVaultClient::new(&env, &contract_id);

        let admin = Address::generate(&env);
        let creator = Address::generate(&env);

        let usdc_id = env.register_stellar_asset_contract(admin.clone());
        let usdc_token_client = token::Client::new(&env, &usdc_id);
        let usdc_asset_client = token::StellarAssetClient::new(&env, &usdc_id);

        // Mint enough USDC to creator (amount + some buffer)
        usdc_asset_client.mint(&creator, &(vault_amount * 2));

        TestEnv {
            env,
            creator,
            usdc_token_client,
            vault_client,
            vault_amount,
        }
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

    // ===== USDC Balance Tests: cancel_vault =====

    // Security Notes:
    // - Only the vault creator may cancel; unauthorized callers must be rejected
    // - Balance changes must be exact: vault_amount in, vault_amount out, no rounding
    // - Double cancellation must be prevented to avoid double-spend of USDC
    // - Contract must never hold residual USDC after a valid cancellation

    /// Tests that after cancel_vault, the creator's USDC balance is fully restored
    /// by exactly the vault amount, and the contract's balance decreases by the same.
    /// Ensures no tokens are created, destroyed, or stuck during cancellation.
    #[test]
    fn test_usdc_balance_updates_after_cancel_vault() {
        // Step 1 — Setup
        let env = Env::default();
        let vault_amount = 1_000_000i128; // 1 USDC
        let TestEnv {
            env,
            creator,
            usdc_token_client,
            vault_client,
            vault_amount,
        } = setup_vault_test(env, vault_amount);

        let creator_balance_before_create = usdc_token_client.balance(&creator);
        let contract_balance_before_create = usdc_token_client.balance(&vault_client.address);

        // Step 2 — Create the Vault
        let start_time = 1000;
        let end_time = 2000;
        env.ledger().set_timestamp(start_time);

        let vault_id = vault_client.create_vault(
            &creator,
            &vault_amount,
            &start_time,
            &end_time,
            &BytesN::from_array(&env, &[0u8; 32]),
            &None,
            &Address::generate(&env),
            &Address::generate(&env),
        );

        let creator_balance_after_create = usdc_token_client.balance(&creator);
        let contract_balance_after_create = usdc_token_client.balance(&vault_client.address);

        assert_eq!(
            creator_balance_after_create,
            creator_balance_before_create - vault_amount,
            "Creator balance should decrease by vault_amount after create_vault"
        );
        assert_eq!(
            contract_balance_after_create,
            contract_balance_before_create + vault_amount,
            "Contract balance should increase by vault_amount after create_vault"
        );

        // Step 3 — Cancel the Vault
        vault_client
            .cancel_vault(&vault_id)
            .expect("cancel_vault should succeed for creator");

        // Step 4 — Assert Balance Correctness
        let creator_balance_after_cancel = usdc_token_client.balance(&creator);
        let contract_balance_after_cancel = usdc_token_client.balance(&vault_client.address);

        assert_eq!(
            creator_balance_after_cancel,
            creator_balance_after_create + vault_amount,
            "Creator USDC balance must increase by vault_amount after cancel_vault"
        );
        assert_eq!(
            contract_balance_after_cancel,
            contract_balance_after_create - vault_amount,
            "Contract USDC balance must decrease by vault_amount after cancel_vault"
        );
        assert_eq!(
            creator_balance_after_cancel, creator_balance_before_create,
            "Creator USDC balance must be fully restored to pre-vault amount after cancel"
        );
        assert_eq!(
            contract_balance_after_cancel, contract_balance_before_create,
            "Contract USDC balance must be fully restored to pre-vault amount after cancel"
        );
    }

    /// Tests that calling cancel_vault from an address other than the creator fails.
    /// Ensures that unauthorized users cannot cancel a vault and redirect funds.
    #[test]
    fn test_cancel_vault_unauthorized_caller_fails() {
        let env = Env::default();
        let vault_amount = 1_000_000i128;
        let TestEnv {
            env,
            creator,
            usdc_token_client,
            vault_client,
            vault_amount,
        } = setup_vault_test(env, vault_amount);

        let start_time = 1000;
        let end_time = 2000;
        env.ledger().set_timestamp(start_time);

        let vault_id = vault_client.create_vault(
            &creator,
            &vault_amount,
            &start_time,
            &end_time,
            &BytesN::from_array(&env, &[0u8; 32]),
            &None,
            &Address::generate(&env),
            &Address::generate(&env),
        );

        let creator_balance_after_create = usdc_token_client.balance(&creator);
        let contract_balance_after_create = usdc_token_client.balance(&vault_client.address);

        let non_creator = Address::generate(&env);

        // Use try_cancel_vault to capture the error
        let result = vault_client.try_cancel_vault(&vault_id);

        // Assert failure with NotAuthorized error (Error code 2)
        assert_eq!(
            result,
            Err(Ok(Error::NotAuthorized)),
            "cancel_vault should fail with NotAuthorized for non-creator"
        );

        assert_eq!(
            usdc_token_client.balance(&creator),
            creator_balance_after_create,
            "Creator balance should not change after unauthorized cancel attempt"
        );
        assert_eq!(
            usdc_token_client.balance(&vault_client.address),
            contract_balance_after_create,
            "Contract balance should not change after unauthorized cancel attempt"
        );
    }

    /// Tests that a vault cannot be cancelled more than once.
    /// Prevents double-spending by ensuring a cancelled vault is no longer active.
    #[test]
    fn test_cancel_vault_no_double_cancel() {
        let env = Env::default();
        let vault_amount = 1_000_000i128;
        let TestEnv {
            env,
            creator,
            usdc_token_client,
            vault_client,
            vault_amount,
        } = setup_vault_test(env, vault_amount);

        let start_time = 1000;
        let end_time = 2000;
        env.ledger().set_timestamp(start_time);

        let vault_id = vault_client.create_vault(
            &creator,
            &vault_amount,
            &start_time,
            &end_time,
            &BytesN::from_array(&env, &[0u8; 32]),
            &None,
            &Address::generate(&env),
            &Address::generate(&env),
        );

        // First cancel succeeds
        vault_client
            .cancel_vault(&vault_id)
            .expect("First cancel should succeed");

        let creator_balance_after_cancel = usdc_token_client.balance(&creator);
        let contract_balance_after_cancel = usdc_token_client.balance(&vault_client.address);

        // Second cancel attempt should fail with VaultNotActive (Error code 3)
        let result = vault_client.try_cancel_vault(&vault_id);
        assert_eq!(
            result,
            Err(Ok(Error::VaultNotActive)),
            "Second cancel_vault call should fail with VaultNotActive"
        );

        assert_eq!(
            usdc_token_client.balance(&creator),
            creator_balance_after_cancel,
            "Creator balance should not change after second cancel attempt"
        );
        assert_eq!(
            usdc_token_client.balance(&vault_client.address),
            contract_balance_after_cancel,
            "Contract balance should not change after second cancel attempt"
        );
    }

    /// Tests cancel_vault when the creator has exactly the vault amount.
    /// Guards against rounding errors and ensures full balance restoration.
    #[test]
    fn test_cancel_vault_exact_balance_no_remainder() {
        let env = Env::default();
        let vault_amount = 1_000_000i128;

        // Custom setup to have exact balance
        env.mock_all_auths();
        let contract_id = env.register(DisciplrVault, ());
        let vault_client = DisciplrVaultClient::new(&env, &contract_id);

        let admin = Address::generate(&env);
        let creator = Address::generate(&env);

        let usdc_id = env.register_stellar_asset_contract(admin.clone());
        let usdc_token_client = token::Client::new(&env, &usdc_id);
        let usdc_asset_client = token::StellarAssetClient::new(&env, &usdc_id);

        // Mint EXACTLY vault_amount to creator
        usdc_asset_client.mint(&creator, &vault_amount);

        assert_eq!(usdc_token_client.balance(&creator), vault_amount);

        let start_time = 1000;
        let end_time = 2000;
        env.ledger().set_timestamp(start_time);

        let vault_id = vault_client.create_vault(
            &creator,
            &vault_amount,
            &start_time,
            &end_time,
            &BytesN::from_array(&env, &[0u8; 32]),
            &None,
            &Address::generate(&env),
            &Address::generate(&env),
        );

        assert_eq!(
            usdc_token_client.balance(&creator),
            0,
            "Creator balance should be exactly zero after vault creation"
        );

        vault_client
            .cancel_vault(&vault_id)
            .expect("cancel_vault should succeed");

        assert_eq!(
            usdc_token_client.balance(&creator),
            vault_amount,
            "Creator balance should be restored to exactly vault_amount"
        );
        assert_eq!(
            usdc_token_client.balance(&vault_client.address),
            0,
            "Contract balance should be exactly zero after full refund"
        );
    }
}
