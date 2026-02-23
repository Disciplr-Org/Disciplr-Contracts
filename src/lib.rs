#![no_std]
#![allow(clippy::too_many_arguments)]

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

    fn setup_active_vault(env: &Env) -> (DisciplrVaultClient<'_>, u32, u64) {
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(env, &contract_id);

        let creator = Address::generate(env);
        let verifier = Address::generate(env);
        let success_dest = Address::generate(env);
        let failure_dest = Address::generate(env);

        let start_time = 1000;
        let end_time = 2000;

        env.ledger().set_timestamp(start_time);
        env.mock_all_auths();

        let vault_id = client.create_vault(
            &creator,
            &1000,
            &start_time,
            &end_time,
            &BytesN::from_array(env, &[0u8; 32]),
            &Some(verifier),
            &success_dest,
            &failure_dest,
        );

        (client, vault_id, end_time)
    }

    fn setup_active_vault_without_verifier(env: &Env) -> (DisciplrVaultClient<'_>, u32, u64) {
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(env, &contract_id);

        let creator = Address::generate(env);
        let success_dest = Address::generate(env);
        let failure_dest = Address::generate(env);

        let start_time = 1000;
        let end_time = 2000;

        env.ledger().set_timestamp(start_time);
        env.mock_all_auths();

        let vault_id = client.create_vault(
            &creator,
            &1000,
            &start_time,
            &end_time,
            &BytesN::from_array(env, &[0u8; 32]),
            &None,
            &success_dest,
            &failure_dest,
        );

        (client, vault_id, end_time)
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

    #[test]
    fn test_validate_milestone_rejects_when_vault_completed() {
        let env = Env::default();
        let (client, vault_id, end_time) = setup_active_vault(&env);

        env.ledger().set_timestamp(end_time - 1);
        let validated = client.validate_milestone(&vault_id);
        assert!(validated);

        let result = client.try_validate_milestone(&vault_id);
        assert_eq!(result, Err(Ok(Error::VaultNotActive)));
    }

    #[test]
    fn test_validate_milestone_rejects_when_vault_failed() {
        let env = Env::default();
        let (client, vault_id, end_time) = setup_active_vault(&env);

        env.ledger().set_timestamp(end_time);
        let redirected = client.redirect_funds(&vault_id);
        assert!(redirected);

        let result = client.try_validate_milestone(&vault_id);
        assert_eq!(result, Err(Ok(Error::VaultNotActive)));
    }

    #[test]
    fn test_validate_milestone_rejects_when_vault_cancelled() {
        let env = Env::default();
        let (client, vault_id, _) = setup_active_vault(&env);

        let cancelled = client.cancel_vault(&vault_id);
        assert!(cancelled);

        let result = client.try_validate_milestone(&vault_id);
        assert_eq!(result, Err(Ok(Error::VaultNotActive)));
    }

    #[test]
    fn test_validate_milestone_rejects_non_active_statuses() {
        // Completed vault should reject validation.
        let env_completed = Env::default();
        let (client_completed, vault_completed, end_completed) = setup_active_vault(&env_completed);
        env_completed.ledger().set_timestamp(end_completed - 1);
        assert!(client_completed.validate_milestone(&vault_completed));
        assert_eq!(
            client_completed.try_validate_milestone(&vault_completed),
            Err(Ok(Error::VaultNotActive))
        );

        // Failed vault should reject validation.
        let env_failed = Env::default();
        let (client_failed, vault_failed, end_failed) = setup_active_vault(&env_failed);
        env_failed.ledger().set_timestamp(end_failed);
        assert!(client_failed.redirect_funds(&vault_failed));
        assert_eq!(
            client_failed.try_validate_milestone(&vault_failed),
            Err(Ok(Error::VaultNotActive))
        );

        // Cancelled vault should reject validation.
        let env_cancelled = Env::default();
        let (client_cancelled, vault_cancelled, _) = setup_active_vault(&env_cancelled);
        assert!(client_cancelled.cancel_vault(&vault_cancelled));
        assert_eq!(
            client_cancelled.try_validate_milestone(&vault_cancelled),
            Err(Ok(Error::VaultNotActive))
        );
    }

    #[test]
    fn test_validate_milestone_uses_creator_auth_when_verifier_missing() {
        let env = Env::default();
        let (client, vault_id, end_time) = setup_active_vault_without_verifier(&env);

        env.ledger().set_timestamp(end_time - 1);
        let validated = client.validate_milestone(&vault_id);
        assert!(validated);
    }

    #[test]
    fn test_redirect_funds_rejects_before_end_timestamp() {
        let env = Env::default();
        let (client, vault_id, end_time) = setup_active_vault(&env);

        env.ledger().set_timestamp(end_time - 1);
        let result = client.try_redirect_funds(&vault_id);
        assert_eq!(result, Err(Ok(Error::InvalidTimestamp)));
    }

    #[test]
    fn test_release_funds_rejects_when_vault_not_active() {
        let env = Env::default();
        let (client, vault_id, end_time) = setup_active_vault(&env);

        env.ledger().set_timestamp(end_time - 1);
        let validated = client.validate_milestone(&vault_id);
        assert!(validated);

        let result = client.try_release_funds(&vault_id);
        assert_eq!(result, Err(Ok(Error::VaultNotActive)));
    }

    #[test]
    fn test_cancel_vault_rejects_when_vault_not_active() {
        let env = Env::default();
        let (client, vault_id, end_time) = setup_active_vault(&env);

        env.ledger().set_timestamp(end_time - 1);
        let validated = client.validate_milestone(&vault_id);
        assert!(validated);

        let result = client.try_cancel_vault(&vault_id);
        assert_eq!(result, Err(Ok(Error::VaultNotActive)));
    }

    #[test]
    fn test_operations_reject_unknown_vault_id() {
        let env = Env::default();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);
        let missing_vault_id = 999_u32;

        assert_eq!(
            client.try_validate_milestone(&missing_vault_id),
            Err(Ok(Error::VaultNotFound))
        );
        assert_eq!(
            client.try_release_funds(&missing_vault_id),
            Err(Ok(Error::VaultNotFound))
        );
        assert_eq!(
            client.try_redirect_funds(&missing_vault_id),
            Err(Ok(Error::VaultNotFound))
        );
        assert_eq!(
            client.try_cancel_vault(&missing_vault_id),
            Err(Ok(Error::VaultNotFound))
        );
        assert!(client.get_vault_state(&missing_vault_id).is_none());
    }
}

#[cfg(test)]
mod tests {
    extern crate std; // no_std crate — explicitly link std for the test harness

    use super::*;
    use soroban_sdk::{
        testutils::{Address as _, AuthorizedFunction, AuthorizedInvocation, Events},
        Address, BytesN, Env, IntoVal, Symbol, TryIntoVal,
    };

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

    #[test]
    #[should_panic(expected = "end_timestamp must be greater than start_timestamp")]
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
}
