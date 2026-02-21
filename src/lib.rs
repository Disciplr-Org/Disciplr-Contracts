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
#[derive(Clone)]
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

        let mut vault_count: u32 = env.storage().instance().get(&DataKey::VaultCount).unwrap_or(0);
        let vault_id = vault_count;
        vault_count += 1;
        env.storage().instance().set(&DataKey::VaultCount, &vault_count);

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
        
        env.storage().instance().set(&DataKey::Vault(vault_id), &vault);

        env.events().publish(
            (Symbol::new(&env, "vault_created"), vault_id),
            vault,
        );
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

        env.events().publish(
            (Symbol::new(&env, "milestone_validated"), vault_id),
            (),
        );
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

    /// Cancel vault and return funds to creator (if allowed by rules).
    /// Only Active vaults can be cancelled.
    pub fn cancel_vault(env: Env, vault_id: u32, creator: Address) -> bool {
        creator.require_auth();
        
        // Get vault state
        let vault_opt = Self::get_vault_state(env.clone(), vault_id);
        
        if let Some(vault) = vault_opt {
            // Verify caller is the creator
            if vault.creator != creator {
                panic!("Only vault creator can cancel");
            }
            
            // Only Active vaults can be cancelled
            if vault.status != VaultStatus::Active {
                panic!("Only Active vaults can be cancelled");
            }
            
            // TODO: return USDC to creator, set status to Cancelled
            env.events().publish(
                (Symbol::new(&env, "vault_cancelled"), vault_id),
                (),
            );
            true
        } else {
            panic!("Vault not found");
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
        env.storage().instance().get(&vault_id)
    }
}

// Test helper function outside of contractimpl
#[cfg(test)]
fn set_vault_in_storage(env: &Env, contract_id: &Address, vault_id: u32, vault: ProductivityVault) {
    env.as_contract(contract_id, || {
        env.storage().instance().set(&vault_id, &vault);
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use soroban_sdk::{testutils::Address as _, Env};

    fn create_test_vault(env: &Env, status: VaultStatus) -> (u32, Address, ProductivityVault) {
        let creator = Address::generate(env);
        let verifier = Address::generate(env);
        let success_dest = Address::generate(env);
        let failure_dest = Address::generate(env);
        let milestone_hash = BytesN::from_array(env, &[0u8; 32]);
        
        let vault = ProductivityVault {
            creator: creator.clone(),
            amount: 1000,
            start_timestamp: 1000,
            end_timestamp: 2000,
            milestone_hash,
            verifier: Some(verifier),
            success_destination: success_dest,
            failure_destination: failure_dest,
            status,
        };
        
        let vault_id = 1u32;
        (vault_id, creator, vault)
    }

    #[test]
    #[should_panic(expected = "Only Active vaults can be cancelled")]
    fn test_cancel_vault_when_completed_fails() {
        let env = Env::default();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);
        
        // Create a vault with Completed status
        let (vault_id, creator, vault) = create_test_vault(&env, VaultStatus::Completed);
        
        // Store the vault in contract storage
        set_vault_in_storage(&env, &contract_id, vault_id, vault);
        
        // Mock auth for creator
        env.mock_all_auths();
        
        // Attempt to cancel - should panic
        client.cancel_vault(&vault_id, &creator);
    }

    #[test]
    #[should_panic(expected = "Only Active vaults can be cancelled")]
    fn test_cancel_vault_when_failed_fails() {
        let env = Env::default();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);
        
        // Create a vault with Failed status
        let (vault_id, creator, vault) = create_test_vault(&env, VaultStatus::Failed);
        
        // Store the vault in contract storage
        set_vault_in_storage(&env, &contract_id, vault_id, vault);
        
        // Mock auth for creator
        env.mock_all_auths();
        
        // Attempt to cancel - should panic
        client.cancel_vault(&vault_id, &creator);
    }

    #[test]
    fn test_cancel_vault_when_active_succeeds() {
        let env = Env::default();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);
        
        // Create a vault with Active status
        let (vault_id, creator, vault) = create_test_vault(&env, VaultStatus::Active);
        
        // Store the vault in contract storage
        set_vault_in_storage(&env, &contract_id, vault_id, vault);
        
        // Mock auth for creator
        env.mock_all_auths();
        
        // Cancel should succeed
        let result = client.cancel_vault(&vault_id, &creator);
        assert!(result, "Expected cancel_vault to succeed for Active vault");
    }

    #[test]
    #[should_panic(expected = "Only Active vaults can be cancelled")]
    fn test_cancel_vault_when_cancelled_fails() {
        let env = Env::default();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);
        
        // Create a vault with Cancelled status
        let (vault_id, _creator, vault) = create_test_vault(&env, VaultStatus::Cancelled);
        
        // Store the vault in contract storage
        set_vault_in_storage(&env, &contract_id, vault_id, vault.clone());
        
        // Mock auth for creator
        env.mock_all_auths();
        
        // Attempt to cancel - should panic
        client.cancel_vault(&vault_id, &vault.creator);
    }

    #[test]
    #[should_panic(expected = "Only vault creator can cancel")]
    fn test_cancel_vault_non_creator_fails() {
        let env = Env::default();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);
        
        // Create a vault with Active status
        let (vault_id, _creator, vault) = create_test_vault(&env, VaultStatus::Active);
        
        // Store the vault in contract storage
        set_vault_in_storage(&env, &contract_id, vault_id, vault);
        
        // Try to cancel with a different address
        let non_creator = Address::generate(&env);
        env.mock_all_auths();
        
        // Attempt to cancel - should panic
        client.cancel_vault(&vault_id, &non_creator);
    }

    #[test]
    #[should_panic(expected = "Vault not found")]
    fn test_cancel_vault_nonexistent_fails() {
        let env = Env::default();
        let contract_id = env.register(DisciplrVault, ());
        let client = DisciplrVaultClient::new(&env, &contract_id);
        
        let creator = Address::generate(&env);
        let vault_id = 999u32;
        
        env.mock_all_auths();
        
        // Attempt to cancel non-existent vault - should panic
        client.cancel_vault(&vault_id, &creator);
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
        Address, BytesN, Env, IntoVal, Symbol, TryIntoVal,
    };

    /// Helper: build a default set of valid vault parameters.
    fn make_vault_args(
        env: &Env,
    ) -> (Address, i128, u64, u64, BytesN<32>, Option<Address>, Address, Address) {
        let creator        = Address::generate(env);
        let success_dest   = Address::generate(env);
        let failure_dest   = Address::generate(env);
        let verifier       = Address::generate(env);
        let milestone_hash = BytesN::from_array(env, &[1u8; 32]);
        let amount         = 1_000_000i128; // 1 USDC (6 decimals)
        let start          = 1_000_000u64;
        let end            = 2_000_000u64;

        (creator, amount, start, end, milestone_hash, Some(verifier), success_dest, failure_dest)
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
        let client      = DisciplrVaultClient::new(&env, &contract_id);

        let (creator, amount, start_timestamp, end_timestamp,
             milestone_hash, verifier, success_destination, failure_destination) =
            make_vault_args(&env);

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
        assert_eq!(emitting_contract, contract_id, "event must come from the vault contract");

        // topics[0] = Symbol("vault_created"), topics[1] = vault_id
        let event_name: Symbol = topics.get(0).unwrap().try_into_val(&env).unwrap();
        let event_vault_id: u32 = topics.get(1).unwrap().try_into_val(&env).unwrap();

        assert_eq!(event_name, Symbol::new(&env, "vault_created"), "event name must be vault_created");
        assert_eq!(event_vault_id, vault_id, "event vault_id must match the returned vault_id");
    }

    /// Documents expected timestamp validation behaviour.
    /// Marked #[ignore] until the contract enforces end > start.
    #[test]
    #[ignore = "validation not yet implemented in create_vault"]
    fn test_create_vault_rejects_invalid_timestamps() {
        let env = Env::default();
        env.mock_all_auths();

        let contract_id = env.register(DisciplrVault, ());
        let client      = DisciplrVaultClient::new(&env, &contract_id);

        let (creator, amount, start, _, hash, verifier, s_dest, f_dest) = make_vault_args(&env);

        // end == start — should panic once validation is added
        client.create_vault(&creator, &amount, &start, &start, &hash, &verifier, &s_dest, &f_dest);
    }
}