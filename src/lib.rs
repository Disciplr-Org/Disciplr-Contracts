#![no_std]

use soroban_sdk::{
    contract, contractimpl, contracttype, Address, BytesN, Env, Symbol,
    symbol_short,
};

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
    const NEXT_VAULT_ID_KEY: Symbol = symbol_short!("vault_id");

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

        // Retrieve the next vault ID from storage, default to 0 if not set
        let next_vault_id: u32 = env.storage().persistent().get(&Self::NEXT_VAULT_ID_KEY).unwrap_or(0);

        // Create the vault metadata
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

        // Persist the vault metadata (using the vault ID as the key)
        env.storage().persistent().set(&next_vault_id, &vault);

        // Increment and persist the next vault ID
        env.storage().persistent().set(&Self::NEXT_VAULT_ID_KEY, &(next_vault_id + 1));

        // Publish an event for the created vault
        env.events().publish(
            (Symbol::new(&env, "vault_created"), next_vault_id),
            vault,
        );

        next_vault_id
    }

    /// Verifier (or authorized party) validates milestone completion.
    pub fn validate_milestone(env: Env, vault_id: u32) -> bool {
        // TODO: check vault exists, status is Active, caller is verifier, timestamp < end
        // TODO: transfer USDC to success_destination, set status Completed
        env.events().publish(
            (Symbol::new(&env, "milestone_validated"), vault_id),
            (),
        );
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
}
