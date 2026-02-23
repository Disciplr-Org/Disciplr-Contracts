#![no_std]
#![allow(clippy::too_many_arguments)]

use soroban_sdk::{
    contract, contracterror, contractimpl, contracttype, Address, BytesN, Env, Symbol,
};

// ─── Storage Keys ────────────────────────────────────────────────────────────

/// Keys for contract storage.
#[contracttype]
#[derive(Clone)]
pub enum DataKey {
    /// Global vault-id counter (instance storage).
    VaultCount,
    /// Per-vault metadata (persistent storage), keyed by vault id.
    Vault(u32),
}

// ─── Domain Types ────────────────────────────────────────────────────────────

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

/// Lifecycle status of a productivity vault.
#[contracttype]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VaultStatus {
    Active = 0,
    Completed = 1,
    Failed = 2,
    Cancelled = 3,
}

/// On-chain representation of a productivity vault.
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

// ─── Event Payloads ──────────────────────────────────────────────────────────
//
// Each state-changing operation publishes a dedicated event with a typed
// payload struct so that indexers / auditing tools get a predictable schema.

/// Payload for `vault_created` events.
#[contracttype]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VaultCreatedEvent {
    pub vault_id: u32,
    pub creator: Address,
    pub amount: i128,
    pub start_timestamp: u64,
    pub end_timestamp: u64,
    pub milestone_hash: BytesN<32>,
    pub verifier: Option<Address>,
    pub success_destination: Address,
    pub failure_destination: Address,
}

/// Payload for `milestone_validated` events.
#[contracttype]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MilestoneValidatedEvent {
    pub vault_id: u32,
    pub verifier: Address,
    pub destination: Address,
    pub amount: i128,
    pub status: VaultStatus,
}

/// Payload for `funds_released` events.
#[contracttype]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FundsReleasedEvent {
    pub vault_id: u32,
    pub destination: Address,
    pub amount: i128,
    pub status: VaultStatus,
}

/// Payload for `funds_redirected` events.
#[contracttype]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FundsRedirectedEvent {
    pub vault_id: u32,
    pub destination: Address,
    pub amount: i128,
    pub status: VaultStatus,
}

/// Payload for `vault_cancelled` events.
#[contracttype]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VaultCancelledEvent {
    pub vault_id: u32,
    pub creator: Address,
    pub amount: i128,
    pub status: VaultStatus,
}

// ─── Contract ────────────────────────────────────────────────────────────────

#[contract]
pub struct DisciplrVault;

// ─── Internal Helpers ────────────────────────────────────────────────────────

/// Read a vault from persistent storage or panic.
fn read_vault(env: &Env, vault_id: u32) -> ProductivityVault {
    env.storage()
        .persistent()
        .get(&DataKey::Vault(vault_id))
        .unwrap_or_else(|| panic!("vault not found"))
}

/// Write a vault to persistent storage.
fn write_vault(env: &Env, vault_id: u32, vault: &ProductivityVault) {
    env.storage()
        .persistent()
        .set(&DataKey::Vault(vault_id), vault);
}

/// Allocate and return the next vault id (0, 1, 2, …).
fn next_vault_id(env: &Env) -> u32 {
    let id: u32 = env
        .storage()
        .instance()
        .get(&DataKey::VaultCount)
        .unwrap_or(0);
    env.storage()
        .instance()
        .set(&DataKey::VaultCount, &(id + 1));
    id
}

/// Panic if the vault is not `Active`.
fn require_active(vault: &ProductivityVault) {
    if vault.status != VaultStatus::Active {
        panic!("vault is not active");
    }
}

// ─── Public Interface ────────────────────────────────────────────────────────

#[contractimpl]
impl DisciplrVault {
    /// Create a new productivity vault. Caller must have approved USDC transfer to this contract.
    ///
    /// # Validation Rules
    /// - Requires `amount > 0`.
    /// - Requires `start_timestamp < end_timestamp`.
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

        if amount <= 0 {
            panic!("amount must be positive");
        }
        if end_timestamp <= start_timestamp {
            panic!("end_timestamp must be after start_timestamp");
        }

        // TODO: pull USDC from creator via token::Client

        let vault_id = next_vault_id(&env);

        let vault = ProductivityVault {
            creator: creator.clone(),
            amount,
            start_timestamp,
            end_timestamp,
            milestone_hash: milestone_hash.clone(),
            verifier: verifier.clone(),
            success_destination: success_destination.clone(),
            failure_destination: failure_destination.clone(),
            status: VaultStatus::Active,
        };
        write_vault(&env, vault_id, &vault);

        env.events().publish(
            (Symbol::new(&env, "vault_created"), vault_id),
            VaultCreatedEvent {
                vault_id,
                creator: vault.creator.clone(),
                amount,
                start_timestamp,
                end_timestamp,
                milestone_hash,
                verifier,
                success_destination,
                failure_destination,
            },
        );

        vault_id
    }

    /// Verifier validates milestone completion.
    ///
    /// Transitions vault `Active` → `Completed`.  The caller must be the
    /// designated verifier recorded on the vault, and the current ledger
    /// timestamp must be ≤ `end_timestamp`.
    ///
    /// **Event:** `milestone_validated` — topics: `(symbol, vault_id)`,
    /// data: [`MilestoneValidatedEvent`].
    ///
    /// # Panics
    /// * Vault not found
    /// * Vault not `Active`
    /// * No verifier set on vault (use `release_funds` instead)
    /// * Caller ≠ designated verifier
    /// * Current timestamp > `end_timestamp`
    pub fn validate_milestone(env: Env, verifier: Address, vault_id: u32) -> bool {
        verifier.require_auth();

        let mut vault = read_vault(&env, vault_id);
        require_active(&vault);

        match vault.verifier {
            Some(ref expected) => {
                if *expected != verifier {
                    panic!("caller is not the designated verifier");
                }
            }
            None => panic!("vault has no designated verifier"),
        }

        if env.ledger().timestamp() > vault.end_timestamp {
            panic!("past deadline");
        }

        vault.status = VaultStatus::Completed;
        write_vault(&env, vault_id, &vault);

        // TODO: transfer USDC to vault.success_destination

        env.events().publish(
            (Symbol::new(&env, "milestone_validated"), vault_id),
            MilestoneValidatedEvent {
                vault_id,
                verifier,
                destination: vault.success_destination.clone(),
                amount: vault.amount,
                status: VaultStatus::Completed,
            },
        );

        true
    }

    /// Release funds to the success destination (self-verified vaults).
    ///
    /// Only callable by the creator when **no verifier** is set.
    /// Transitions vault `Active` → `Completed`.
    ///
    /// **Event:** `funds_released` — topics: `(symbol, vault_id)`,
    /// data: [`FundsReleasedEvent`].
    ///
    /// # Panics
    /// * Vault not found / not `Active`
    /// * Vault has a verifier (use `validate_milestone` instead)
    /// * Caller ≠ creator
    pub fn release_funds(env: Env, creator: Address, vault_id: u32) -> bool {
        creator.require_auth();

        let mut vault = read_vault(&env, vault_id);
        require_active(&vault);

        if vault.verifier.is_some() {
            panic!("vault has a verifier; use validate_milestone");
        }
        if vault.creator != creator {
            panic!("caller is not the vault creator");
        }

        vault.status = VaultStatus::Completed;
        write_vault(&env, vault_id, &vault);

        // TODO: transfer USDC to success_destination

        env.events().publish(
            (Symbol::new(&env, "funds_released"), vault_id),
            FundsReleasedEvent {
                vault_id,
                destination: vault.success_destination.clone(),
                amount: vault.amount,
                status: VaultStatus::Completed,
            },
        );

        true
    }

    /// Redirect funds to the failure destination after the deadline.
    ///
    /// Callable by **anyone** once `ledger_timestamp > end_timestamp` and
    /// the vault is still `Active`.
    /// Transitions vault `Active` → `Failed`.
    ///
    /// **Event:** `funds_redirected` — topics: `(symbol, vault_id)`,
    /// data: [`FundsRedirectedEvent`].
    ///
    /// # Panics
    /// * Vault not found / not `Active`
    /// * Deadline has not passed
    pub fn redirect_funds(env: Env, vault_id: u32) -> bool {
        let mut vault = read_vault(&env, vault_id);
        require_active(&vault);

        if env.ledger().timestamp() <= vault.end_timestamp {
            panic!("deadline has not passed");
        }

        vault.status = VaultStatus::Failed;
        write_vault(&env, vault_id, &vault);

        // TODO: transfer USDC to failure_destination

        env.events().publish(
            (Symbol::new(&env, "funds_redirected"), vault_id),
            FundsRedirectedEvent {
                vault_id,
                destination: vault.failure_destination.clone(),
                amount: vault.amount,
                status: VaultStatus::Failed,
            },
        );

        true
    }

    /// Cancel the vault and return funds to the creator.
    ///
    /// Only the creator may cancel, and only while the vault is `Active`
    /// **and before** `start_timestamp` (the vault hasn't started yet).
    ///
    /// **Event:** `vault_cancelled` — topics: `(symbol, vault_id)`,
    /// data: [`VaultCancelledEvent`].
    ///
    /// # Panics
    /// * Vault not found / not `Active`
    /// * Caller ≠ creator
    /// * Ledger timestamp ≥ `start_timestamp`
    pub fn cancel_vault(env: Env, creator: Address, vault_id: u32) -> bool {
        creator.require_auth();

        let mut vault = read_vault(&env, vault_id);
        require_active(&vault);

        if vault.creator != creator {
            panic!("caller is not the vault creator");
        }
        if env.ledger().timestamp() >= vault.start_timestamp {
            panic!("cannot cancel after vault has started");
        }

        vault.status = VaultStatus::Cancelled;
        write_vault(&env, vault_id, &vault);

        // TODO: return USDC to creator

        env.events().publish(
            (Symbol::new(&env, "vault_cancelled"), vault_id),
            VaultCancelledEvent {
                vault_id,
                creator,
                amount: vault.amount,
                status: VaultStatus::Cancelled,
            },
        );

        true
    }

    /// Return vault state for a given id, or `None` if not found.
    pub fn get_vault_state(env: Env, vault_id: u32) -> Option<ProductivityVault> {
        env.storage().persistent().get(&DataKey::Vault(vault_id))
    }
}

#[cfg(test)]
mod test;
