#![no_std]

use soroban_sdk::{
    contract, contracterror, contractimpl, contracttype, panic_with_error, Address, BytesN, Env,
    Symbol,
};

// ── Storage Keys ──────────────────────────────────────────────────────────────

#[contracttype]
#[derive(Clone)]
pub enum DataKey {
    Vault(u32),
    VaultCount,
}

#[cfg(test)]
mod tests;

// ── Domain Types ──────────────────────────────────────────────────────────────

/// Lifecycle status of a `ProductivityVault`.
///
/// State-machine transitions:
/// ```text
///   Active ──release_funds──► Completed
///   Active ──redirect_funds─► Failed
///   Active ──cancel_vault───► Cancelled
/// ```
/// Every terminal state (Completed / Failed / Cancelled) is **absorbing**;
/// no further state-changing call will succeed once the vault leaves Active.
#[contracttype]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VaultStatus {
    Active = 0,
    Completed = 1,
    Failed = 2,
    Cancelled = 3,
}

/// On-chain representation of a single productivity commitment.
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

// ── Errors ────────────────────────────────────────────────────────────────────

#[contracterror]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u32)]
pub enum Error {
    /// Vault not found in storage.
    VaultNotFound = 1,
    /// Operation requires the vault to be in Active status.
    /// Returned on any attempt to release/redirect/cancel a vault that has
    /// already reached a terminal state, preventing double-release and
    /// double-redirect.
    VaultNotActive = 2,
    /// Caller is not authorised for this operation.
    Unauthorised = 3,
    /// redirect_funds called before the vault's end_timestamp has passed.
    DeadlineNotReached = 4,
}

// ── Contract ──────────────────────────────────────────────────────────────────

#[contract]
pub struct DisciplrVault;

#[contractimpl]
impl DisciplrVault {
    // ── Internal helpers ──────────────────────────────────────────────────

    /// Load a vault from persistent storage, panicking with `VaultNotFound`
    /// if the key does not exist.
    fn load_vault(env: &Env, vault_id: u32) -> ProductivityVault {
        env.storage()
            .persistent()
            .get(&DataKey::Vault(vault_id))
            .unwrap_or_else(|| panic_with_error!(env, Error::VaultNotFound))
    }

    /// Persist `vault` back to storage under its `vault_id` key.
    fn save_vault(env: &Env, vault_id: u32, vault: &ProductivityVault) {
        env.storage()
            .persistent()
            .set(&DataKey::Vault(vault_id), vault);
    }

    /// Assert the vault is `Active`.  If not, panic with `VaultNotActive`.
    ///
    /// This is the central idempotency guard: every state-changing function
    /// calls this before touching balances, ensuring each vault can only be
    /// settled once regardless of how many times the function is invoked.
    fn require_active(env: &Env, vault: &ProductivityVault) {
        if vault.status != VaultStatus::Active {
            panic_with_error!(env, Error::VaultNotActive);
        }
    }

    // ── Public interface ──────────────────────────────────────────────────

    /// Create a new productivity vault.
    ///
    /// The caller must have previously approved a USDC token transfer to this
    /// contract equal to `amount`.  In this implementation the token transfer
    /// is stubbed out; a production version would call the token contract here.
    ///
    /// Returns the newly assigned `vault_id`.
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

        // Allocate a monotonically increasing vault id.
        let vault_id: u32 = env
            .storage()
            .persistent()
            .get(&DataKey::VaultCount)
            .unwrap_or(0u32);

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

        Self::save_vault(&env, vault_id, &vault);

        // Persist incremented counter so the next vault gets a unique id.
        env.storage()
            .persistent()
            .set(&DataKey::VaultCount, &(vault_id + 1));

        env.events()
            .publish((Symbol::new(&env, "vault_created"), vault_id), vault);

        vault_id
    }

    /// Verifier confirms milestone completion.
    ///
    /// Requires the vault to be `Active` and the caller to be the designated
    /// verifier.  Transitions the vault to `Completed`.
    ///
    /// # Idempotency
    /// Subsequent calls fail with `VaultNotActive` because the status is no
    /// longer `Active` after the first successful call.
    pub fn validate_milestone(env: Env, vault_id: u32, caller: Address) -> bool {
        caller.require_auth();

        let mut vault = Self::load_vault(&env, vault_id);
        Self::require_active(&env, &vault);

        // Ensure caller is the designated verifier when one is set.
        if let Some(ref verifier) = vault.verifier {
            if *verifier != caller {
                panic_with_error!(&env, Error::Unauthorised);
            }
        }

        // ── Transfer USDC to success_destination (stubbed) ───────────────
        // production: token_client.transfer(&env.current_contract_address(),
        //                                   &vault.success_destination,
        //                                   &vault.amount);

        // Transition to terminal state AFTER transfer succeeds.
        vault.status = VaultStatus::Completed;
        Self::save_vault(&env, vault_id, &vault);

        env.events().publish(
            (Symbol::new(&env, "milestone_validated"), vault_id),
            vault_id,
        );

        true
    }

    /// Release funds to the `success_destination`.
    ///
    /// # Idempotency / Double-Release Prevention
    /// Checks `status == Active` **before** initiating any transfer and
    /// immediately sets `status = Completed` and persists the vault.  Any
    /// subsequent invocation will find status `Completed` and panic with
    /// `VaultNotActive`, making double-release impossible.
    pub fn release_funds(env: Env, vault_id: u32) -> bool {
        let mut vault = Self::load_vault(&env, vault_id);

        // ── IDEMPOTENCY GUARD ─────────────────────────────────────────────
        // If the vault is already Completed, Failed, or Cancelled, this call
        // is rejected immediately — no funds can be moved a second time.
        Self::require_active(&env, &vault);

        // ── Transfer USDC to success_destination (stubbed) ───────────────
        // production: token_client.transfer(&env.current_contract_address(),
        //                                   &vault.success_destination,
        //                                   &vault.amount);

        // Persist the terminal state BEFORE returning so that any re-entrant
        // or replayed call sees Completed and is rejected.
        vault.status = VaultStatus::Completed;
        Self::save_vault(&env, vault_id, &vault);

        env.events()
            .publish((Symbol::new(&env, "funds_released"), vault_id), vault_id);

        true
    }

    /// Redirect funds to the `failure_destination` after the deadline passes.
    ///
    /// # Idempotency / Double-Redirect Prevention
    /// Like `release_funds`, this checks `status == Active` first and
    /// immediately sets `status = Failed` in persistent storage.  Replayed or
    /// concurrent calls receive `VaultNotActive`.
    pub fn redirect_funds(env: Env, vault_id: u32) -> bool {
        let mut vault = Self::load_vault(&env, vault_id);

        // ── IDEMPOTENCY GUARD ─────────────────────────────────────────────
        Self::require_active(&env, &vault);

        // Redirect is only valid once the commitment window has closed.
        let now = env.ledger().timestamp();
        if now <= vault.end_timestamp {
            panic_with_error!(&env, Error::DeadlineNotReached);
        }

        // ── Transfer USDC to failure_destination (stubbed) ───────────────
        // production: token_client.transfer(&env.current_contract_address(),
        //                                   &vault.failure_destination,
        //                                   &vault.amount);

        // Persist terminal state immediately.
        vault.status = VaultStatus::Failed;
        Self::save_vault(&env, vault_id, &vault);

        env.events()
            .publish((Symbol::new(&env, "funds_redirected"), vault_id), vault_id);

        true
    }

    /// Cancel the vault and return funds to the creator.
    ///
    /// Only the original creator may call this, and only while the vault is
    /// still `Active`.
    pub fn cancel_vault(env: Env, vault_id: u32) -> bool {
        let mut vault = Self::load_vault(&env, vault_id);

        // ── IDEMPOTENCY GUARD ─────────────────────────────────────────────
        Self::require_active(&env, &vault);

        vault.creator.require_auth();

        // ── Return USDC to creator (stubbed) ─────────────────────────────
        // production: token_client.transfer(&env.current_contract_address(),
        //                                   &vault.creator,
        //                                   &vault.amount);

        vault.status = VaultStatus::Cancelled;
        Self::save_vault(&env, vault_id, &vault);

        env.events()
            .publish((Symbol::new(&env, "vault_cancelled"), vault_id), vault_id);

        true
    }

    /// Return the current on-chain state for a given vault id, or `None` if it
    /// does not exist.
    pub fn get_vault_state(env: Env, vault_id: u32) -> Option<ProductivityVault> {
        env.storage().persistent().get(&DataKey::Vault(vault_id))
    }
}

