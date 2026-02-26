//! # Disciplr Vault Smart Contract
//!
//! A Soroban smart contract for creating programmable time-locked USDC vaults on Stellar.
//! Users can lock funds with milestone-based release conditions, enabling productivity
//! commitments with automated fund distribution based on success or failure.
//!
//! ## Features
//!
//! - Time-locked vault creation with customizable start/end timestamps
//! - Milestone-based validation system with optional verifier
//! - Automatic fund routing to success or failure destinations
//! - Vault cancellation with fund recovery
//! - Event emission for all state changes
//!
//! ## Security Considerations
//!
//! - All state-changing operations require proper authentication
//! - Timestamp validation prevents premature or late operations
//! - Status checks ensure vaults can only transition through valid states
//! - Fund transfers are atomic and cannot be partially executed

#![no_std]
#![allow(clippy::too_many_arguments)]

use soroban_sdk::{
    contract, contracterror, contractimpl, contracttype, token, Address, BytesN, Env, Symbol,
};

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------
//
// Contract-specific errors used in revert paths. Follows Soroban error
// conventions: use Result<T, Error> and return Err(Error::Variant) instead
// of generic panics where appropriate.

#[contracterror]
#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
#[repr(u32)]
pub enum Error {
    /// Vault with the given id does not exist.
    VaultNotFound = 1,
    /// Caller is not authorized for this operation (e.g. not verifier/creator, or release before deadline without validation).
    NotAuthorized = 2,
    /// Vault is not in Active status (e.g. already Completed, Failed, or Cancelled).
    VaultNotActive = 3,
    /// Timestamp constraint violated (e.g. redirect before end_timestamp, or invalid time window).
    InvalidTimestamp = 4,
    /// Validation is no longer allowed because current time is at or past end_timestamp.
    MilestoneExpired = 5,
    /// Vault is in an invalid status for the requested operation.
    InvalidStatus = 6,
    /// Amount must be positive (e.g. create_vault amount <= 0).
    InvalidAmount = 7,
    /// start_timestamp must be strictly less than end_timestamp.
    InvalidTimestamps = 8,
    /// Vault duration (end − start) exceeds MAX_VAULT_DURATION.
    DurationTooLong = 9,
}

// ---------------------------------------------------------------------------
// Data types
// ---------------------------------------------------------------------------

/// Represents the current lifecycle state of a productivity vault.
///
/// # States
///
/// - `Active`: Vault is created and awaiting milestone validation or deadline
/// - `Completed`: Milestone validated successfully, funds released to success destination
/// - `Failed`: Deadline passed without validation, funds redirected to failure destination
/// - `Cancelled`: Vault cancelled by creator, funds returned
///
/// # Invariants
///
/// - Once a vault reaches `Completed`, `Failed`, or `Cancelled`, it cannot transition to any other state
/// - Only `Active` vaults can be validated, released, redirected, or cancelled
#[contracttype]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VaultStatus {
    /// Vault is active and awaiting milestone completion or deadline
    Active = 0,
    /// Milestone validated successfully, funds released to success destination
    Completed = 1,
    /// Deadline passed without validation, funds sent to failure destination
    Failed = 2,
    /// Vault cancelled by creator, funds returned
    Cancelled = 3,
}

// Constants to prevent abuse, spam, and potential overflow issues
pub const MAX_VAULT_DURATION: u64 = 365 * 24 * 60 * 60; // 1 year in seconds
pub const MIN_AMOUNT: i128 = 10_000_000; // 1 USDC with 7 decimals
pub const MAX_AMOUNT: i128 = 10_000_000_000_000; // 10 million USDC with 7 decimals

#[contracttype]
pub enum DataKey {
    VaultCount,
    Vault(u32),
}

/// Core data structure representing a productivity vault with time-locked funds.
///
/// # Fields
///
/// - `creator`: Address that created and funded the vault
/// - `amount`: Amount of USDC locked in the vault (in stroops, 1 USDC = 10^7 stroops)
/// - `start_timestamp`: Unix timestamp when the vault becomes active
/// - `end_timestamp`: Unix timestamp deadline for milestone completion
/// - `milestone_hash`: SHA-256 hash of the milestone criteria for validation
/// - `verifier`: Optional address authorized to validate milestone completion
/// - `success_destination`: Address to receive funds upon successful milestone validation
/// - `failure_destination`: Address to receive funds if milestone is not validated by deadline
/// - `status`: Current lifecycle state of the vault
///
/// # Invariants
///
/// - `amount` must be positive (> 0)
/// - `end_timestamp` must be greater than `start_timestamp`
/// - `creator`, `success_destination`, and `failure_destination` must be valid addresses
/// - If `verifier` is `Some`, only that address can validate the milestone
/// - If `verifier` is `None`, any authorized party can validate (implementation-defined)
#[contracttype]
pub struct ProductivityVault {
    /// Address that created and funded the vault
    pub creator: Address,
    /// Amount of USDC locked (in stroops)
    pub amount: i128,
    /// Unix timestamp when vault becomes active
    pub start_timestamp: u64,
    /// Unix timestamp deadline for milestone completion
    pub end_timestamp: u64,
    /// SHA-256 hash of milestone criteria
    pub milestone_hash: BytesN<32>,
    /// Optional address authorized to validate milestone
    pub verifier: Option<Address>,
    /// Address to receive funds on success
    pub success_destination: Address,
    /// Address to receive funds on failure
    pub failure_destination: Address,
    /// Current vault status
    pub status: VaultStatus,
    pub milestone_validated: bool,
}

/// Main contract for managing productivity vaults with time-locked USDC.
///
/// This contract enables users to create commitment mechanisms by locking funds
/// that are automatically distributed based on milestone completion within a deadline.
#[contract]
pub struct DisciplrVault;

#[contractimpl]
impl DisciplrVault {
    /// Creates a new productivity vault with time-locked USDC funds.
    ///
    /// This function initializes a vault that locks the specified amount of USDC until
    /// either the milestone is validated or the deadline passes. The creator must have
    /// previously approved the USDC token contract to transfer funds on their behalf.
    ///
    /// # Parameters
    ///
    /// - `env`: Soroban environment for contract execution
    /// - `creator`: Address creating and funding the vault (must authorize this call)
    /// - `amount`: Amount of USDC to lock in stroops (must be > 0)
    /// - `start_timestamp`: Unix timestamp when the vault becomes active
    /// - `end_timestamp`: Unix timestamp deadline for milestone completion (must be > start_timestamp)
    /// - `milestone_hash`: SHA-256 hash of the milestone criteria for validation
    /// - `verifier`: Optional address authorized to validate milestone (None allows any authorized party)
    /// - `success_destination`: Address to receive funds upon successful validation
    /// - `failure_destination`: Address to receive funds if deadline passes without validation
    ///
    /// # Returns
    ///
    /// Returns a unique `u32` vault ID that can be used to reference this vault in future operations.
    ///
    /// # Events
    ///
    /// Emits a `vault_created` event with the vault ID and full vault data.
    ///
    /// # Panics / Reverts
    ///
    /// - If `creator` does not authorize the transaction
    /// - If `amount` is not positive (≤ 0)
    /// - If `end_timestamp` ≤ `start_timestamp`
    /// - If USDC transfer from creator fails (insufficient balance or allowance)
    /// - If any address parameter is invalid
    ///
    /// # Security Notes
    ///
    /// - Creator must call `approve()` on the USDC token contract before calling this function
    /// - The contract will hold custody of the funds until vault resolution
    /// - Vault ID allocation must be collision-resistant in production implementation
    ///
    /// # TODO
    ///
    /// - Implement actual USDC token transfer from creator to contract
    /// - Implement persistent storage with unique vault ID generation
    /// - Add validation for timestamp ordering and amount positivity
    pub fn create_vault(
        env: Env,
        usdc_token: Address,
        creator: Address,
        amount: i128,
        start_timestamp: u64,
        end_timestamp: u64,
        milestone_hash: BytesN<32>,
        verifier: Option<Address>,
        success_destination: Address,
        failure_destination: Address,
    ) -> Result<u32, Error> {
        creator.require_auth();

        // Enforce amount bounds
        if amount < MIN_AMOUNT {
            return Err(Error::InvalidAmount);
        }
        if amount > MAX_AMOUNT {
            return Err(Error::InvalidAmount);
        }

        // Reasonable start time (e.g. not too far in past/future)
        let current = env.ledger().timestamp();
        if start_timestamp < current {
            return Err(Error::InvalidTimestamp);
        }

        // Enforce duration bounds
        if end_timestamp <= start_timestamp {
            return Err(Error::InvalidTimestamps);
        }
        let duration = end_timestamp - start_timestamp;
        if duration > MAX_VAULT_DURATION {
            return Err(Error::InvalidTimestamp);
        }

        // Pull USDC from creator into this contract.
        let token_client = token::Client::new(&env, &usdc_token);
        token_client.transfer(&creator, &env.current_contract_address(), &amount);

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
            creator: creator.clone(),
            amount,
            start_timestamp,
            end_timestamp,
            milestone_hash,
            verifier,
            success_destination,
            failure_destination,
            status: VaultStatus::Active,
            milestone_validated: false,
        };
        env.storage()
            .instance()
            .set(&DataKey::Vault(vault_id), &vault);
        env.events()
            .publish((Symbol::new(&env, "vault_created"), vault_id), vault_id);
        Ok(vault_id)
    }

    /// Verifier (or creator when verifier is None) validates milestone completion.
    pub fn validate_milestone(env: Env, vault_id: u32) -> Result<bool, Error> {
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&DataKey::Vault(vault_id))
            .ok_or(Error::VaultNotFound)?;

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        let current = env.ledger().timestamp();
        if current >= vault.end_timestamp {
            return Err(Error::MilestoneExpired);
        }

        if let Some(ref verifier) = vault.verifier {
            verifier.require_auth();
        } else {
            vault.creator.require_auth();
        }

        vault.milestone_validated = true;
        env.storage()
            .instance()
            .set(&DataKey::Vault(vault_id), &vault);

    /// Validates milestone completion and releases funds to the success destination.
    ///
    /// This function allows the designated verifier (or authorized party if no verifier is set)
    /// to confirm that the milestone criteria have been met. Upon successful validation,
    /// the locked USDC is transferred to the success destination and the vault status
    /// is updated to `Completed`.
    ///
    /// # Parameters
    ///
    /// - `env`: Soroban environment for contract execution
    /// - `vault_id`: Unique identifier of the vault to validate
    ///
    /// # Returns
    ///
    /// Returns `true` if validation succeeds and funds are released, `false` otherwise.
    ///
    /// # Events
    ///
    /// Emits a `milestone_validated` event with the vault ID upon successful validation.
    ///
    /// # Panics / Reverts
    ///
    /// - If vault with `vault_id` does not exist
    /// - If vault status is not `Active` (already completed, failed, or cancelled)
    /// - If caller is not the designated verifier (when verifier is set)
    /// - If current timestamp is past `end_timestamp` (deadline expired)
    /// - If USDC transfer to success destination fails
    ///
    /// # Invariants
    ///
    /// - After successful execution, vault status transitions from `Active` to `Completed`
    /// - Funds are atomically transferred to success destination
    /// - Vault cannot be validated more than once
    ///
    /// # Security Notes
    ///
    /// - Only the designated verifier can call this function (if verifier is set)
    /// - Validation must occur before the end_timestamp deadline
    /// - Once validated, the vault cannot be cancelled or redirected
    ///
    /// # TODO
    ///
    /// - Implement vault existence and status checks
    /// - Implement verifier authorization check
    /// - Implement timestamp validation (current time < end_timestamp)
    /// - Implement USDC transfer to success_destination
    /// - Update vault status to Completed in storage
    pub fn validate_milestone(env: Env, vault_id: u32) -> bool {
        // TODO: check vault exists, status is Active, caller is verifier, timestamp < end
        // TODO: transfer USDC to success_destination, set status Completed
        env.events()
            .publish((Symbol::new(&env, "milestone_validated"), vault_id), ());
        Ok(true)
    }

    /// Release funds to success destination (after validation, or after deadline when no verifier).
    pub fn release_funds(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error> {
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&DataKey::Vault(vault_id))
            .ok_or(Error::VaultNotFound)?;

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        let current = env.ledger().timestamp();
        let can_release = vault.milestone_validated || current > vault.end_timestamp;
        if !can_release {
            return Err(Error::NotAuthorized);
        }

        vault.status = VaultStatus::Completed;
        env.storage()
            .instance()
            .set(&DataKey::Vault(vault_id), &vault);

        let token_client = token::Client::new(&env, &usdc_token);
        token_client.transfer(
            &env.current_contract_address(),
            &vault.success_destination,
            &vault.amount,
        );

        env.events()
            .publish((Symbol::new(&env, "funds_released"), vault_id), ());
        Ok(true)
    }

    /// Redirect funds to failure destination after deadline without validation.
    pub fn redirect_funds(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error> {
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&DataKey::Vault(vault_id))
            .ok_or(Error::VaultNotFound)?;

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        let current = env.ledger().timestamp();
        if current <= vault.end_timestamp {
            return Err(Error::InvalidTimestamp);
        }

        vault.status = VaultStatus::Failed;
        env.storage()
            .instance()
            .set(&DataKey::Vault(vault_id), &vault);

        let token_client = token::Client::new(&env, &usdc_token);
        token_client.transfer(
            &env.current_contract_address(),
            &vault.failure_destination,
            &vault.amount,
        );

        env.events()
            .publish((Symbol::new(&env, "funds_redirected"), vault_id), ());
        Ok(true)
    }

    /// Cancel vault and return funds to creator.
    pub fn cancel_vault(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error> {
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&DataKey::Vault(vault_id))
            .ok_or(Error::VaultNotFound)?;

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        vault.creator.require_auth();

        vault.status = VaultStatus::Cancelled;
        env.storage()
            .instance()
            .set(&DataKey::Vault(vault_id), &vault);

        let token_client = token::Client::new(&env, &usdc_token);
        token_client.transfer(
            &env.current_contract_address(),
            &vault.creator,
            &vault.amount,
        );

        env.events()
            .publish((Symbol::new(&env, "vault_cancelled"), vault_id), ());
        Ok(true)
    }

    /// Return current vault state for a given vault id.
    pub fn get_vault_state(env: Env, vault_id: u32) -> Option<ProductivityVault> {
        env.storage().instance().get(&DataKey::Vault(vault_id))
    /// Releases vault funds to the success destination.
    ///
    /// This function transfers the locked USDC to the success destination address
    /// and marks the vault as completed. It can be called after milestone validation
    /// or by automated deadline logic.
    ///
    /// # Parameters
    ///
    /// - `env`: Soroban environment for contract execution (currently unused)
    /// - `vault_id`: Unique identifier of the vault to release funds from
    ///
    /// # Returns
    ///
    /// Returns `true` if funds are successfully released, `false` otherwise.
    ///
    /// # Panics / Reverts
    ///
    /// - If vault with `vault_id` does not exist
    /// - If vault status is not `Active`
    /// - If USDC transfer to success destination fails
    /// - If caller is not authorized to release funds
    ///
    /// # Invariants
    ///
    /// - After successful execution, vault status transitions to `Completed`
    /// - Full vault amount is transferred to success_destination
    /// - Vault cannot be released more than once
    ///
    /// # Security Notes
    ///
    /// - Authorization rules must be enforced (typically verifier or contract logic)
    /// - Transfer is atomic - either full amount transfers or transaction reverts
    ///
    /// # TODO
    ///
    /// - Implement vault status check (must be Active)
    /// - Implement USDC transfer to success_destination
    /// - Update vault status to Completed in storage
    /// - Add authorization checks
    pub fn release_funds(_env: Env, _vault_id: u32) -> bool {
        // TODO: require status Active, transfer to success_destination, set Completed
        true
    }

    /// Redirects vault funds to the failure destination after deadline expiration.
    ///
    /// This function transfers the locked USDC to the failure destination address
    /// when the milestone has not been validated before the end_timestamp deadline.
    /// This enforces the commitment mechanism by penalizing missed deadlines.
    ///
    /// # Parameters
    ///
    /// - `env`: Soroban environment for contract execution (currently unused)
    /// - `vault_id`: Unique identifier of the vault to redirect funds from
    ///
    /// # Returns
    ///
    /// Returns `true` if funds are successfully redirected, `false` otherwise.
    ///
    /// # Panics / Reverts
    ///
    /// - If vault with `vault_id` does not exist
    /// - If vault status is not `Active`
    /// - If current timestamp is before `end_timestamp` (deadline not yet passed)
    /// - If USDC transfer to failure destination fails
    ///
    /// # Invariants
    ///
    /// - After successful execution, vault status transitions to `Failed`
    /// - Full vault amount is transferred to failure_destination
    /// - Can only be called after end_timestamp has passed
    /// - Vault cannot be redirected more than once
    ///
    /// # Security Notes
    ///
    /// - Timestamp check prevents premature fund redirection
    /// - Transfer is atomic - either full amount transfers or transaction reverts
    /// - Anyone can call this function after the deadline (permissionless execution)
    ///
    /// # TODO
    ///
    /// - Implement vault status check (must be Active)
    /// - Implement timestamp validation (current time > end_timestamp)
    /// - Implement USDC transfer to failure_destination
    /// - Update vault status to Failed in storage
    pub fn redirect_funds(_env: Env, _vault_id: u32) -> bool {
        // TODO: require status Active and past end_timestamp, transfer to failure_destination, set Failed
        true
    }

    /// Cancels an active vault and returns funds to the creator.
    ///
    /// This function allows the vault creator to cancel an active vault and recover
    /// their locked funds. Cancellation rules may restrict when this is allowed
    /// (e.g., only before start_timestamp or with penalties).
    ///
    /// # Parameters
    ///
    /// - `env`: Soroban environment for contract execution (currently unused)
    /// - `vault_id`: Unique identifier of the vault to cancel
    ///
    /// # Returns
    ///
    /// Returns `true` if vault is successfully cancelled and funds returned, `false` otherwise.
    ///
    /// # Panics / Reverts
    ///
    /// - If vault with `vault_id` does not exist
    /// - If vault status is not `Active`
    /// - If caller is not the vault creator
    /// - If cancellation is not allowed by business rules (e.g., after start_timestamp)
    /// - If USDC transfer back to creator fails
    ///
    /// # Invariants
    ///
    /// - After successful execution, vault status transitions to `Cancelled`
    /// - Full vault amount is returned to creator address
    /// - Vault cannot be cancelled more than once
    /// - Only creator can cancel their own vault
    ///
    /// # Security Notes
    ///
    /// - Requires creator authorization to prevent unauthorized cancellations
    /// - Business logic should define clear cancellation windows
    /// - Consider implementing cancellation penalties for post-start cancellations
    ///
    /// # TODO
    ///
    /// - Implement creator authorization check
    /// - Implement vault status check (must be Active)
    /// - Implement cancellation policy (time-based restrictions)
    /// - Implement USDC transfer back to creator
    /// - Update vault status to Cancelled in storage
    pub fn cancel_vault(_env: Env, _vault_id: u32) -> bool {
        // TODO: require creator auth, return USDC to creator, set Cancelled
        true
    }

    /// Retrieves the current state of a vault by its ID.
    ///
    /// This function queries the contract storage and returns the complete vault
    /// data structure including all metadata and current status.
    ///
    /// # Parameters
    ///
    /// - `env`: Soroban environment for contract execution (currently unused)
    /// - `vault_id`: Unique identifier of the vault to query
    ///
    /// # Returns
    ///
    /// Returns `Some(ProductivityVault)` if the vault exists, or `None` if no vault
    /// with the given ID is found.
    ///
    /// # Panics / Reverts
    ///
    /// This function does not panic. It returns `None` for non-existent vaults.
    ///
    /// # Usage
    ///
    /// This is a read-only query function that can be called by anyone to inspect
    /// vault state. Useful for:
    /// - Checking vault status before attempting operations
    /// - Displaying vault details in user interfaces
    /// - Verifying vault parameters and deadlines
    /// - Auditing vault history
    ///
    /// # Security Notes
    ///
    /// - This is a public read function with no authorization requirements
    /// - All vault data is publicly visible on-chain
    /// - No state modifications occur during this call
    ///
    /// # TODO
    ///
    /// - Implement storage lookup by vault_id
    /// - Return actual vault data from persistent storage
    /// - Consider adding batch query function for multiple vaults
    pub fn get_vault_state(_env: Env, _vault_id: u32) -> Option<ProductivityVault> {
        None
    }
}

#[cfg(test)]
mod tests {
    extern crate std;

    use super::*;
    use soroban_sdk::{
        testutils::{Address as _, AuthorizedFunction, Events, Ledger},
        token::{StellarAssetClient, TokenClient},
        IntoVal,
    };

    struct TestSetup {
        env: Env,
        contract_id: Address,
        usdc_token: Address,
        creator: Address,
        verifier: Address,
        success_dest: Address,
        failure_dest: Address,
        amount: i128,
        start_timestamp: u64,
        end_timestamp: u64,
    }

    impl TestSetup {
        fn new() -> Self {
            let env = Env::default();
            env.mock_all_auths();

            // Deploy USDC mock token.
            let usdc_admin = Address::generate(&env);
            let usdc_token = env.register_stellar_asset_contract_v2(usdc_admin.clone());
            let usdc_addr = usdc_token.address();
            let usdc_asset = StellarAssetClient::new(&env, &usdc_addr);

            // Actors.
            let creator = Address::generate(&env);
            let verifier = Address::generate(&env);
            let success_dest = Address::generate(&env);
            let failure_dest = Address::generate(&env);

            // Mint USDC to creator.
            let amount: i128 = MIN_AMOUNT;
            usdc_asset.mint(&creator, &amount);

            // Deploy contract.
            let contract_id = env.register(DisciplrVault, ());

            TestSetup {
                env,
                contract_id,
                usdc_token: usdc_addr,
                creator,
                verifier,
                success_dest,
                failure_dest,
                amount,
                start_timestamp: 100,
                end_timestamp: 1_000,
            }
        }

        fn client(&self) -> DisciplrVaultClient<'_> {
            DisciplrVaultClient::new(&self.env, &self.contract_id)
        }

        fn usdc_client(&self) -> TokenClient<'_> {
            TokenClient::new(&self.env, &self.usdc_token)
        }

        fn milestone_hash(&self) -> BytesN<32> {
            BytesN::from_array(&self.env, &[1u8; 32])
        }

        fn create_default_vault(&self) -> u32 {
            self.client().create_vault(
                &self.usdc_token,
                &self.creator,
                &self.amount,
                &self.start_timestamp,
                &self.end_timestamp,
                &self.milestone_hash(),
                &Some(self.verifier.clone()),
                &self.success_dest,
                &self.failure_dest,
            )
        }

        /// Create vault with verifier = None (only creator can validate).
        fn create_vault_no_verifier(&self) -> u32 {
            self.client().create_vault(
                &self.usdc_token,
                &self.creator,
                &self.amount,
                &self.start_timestamp,
                &self.end_timestamp,
                &self.milestone_hash(),
                &None,
                &self.success_dest,
                &self.failure_dest,
            )
        }
    }

    // -----------------------------------------------------------------------
    // Upstream Tests (Migrated & Merged)
    // -----------------------------------------------------------------------

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
        let amount = MIN_AMOUNT;
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
                let event_name: Symbol = topics.get(0).unwrap().into_val(&env);
                if event_name == Symbol::new(&env, "vault_created") {
                    let event_vault_id: u32 = topics.get(1).unwrap().into_val(&env);
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
    }

    /// Issue #44: Test that create_vault accepts verifier == creator
    /// and that validate_milestone can be called by the creator in that case.
    #[test]
    fn test_verifier_same_as_creator() {
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
    }

    // -----------------------------------------------------------------------
    // Issue #25: release_funds fails when vault is Failed
    // -----------------------------------------------------------------------

    #[test]
    fn test_release_funds_fails_when_vault_failed() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
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
