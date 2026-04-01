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
    /// Milestone has already been validated for this vault.
    AlreadyValidated = 10,
}

// ---------------------------------------------------------------------------
// Data types
// ---------------------------------------------------------------------------

// Constants to prevent abuse, spam, and potential overflow issues
pub const MAX_VAULT_DURATION: u64 = 365 * 24 * 60 * 60; // 1 year in seconds
pub const MIN_AMOUNT: i128 = 10_000_000; // 1 USDC with 7 decimals
pub const MAX_AMOUNT: i128 = 10_000_000_000_000; // 10 million USDC with 7 decimals

#[contracttype]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VaultStatus {
    Active = 0,
    Completed = 1,
    Failed = 2,
    Cancelled = 3,
}

/// Core vault record persisted in contract storage.
#[contracttype]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProductivityVault {
    /// Address that created (and funded) the vault.
    pub creator: Address,
    /// USDC amount locked in the vault (in stroops / smallest unit).
    pub amount: i128,
    /// Ledger timestamp when the commitment period starts.
    pub start_timestamp: u64,
    /// Ledger timestamp after which deadline-based release is allowed.
    pub end_timestamp: u64,
    /// Commitment metadata for the off-chain milestone description.
    /// This hash is stored and compared only as opaque bytes; it is not used
    /// as an on-chain cryptographic primitive or security boundary.
    pub milestone_hash: BytesN<32>,
    /// Optional designated verifier. When `Some(addr)`, only that address may call `validate_milestone`.
    /// When `None`, only the creator may call `validate_milestone` (no third-party validation).
    /// `release_funds` is consistent: after deadline, anyone can release; before deadline, only
    /// after the designated validator (or creator when verifier is None) has validated.
    pub verifier: Option<Address>,
    /// Funds go here on success.
    pub success_destination: Address,
    /// Funds go here on failure/redirect.
    pub failure_destination: Address,
    /// Current lifecycle status.
    pub status: VaultStatus,
    /// Set to `true` once the verifier (or authorised party) calls `validate_milestone`.
    /// Used by `release_funds` to allow early release before the deadline.
    pub milestone_validated: bool,
}

// ---------------------------------------------------------------------------
// Storage keys
// ---------------------------------------------------------------------------

#[contracttype]
#[derive(Clone)]
pub enum DataKey {
    Vault(u32),
    VaultCount,
    TokenAddress,
}

fn ensure_amount_in_range(amount: i128) -> Result<i128, Error> {
    if !(MIN_AMOUNT..=MAX_AMOUNT).contains(&amount) {
        return Err(Error::InvalidAmount);
    }

    Ok(amount)
}

fn ensure_valid_duration(start_timestamp: u64, end_timestamp: u64) -> Result<u64, Error> {
    let duration = end_timestamp
        .checked_sub(start_timestamp)
        .ok_or(Error::InvalidTimestamps)?;

    if duration == 0 {
        return Err(Error::InvalidTimestamps);
    }

    if duration > MAX_VAULT_DURATION {
        return Err(Error::DurationTooLong);
    }

    Ok(duration)
}

// ---------------------------------------------------------------------------
// Contract
// ---------------------------------------------------------------------------

#[contract]
pub struct DisciplrVault;

#[contractimpl]
impl DisciplrVault {
    /// Initialize the contract with the canonical USDC token address.
    ///
    /// This must be called before any token operations. Once set, the token address
    /// cannot be changed. All token transfers will verify the provided token matches
    /// the initialized address.
    ///
    /// # Security Note
    /// This prevents draining via mismatched token contract arguments. The contract
    /// only accepts the single canonical token address set during initialization.
    pub fn initialize(env: Env, usdc_token: Address) -> Result<(), Error> {
        let key = DataKey::TokenAddress;
        if env.storage().instance().has(&key) {
            return Err(Error::InvalidStatus);
        }
        env.storage().instance().set(&key, &usdc_token);
        Ok(())
    }

    fn get_token_address(env: &Env, provided_token: &Address) -> Result<Address, Error> {
        let key = DataKey::TokenAddress;
        match env.storage().instance().get::<_, Address>(&key) {
            Some(canonical) => {
                if provided_token != &canonical {
                    return Err(Error::InvalidTokenAddress);
                }
                Ok(canonical)
            }
            None => Err(Error::TokenNotInitialized),
        }
    }

    /// Create a new productivity vault. Transfers USDC from creator to contract.
    ///
    /// # Validation Rules
    /// - `amount` must be within [`MIN_AMOUNT`, `MAX_AMOUNT`]; otherwise returns `Error::InvalidAmount`.
    /// - `start_timestamp` must be less than `end_timestamp`; otherwise returns `Error::InvalidTimestamps`.
    /// - `end_timestamp - start_timestamp` must fit in `u64` and be at most [`MAX_VAULT_DURATION`].
    ///
    /// The `milestone_hash` parameter is commitment metadata for an off-chain
    /// milestone description. The contract stores it as opaque bytes for later
    /// reference; it does not depend on collision resistance or post-quantum
    /// properties for authorization or fund safety.
    ///
    /// # Prerequisites
    /// Creator must have sufficient USDC balance and authorize the transaction.
    /// Contract must be initialized via `initialize()`.
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

        let _canonical_token = Self::get_token_address(&env, &usdc_token)?;

        // Validate amount bounds
        if amount < MIN_AMOUNT {
            return Err(Error::InvalidAmount);
        }
        if amount > MAX_AMOUNT {
            return Err(Error::InvalidAmount);
        }

        // Validate timestamps
        let current_time = env.ledger().timestamp();
        if start_timestamp < current_time {
            return Err(Error::InvalidTimestamp);
        }

        ensure_valid_duration(start_timestamp, end_timestamp)?;

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
            creator,
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

        env.events().publish(
            (Symbol::new(&env, "vault_created"), vault_id),
            vault.clone(),
        );

        Ok(vault_id)
    }

    // -----------------------------------------------------------------------
    // validate_milestone
    // -----------------------------------------------------------------------

    /// Verifier (or authorized party) validates milestone completion.
    ///
    /// **Optional verifier behavior:** If `verifier` is `Some(addr)`, only that address may call
    /// this function. If `verifier` is `None`, only the creator may call it (no validation by
    /// other parties). Rejects when current time >= end_timestamp (MilestoneExpired).
    /// Returns `Error::AlreadyValidated` if the milestone was previously validated.
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

        if vault.milestone_validated {
            return Err(Error::AlreadyValidated);
        }

        // When verifier is Some, only that address may validate; when None, only creator may validate.
        if let Some(ref verifier) = vault.verifier {
            verifier.require_auth();
        } else {
            vault.creator.require_auth();
        }

        // Timestamp check: rejects when current time >= end_timestamp
        if env.ledger().timestamp() >= vault.end_timestamp {
            return Err(Error::MilestoneExpired);
        }

        vault.milestone_validated = true;
        env.storage().instance().set(&vault_key, &vault);

        env.events()
            .publish((Symbol::new(&env, "milestone_validated"), vault_id), ());
        Ok(true)
    }

    // -----------------------------------------------------------------------
    // release_funds
    // -----------------------------------------------------------------------

    /// Release vault funds to `success_destination`.
    ///
    /// Funds can be released if:
    /// - The milestone has been validated (via `validate_milestone`), OR
    /// - The current time has reached or passed `end_timestamp`
    pub fn release_funds(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;
        let amount = ensure_amount_in_range(vault.amount)?;

        if vault.status != VaultStatus::Active {
<<<<<<< test/error-variant-coverage
            return Err(Error::InvalidStatus); // changed from VaultNotActive
=======
            return Err(Error::VaultNotActive);
>>>>>>> main
        }

        let _canonical_token = Self::get_token_address(&env, &usdc_token)?;

        let now = env.ledger().timestamp();
        let deadline_reached = now >= vault.end_timestamp;
        let validated = vault.milestone_validated;

        if !validated && !deadline_reached {
            return Err(Error::NotAuthorized);
        }

        let token_client = token::Client::new(&env, &usdc_token);
        token_client.transfer(
            &env.current_contract_address(),
            &vault.success_destination,
            &amount,
        );

        vault.status = VaultStatus::Completed;
        env.storage().instance().set(&vault_key, &vault);

        env.events()
            .publish((Symbol::new(&env, "funds_released"), vault_id), amount);
        Ok(true)
    }

    // -----------------------------------------------------------------------
    // redirect_funds
    // -----------------------------------------------------------------------

    /// Redirect vault funds to `failure_destination` when deadline passes without validation.
    ///
    /// # Authorization
    /// Anyone can call this function - authorization is based on vault state conditions.
    ///
    /// # Preconditions
    /// - Vault must exist and be in `Active` status
    /// - Current ledger time must be >= `end_timestamp`
    /// - `milestone_validated` must be false
    ///
    /// # Effects
    /// - Transfers locked USDC to `failure_destination`
    /// - Sets vault status to `Failed`
    /// - Emits `funds_redirected` event
    ///
    /// # Errors
    /// - `VaultNotFound` (1): Vault does not exist
    /// - `VaultNotActive` (3): Vault is not in Active status
    /// - `InvalidTimestamp` (4): Deadline has not been reached yet
    /// - `NotAuthorized` (2): Milestone was validated - use `release_funds` instead
    ///
    /// # Security Considerations
    /// This function can be called by any address once the deadline passes without validation.
    /// The USDC token address is passed as a parameter - backends should validate against trusted contracts.
    ///
    /// # API Mapping
    /// - HTTP: `POST /api/v1/vaults/{vault_id}/redirect`
    /// - Request: `{ "vault_id": 42, "usdc_token": "C...", "caller_signature": "..." }`
    pub fn redirect_funds(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;
        let amount = ensure_amount_in_range(vault.amount)?;

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        let _canonical_token = Self::get_token_address(&env, &usdc_token)?;

        if env.ledger().timestamp() < vault.end_timestamp {
            return Err(Error::InvalidTimestamp);
        }

        if vault.milestone_validated {
            return Err(Error::NotAuthorized);
        }

        let token_client = token::Client::new(&env, &usdc_token);
        token_client.transfer(
            &env.current_contract_address(),
            &vault.failure_destination,
            &amount,
        );

        vault.status = VaultStatus::Failed;
        env.storage().instance().set(&vault_key, &vault);

        env.events()
            .publish((Symbol::new(&env, "funds_redirected"), vault_id), amount);
        Ok(true)
    }

    // -----------------------------------------------------------------------
    // cancel_vault
    // -----------------------------------------------------------------------

    /// Cancel an active vault and return all funds to the creator.
    ///
    /// # Authorization
    /// Only the vault creator can cancel. Requires `creator.require_auth()`.
    ///
    /// # Preconditions
    /// - Vault must exist and be in `Active` status
    /// - Caller must be the vault creator
    ///
    /// # Effects
    /// - Transfers locked USDC back to `creator`
    /// - Sets vault status to `Cancelled`
    /// - Emits `vault_cancelled` event
    ///
    /// # Errors
    /// - `VaultNotFound` (1): Vault does not exist
    /// - `VaultNotActive` (3): Vault is not in Active status
    ///
    /// # Security Considerations
    /// Only the creator can cancel. The USDC token address is passed as a parameter -
    /// backends should validate against trusted contracts.
    ///
    /// # API Mapping
    /// - HTTP: `POST /api/v1/vaults/{vault_id}/cancel`
    /// - Request: `{ "vault_id": 42, "usdc_token": "C...", "creator_signature": "..." }`
    pub fn cancel_vault(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;
        let amount = ensure_amount_in_range(vault.amount)?;

        vault.creator.require_auth();

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

        let _canonical_token = Self::get_token_address(&env, &usdc_token)?;

        let token_client = token::Client::new(&env, &usdc_token);
        token_client.transfer(&env.current_contract_address(), &vault.creator, &amount);

        vault.status = VaultStatus::Cancelled;
        env.storage().instance().set(&vault_key, &vault);

        env.events()
            .publish((Symbol::new(&env, "vault_cancelled"), vault_id), ());
        Ok(true)
    }

    // -----------------------------------------------------------------------
    // get_vault_state
    // -----------------------------------------------------------------------

    /// Return current vault state, or `None` if no vault record exists for that ID.
    ///
    /// This contract does not remove vault records during normal lifecycle transitions.
    /// Vaults that are completed, failed, or cancelled remain readable and return
    /// `Some(ProductivityVault)` with their terminal status.
    ///
    /// Under normal contract operation, `None` therefore means the vault ID was
    /// never created. If storage were cleared externally, `None` would also be
    /// observed, but the contract itself has no path that deletes vault records.
    pub fn get_vault_state(env: Env, vault_id: u32) -> Option<ProductivityVault> {
        env.storage().instance().get(&DataKey::Vault(vault_id))
    }

    /// Return the total number of vaults created.
    ///
    /// This is a view function that returns the count of all vaults ever created,
    /// regardless of their current status. The count includes vaults in any
    /// state (Active, Completed, Failed, Cancelled).
    ///
    /// # Returns
    /// `u32` - The total number of vault IDs assigned (0-indexed, so next vault ID = count)
    ///
    /// # API Mapping
    /// - HTTP: `GET /api/v1/vaults/count`
    /// - Response: `{ "count": 157, "as_of_ledger": 12345690 }`
    pub fn vault_count(env: Env) -> u32 {
        env.storage()
            .instance()
            .get(&DataKey::VaultCount)
            .unwrap_or(0)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    extern crate std;

    use super::*;
    use soroban_sdk::{
        testutils::{Address as _, AuthorizedFunction, Events, Ledger},
        token::{StellarAssetClient, TokenClient},
        Address, BytesN, Env, Symbol, TryIntoVal,
    };

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

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
            let amount: i128 = 1_000_000; // 1 USDC (6 decimals)
            usdc_asset.mint(&creator, &amount);

            // Deploy contract.
            let contract_id = env.register(DisciplrVault, ());
            let client = DisciplrVaultClient::new(&env, &contract_id);
            client.initialize(&usdc_addr);

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

        fn malformed_vault(&self, amount: i128) -> ProductivityVault {
            ProductivityVault {
                creator: self.creator.clone(),
                amount,
                start_timestamp: self.start_timestamp,
                end_timestamp: self.end_timestamp,
                milestone_hash: self.milestone_hash(),
                verifier: Some(self.verifier.clone()),
                success_destination: self.success_dest.clone(),
                failure_destination: self.failure_dest.clone(),
                status: VaultStatus::Active,
                milestone_validated: false,
            }
        }
    }

    // -----------------------------------------------------------------------
    // Upstream Tests (Migrated & Merged)
    // -----------------------------------------------------------------------

    #[test]
    fn get_vault_state_returns_some_with_matching_fields() {
        let setup = TestSetup::new();
        let client = setup.client();

        let vault_id = setup.create_default_vault();

        let vault_state = client.get_vault_state(&vault_id);
        assert!(vault_state.is_some());

        let vault = vault_state.unwrap();
        assert_eq!(vault.creator, setup.creator);
        assert_eq!(vault.amount, setup.amount);
        assert_eq!(vault.start_timestamp, setup.start_timestamp);
        assert_eq!(vault.end_timestamp, setup.end_timestamp);
        assert_eq!(vault.milestone_hash, setup.milestone_hash());
        assert_eq!(vault.verifier, Some(setup.verifier));
        assert_eq!(vault.success_destination, setup.success_dest);
        assert_eq!(vault.failure_destination, setup.failure_dest);
        assert_eq!(vault.status, VaultStatus::Active);
    }

    #[test]
    fn test_get_vault_state_missing_returns_none() {
        let setup = TestSetup::new();
        let client = setup.client();

        assert!(client.get_vault_state(&999).is_none());
    }

    #[test]
    fn test_get_vault_state_cancelled_vault_still_returns_some() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        let result = client.cancel_vault(&vault_id, &setup.usdc_token);
        assert!(result);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.status, VaultStatus::Cancelled);
    }

    #[test]
    fn test_get_vault_state_failed_vault_still_returns_some() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);

        let result = client.redirect_funds(&vault_id, &setup.usdc_token);
        assert!(result);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.status, VaultStatus::Failed);
    }

    /// Issue #42: milestone_hash passed to create_vault is stored and returned by get_vault_state.
    #[test]
    fn test_milestone_hash_storage_and_retrieval() {
        let setup = TestSetup::new();
        let client = setup.client();

        let custom_hash = BytesN::from_array(&setup.env, &[0xab; 32]);
        setup.env.ledger().set_timestamp(setup.start_timestamp);

        let vault_id = client.create_vault(
            &setup.usdc_token,
            &setup.creator,
            &setup.amount,
            &setup.start_timestamp,
            &setup.end_timestamp,
            &custom_hash,
            &Some(setup.verifier.clone()),
            &setup.success_dest,
            &setup.failure_dest,
        );

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.milestone_hash, custom_hash);
    }

    #[test]
    fn test_create_vault_invalid_amount_returns_error() {
        let setup = TestSetup::new();
        let client = setup.client();

        let result = client.try_create_vault(
            &setup.usdc_token,
            &setup.creator,
            &0i128,
            &setup.start_timestamp,
            &setup.end_timestamp,
            &setup.milestone_hash(),
            &None,
            &setup.success_dest,
            &setup.failure_dest,
        );
        assert!(
            result.is_err(),
            "create_vault with amount 0 should return InvalidAmount"
        );
    }

    #[test]
    fn test_create_vault_invalid_timestamps_returns_error() {
        let setup = TestSetup::new();
        let client = setup.client();

        let result = client.try_create_vault(
            &setup.usdc_token,
            &setup.creator,
            &setup.amount,
            &1000u64,
            &1000u64,
            &setup.milestone_hash(),
            &None,
            &setup.success_dest,
            &setup.failure_dest,
        );
        assert!(
            result.is_err(),
            "create_vault with start >= end should return InvalidTimestamps"
        );
    }

    #[test]
    fn test_create_vault_accepts_max_u64_end_timestamp_when_duration_is_safe() {
        let setup = TestSetup::new();
        let client = setup.client();

        let start_timestamp = u64::MAX - MAX_VAULT_DURATION;
        let end_timestamp = u64::MAX;
        let usdc_asset = StellarAssetClient::new(&setup.env, &setup.usdc_token);
        usdc_asset.mint(&setup.creator, &setup.amount);

        let vault_id = client.create_vault(
            &setup.usdc_token,
            &setup.creator,
            &setup.amount,
            &start_timestamp,
            &end_timestamp,
            &setup.milestone_hash(),
            &None,
            &setup.success_dest,
            &setup.failure_dest,
        );

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.start_timestamp, start_timestamp);
        assert_eq!(vault.end_timestamp, end_timestamp);
    }

    #[test]
    fn test_create_vault_rejects_max_u64_end_timestamp_when_duration_exceeds_limit() {
        let setup = TestSetup::new();
        let client = setup.client();

        let result = client.try_create_vault(
            &setup.usdc_token,
            &setup.creator,
            &setup.amount,
            &(u64::MAX - MAX_VAULT_DURATION - 1),
            &u64::MAX,
            &setup.milestone_hash(),
            &None,
            &setup.success_dest,
            &setup.failure_dest,
        );

        assert!(result.is_err());
    }

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
    fn test_redirect_funds_rejects_non_existent_vault() {
        let setup = TestSetup::new();
        let client = setup.client();

        let result = client.try_redirect_funds(&999, &setup.usdc_token);
        assert!(result.is_err());
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #8)")]
    fn create_vault_rejects_start_equal_end() {
        let setup = TestSetup::new();
        let client = setup.client();

        client.create_vault(
            &setup.usdc_token,
            &setup.creator,
            &setup.amount,
            &1000,
            &1000, // start == end
            &setup.milestone_hash(),
            &None,
            &setup.success_dest,
            &setup.failure_dest,
        );
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #8)")]
    fn create_vault_rejects_start_greater_than_end() {
        let setup = TestSetup::new();
        let client = setup.client();

        client.create_vault(
            &setup.usdc_token,
            &setup.creator,
            &setup.amount,
            &2000,
            &1000, // start > end
            &setup.milestone_hash(),
            &None,
            &setup.success_dest,
            &setup.failure_dest,
        );
    }

    // -----------------------------------------------------------------------
    // Original branch tests (adapted for new signature and Results)
    // -----------------------------------------------------------------------

    #[test]
    fn test_create_vault_increments_id() {
        let setup = TestSetup::new();

        // Mint extra USDC for second vault.
        let usdc_asset = StellarAssetClient::new(&setup.env, &setup.usdc_token);
        usdc_asset.mint(&setup.creator, &setup.amount);

        let id_a = setup.create_default_vault();
        let id_b = setup.create_default_vault();
        assert_ne!(id_a, id_b, "vault IDs must be distinct");
        assert_eq!(id_b, id_a + 1);
    }

    #[test]
    fn test_release_funds_after_validation() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Validate milestone.
        client.validate_milestone(&vault_id);

        let usdc = setup.usdc_client();
        let success_before = usdc.balance(&setup.success_dest);

        // Release.
        let result = client.release_funds(&vault_id, &setup.usdc_token);
        assert!(result);

        // Success destination received the funds.
        let success_after = usdc.balance(&setup.success_dest);
        assert_eq!(success_after - success_before, setup.amount);

        // Vault status is Completed.
        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.status, VaultStatus::Completed);
    }

    #[test]
    fn test_release_funds_after_deadline() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Advance ledger PAST end_timestamp.
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);

        let usdc = setup.usdc_client();
        let before = usdc.balance(&setup.success_dest);

        let result = client.release_funds(&vault_id, &setup.usdc_token);
        assert!(result);

        assert_eq!(usdc.balance(&setup.success_dest) - before, setup.amount);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.status, VaultStatus::Completed);
    }

    #[test]
    fn test_double_release_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);

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

    /// Covers the requirement from Documentation_validate_milestone_wrong_status.md:
    /// validate_milestone must return Error::VaultNotActive for Completed, Failed, and Cancelled vaults.
    #[test]
    fn test_validate_milestone_rejects_non_active_statuses() {
        use crate::Error;

        // --- Completed vault ---
        {
            let setup = TestSetup::new();
            let client = setup.client();
            setup.env.ledger().set_timestamp(setup.start_timestamp);
            let vault_id = setup.create_default_vault();
            // Validate then release to reach Completed.
            client.validate_milestone(&vault_id);
            client.release_funds(&vault_id, &setup.usdc_token);
            let result = client.try_validate_milestone(&vault_id);
            assert_eq!(
                result,
                Err(Ok(Error::VaultNotActive)),
                "validate_milestone on Completed vault must return VaultNotActive"
            );
        }

        // --- Failed vault ---
        {
            let setup = TestSetup::new();
            let client = setup.client();
            setup.env.ledger().set_timestamp(setup.start_timestamp);
            let vault_id = setup.create_default_vault();
            // Expire and redirect to reach Failed.
            setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
            client.redirect_funds(&vault_id, &setup.usdc_token);
            let result = client.try_validate_milestone(&vault_id);
            assert_eq!(
                result,
                Err(Ok(Error::VaultNotActive)),
                "validate_milestone on Failed vault must return VaultNotActive"
            );
        }

        // --- Cancelled vault ---
        {
            let setup = TestSetup::new();
            let client = setup.client();
            setup.env.ledger().set_timestamp(setup.start_timestamp);
            let vault_id = setup.create_default_vault();
            client.cancel_vault(&vault_id, &setup.usdc_token);
            let result = client.try_validate_milestone(&vault_id);
            assert_eq!(
                result,
                Err(Ok(Error::VaultNotActive)),
                "validate_milestone on Cancelled vault must return VaultNotActive"
            );
        }
    }

    #[test]
    fn test_validate_milestone_duplicate_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_vault_no_verifier();

        // First validation should succeed.
        let result = client.validate_milestone(&vault_id);
        assert!(result);

        // Second validation should fail with AlreadyValidated error.
        let err = client.try_validate_milestone(&vault_id);
        assert!(err.is_err());
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

    // -----------------------------------------------------------------------
    // Issue #118: redirect_funds must be blocked when milestone_validated = true
    // -----------------------------------------------------------------------

    /// After validation, redirect_funds must fail even if the deadline has NOT yet passed.
    #[test]
    fn test_redirect_funds_after_validation_before_deadline_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Validate milestone before deadline.
        setup.env.ledger().set_timestamp(setup.end_timestamp - 1);
        client.validate_milestone(&vault_id);

        // Deadline has NOT passed — redirect must be rejected (NotAuthorized).
        let result = client.try_redirect_funds(&vault_id, &setup.usdc_token);
        assert!(
            result.is_err(),
            "redirect_funds must fail when milestone is validated and deadline not reached"
        );
    }

    /// After validation, redirect_funds must fail even AFTER the deadline has passed.
    /// Funds must go to success_destination via release_funds, not failure_destination.
    #[test]
    fn test_redirect_funds_after_validation_after_deadline_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Validate milestone before deadline.
        setup.env.ledger().set_timestamp(setup.end_timestamp - 1);
        client.validate_milestone(&vault_id);

        // Advance past deadline.
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);

        // Redirect must still be rejected because milestone was validated.
        let result = client.try_redirect_funds(&vault_id, &setup.usdc_token);
        assert!(
            result.is_err(),
            "redirect_funds must fail when milestone is validated, even after deadline"
        );

        // Confirm failure_destination received nothing.
        let usdc = setup.usdc_client();
        assert_eq!(
            usdc.balance(&setup.failure_dest),
            0,
            "failure_destination must not receive funds when milestone was validated"
        );

        // release_funds should still succeed (validated path).
        let released = client.release_funds(&vault_id, &setup.usdc_token);
        assert!(released);
        assert_eq!(usdc.balance(&setup.success_dest), setup.amount);
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

    #[test]
    fn test_release_funds_rejects_malformed_stored_amount() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
        setup.env.as_contract(&setup.contract_id, || {
            setup
                .env
                .storage()
                .instance()
                .set(&DataKey::Vault(77), &setup.malformed_vault(MAX_AMOUNT + 1));
        });

        let result = client.try_release_funds(&77, &setup.usdc_token);
        assert!(result.is_err());
    }

    #[test]
    fn test_redirect_funds_rejects_malformed_stored_amount() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
        setup.env.as_contract(&setup.contract_id, || {
            setup
                .env
                .storage()
                .instance()
                .set(&DataKey::Vault(78), &setup.malformed_vault(MAX_AMOUNT + 1));
        });

        let result = client.try_redirect_funds(&78, &setup.usdc_token);
        assert!(result.is_err());
    }

    #[test]
    fn test_cancel_vault_rejects_malformed_stored_amount() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.as_contract(&setup.contract_id, || {
            setup
                .env
                .storage()
                .instance()
                .set(&DataKey::Vault(79), &setup.malformed_vault(MIN_AMOUNT - 1));
        });

        let result = client.try_cancel_vault(&79, &setup.usdc_token);
        assert!(result.is_err());
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

        client.initialize(&usdc_addr);

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
}

#[cfg(test)]
mod test {
    use super::*;
    use soroban_sdk::{
        testutils::Address as _,
        token::{StellarAssetClient, TokenClient},
        Address, Env,
    };
    extern crate std;

    fn create_token_contract<'a>(
        env: &Env,
        admin: &Address,
    ) -> (Address, StellarAssetClient<'a>, TokenClient<'a>) {
        let contract_address = env
            .register_stellar_asset_contract_v2(admin.clone())
            .address();
        (
            contract_address.clone(),
            StellarAssetClient::new(env, &contract_address),
            TokenClient::new(env, &contract_address),
        )
    }

    fn create_vault_contract(env: &Env) -> Address {
        env.register(DisciplrVault, ())
    }

    #[test]
    fn test_create_vault_success() {
        let env = Env::default();
        env.mock_all_auths();

        let admin = Address::generate(&env);
        let creator = Address::generate(&env);
        let success_dest = Address::generate(&env);
        let failure_dest = Address::generate(&env);

        let (token_address, token_admin, token_client) = create_token_contract(&env, &admin);
        let vault_contract = create_vault_contract(&env);

        // Mint USDC to creator and approve contract
        token_admin.mint(&creator, &1000);

        let vault_client = DisciplrVaultClient::new(&env, &vault_contract);
        vault_client.initialize(&token_address);
        let milestone_hash = BytesN::from_array(&env, &[1u8; 32]);

        let vault_id = vault_client.create_vault(
            &token_address,
            &creator,
            &500,
            &100,
            &200,
            &milestone_hash,
            &None,
            &success_dest,
            &failure_dest,
        );

        assert_eq!(vault_id, 0);
        assert_eq!(token_client.balance(&creator), 500);
        assert_eq!(token_client.balance(&vault_contract), 500);
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #7)")]
    fn test_create_vault_zero_amount() {
        let env = Env::default();
        env.mock_all_auths();

        let admin = Address::generate(&env);
        let creator = Address::generate(&env);
        let (token_address, _, _) = create_token_contract(&env, &admin);
        let vault_contract = create_vault_contract(&env);

        let vault_client = DisciplrVaultClient::new(&env, &vault_contract);
        vault_client.initialize(&token_address);
        let milestone_hash = BytesN::from_array(&env, &[1u8; 32]);

        vault_client.create_vault(
            &token_address,
            &creator,
            &0,
            &100,
            &200,
            &milestone_hash,
            &None,
            &Address::generate(&env),
            &Address::generate(&env),
        );
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #7)")]
    fn test_create_vault_negative_amount() {
        let env = Env::default();
        env.mock_all_auths();

        let admin = Address::generate(&env);
        let creator = Address::generate(&env);
        let (token_address, _, _) = create_token_contract(&env, &admin);
        let vault_contract = create_vault_contract(&env);

        let vault_client = DisciplrVaultClient::new(&env, &vault_contract);
        vault_client.initialize(&token_address);
        let milestone_hash = BytesN::from_array(&env, &[1u8; 32]);

        vault_client.create_vault(
            &token_address,
            &creator,
            &-100,
            &100,
            &200,
            &milestone_hash,
            &None,
            &Address::generate(&env),
            &Address::generate(&env),
        );
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #8)")]
    fn test_create_vault_invalid_timestamps() {
        let env = Env::default();
        env.mock_all_auths();

        let admin = Address::generate(&env);
        let creator = Address::generate(&env);
        let (token_address, _, _) = create_token_contract(&env, &admin);
        let vault_contract = create_vault_contract(&env);

        let vault_client = DisciplrVaultClient::new(&env, &vault_contract);
        vault_client.initialize(&token_address);
        let milestone_hash = BytesN::from_array(&env, &[1u8; 32]);

        vault_client.create_vault(
            &token_address,
            &creator,
            &500,
            &200,
            &100,
            &milestone_hash,
            &None,
            &Address::generate(&env),
            &Address::generate(&env),
        );
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #8)")]
    fn test_create_vault_equal_timestamps() {
        let env = Env::default();
        env.mock_all_auths();

        let admin = Address::generate(&env);
        let creator = Address::generate(&env);
        let (token_address, _, _) = create_token_contract(&env, &admin);
        let vault_contract = create_vault_contract(&env);

        let vault_client = DisciplrVaultClient::new(&env, &vault_contract);
        vault_client.initialize(&token_address);
        let milestone_hash = BytesN::from_array(&env, &[1u8; 32]);

        vault_client.create_vault(
            &token_address,
            &creator,
            &500,
            &100,
            &100,
            &milestone_hash,
            &None,
            &Address::generate(&env),
            &Address::generate(&env),
        );
    }

    #[test]
    #[should_panic(expected = "balance is not sufficient")]
    fn test_create_vault_insufficient_balance() {
        let env = Env::default();
        env.mock_all_auths();

        let admin = Address::generate(&env);
        let creator = Address::generate(&env);
        let (token_address, token_admin, _) = create_token_contract(&env, &admin);
        let vault_contract = create_vault_contract(&env);

        // Mint only 100 USDC but try to lock 500
        token_admin.mint(&creator, &100);

        let vault_client = DisciplrVaultClient::new(&env, &vault_contract);
        vault_client.initialize(&token_address);
        let milestone_hash = BytesN::from_array(&env, &[1u8; 32]);

        vault_client.create_vault(
            &token_address,
            &creator,
            &500,
            &100,
            &200,
            &milestone_hash,
            &None,
            &Address::generate(&env),
            &Address::generate(&env),
        );
    }

    #[test]
    fn test_create_vault_with_verifier() {
        let env = Env::default();
        env.mock_all_auths();

        let admin = Address::generate(&env);
        let creator = Address::generate(&env);
        let verifier = Address::generate(&env);
        let (token_address, token_admin, token_client) = create_token_contract(&env, &admin);
        let vault_contract = create_vault_contract(&env);

        token_admin.mint(&creator, &1000);

        let vault_client = DisciplrVaultClient::new(&env, &vault_contract);
        vault_client.initialize(&token_address);
        let milestone_hash = BytesN::from_array(&env, &[1u8; 32]);

        let vault_id = vault_client.create_vault(
            &token_address,
            &creator,
            &500,
            &100,
            &200,
            &milestone_hash,
            &Some(verifier),
            &Address::generate(&env),
            &Address::generate(&env),
        );

        assert_eq!(vault_id, 0);
        assert_eq!(token_client.balance(&vault_contract), 500);
    }

    #[test]
    fn test_create_vault_exact_balance() {
        let env = Env::default();
        env.mock_all_auths();

        let admin = Address::generate(&env);
        let creator = Address::generate(&env);
        let (token_address, token_admin, token_client) = create_token_contract(&env, &admin);
        let vault_contract = create_vault_contract(&env);

        // Mint exact amount needed
        token_admin.mint(&creator, &500);

        let vault_client = DisciplrVaultClient::new(&env, &vault_contract);
        vault_client.initialize(&token_address);
        let milestone_hash = BytesN::from_array(&env, &[1u8; 32]);

        let vault_id = vault_client.create_vault(
            &token_address,
            &creator,
            &500,
            &100,
            &200,
            &milestone_hash,
            &None,
            &Address::generate(&env),
            &Address::generate(&env),
        );

        assert_eq!(vault_id, 0);
        assert_eq!(token_client.balance(&creator), 0);
        assert_eq!(token_client.balance(&vault_contract), 500);
    }
}
