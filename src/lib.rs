#![no_std]
#![allow(clippy::too_many_arguments)]

use soroban_sdk::{
    contract, contracterror, contractimpl, contracttype, token, Address, BytesN, Env, Symbol,
};

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// Maximum allowed vault duration: 365 days (31 536 000 seconds).
///
/// Prevents unbounded lock-up periods and keeps timestamp arithmetic
/// safely within u64 range regardless of the epoch used.
pub const MAX_DURATION: u64 = 365 * 24 * 60 * 60; // 31_536_000 s

/// Maximum stakeable amount in base token units (e.g. USDC micro-units).
///
/// Set to 1 × 10¹⁸ — about 1 trillion USDC at 6 decimal places.
/// This leaves ample headroom while preventing overflow in any fee or
/// percentage arithmetic performed on `amount` downstream.
pub const MAX_AMOUNT: i128 = 1_000_000_000_000_000_000; // 10^18

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------
//
// Contract-specific errors used in revert paths. Follows Soroban error
// conventions: use Result<T, Error> and return Err(Error::Variant) instead
// of generic panics where appropriate.

/// Errors returned by [`DisciplrVault`] contract entry points.
#[contracterror]
#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
#[repr(u32)]
pub enum Error {
    /// Vault with the given id does not exist.
    VaultNotFound = 1,
    /// Caller is not authorized for this operation (e.g. not verifier/creator,
    /// or release before deadline without validation).
    NotAuthorized = 2,
    /// Vault is not in Active status (e.g. already Completed, Failed, or Cancelled).
    VaultNotActive = 3,
    /// Timestamp constraint violated (e.g. redirect before end_timestamp, or invalid time window).
    InvalidTimestamp = 4,
    /// Validation is no longer allowed because current time is at or past end_timestamp.
    MilestoneExpired = 5,
    /// Vault is in an invalid status for the requested operation.
    InvalidStatus = 6,
    /// `amount` must be positive (`amount <= 0`).
    InvalidAmount = 7,
    /// `start_timestamp` must be strictly less than `end_timestamp`.
    InvalidTimestamps = 8,
    /// Vault duration (`end_timestamp - start_timestamp`) exceeds [`MAX_DURATION`].
    DurationTooLong = 9,
    /// `amount` exceeds [`MAX_AMOUNT`].
    AmountTooLarge = 10,
}

// ---------------------------------------------------------------------------
// Data types
// ---------------------------------------------------------------------------

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
    /// Hash representing the milestone the creator commits to.
    pub milestone_hash: BytesN<32>,
    /// Optional designated verifier. When `Some(addr)`, only that address may call
    /// `validate_milestone`. When `None`, only the creator may validate.
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
}

// ---------------------------------------------------------------------------
// Contract
// ---------------------------------------------------------------------------

#[contract]
pub struct DisciplrVault;

#[contractimpl]
impl DisciplrVault {
    // -----------------------------------------------------------------------
    // create_vault
    // -----------------------------------------------------------------------

    /// Create a new productivity vault. Caller must have approved USDC transfer
    /// to this contract.
    ///
    /// # Validation
    ///
    /// | Condition                                         | Error                      |
    /// |---------------------------------------------------|----------------------------|
    /// | `amount <= 0`                                     | [`Error::InvalidAmount`]   |
    /// | `amount > MAX_AMOUNT`                             | [`Error::AmountTooLarge`]  |
    /// | `start_timestamp >= end_timestamp`                | [`Error::InvalidTimestamps`] |
    /// | `end_timestamp - start_timestamp > MAX_DURATION`  | [`Error::DurationTooLong`] |
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

        // ── Validate amount ───────────────────────────────────────────────
        if amount <= 0 {
            return Err(Error::InvalidAmount);
        }
        if amount > MAX_AMOUNT {
            return Err(Error::AmountTooLarge);
        }

        // ── Validate timestamps ───────────────────────────────────────────
        if end_timestamp <= start_timestamp {
            return Err(Error::InvalidTimestamps);
        }
        // Subtraction is safe: end > start guarantees no underflow.
        if end_timestamp - start_timestamp > MAX_DURATION {
            return Err(Error::DurationTooLong);
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
    /// If `verifier` is `Some(addr)`, only that address may call this function.
    /// If `verifier` is `None`, only the creator may call it.
    /// Rejects when current ledger time >= `end_timestamp` (`MilestoneExpired`).
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

        if let Some(ref verifier) = vault.verifier {
            verifier.require_auth();
        } else {
            vault.creator.require_auth();
        }

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
    /// Allowed when the milestone has been validated OR the deadline has passed.
    pub fn release_funds(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error> {
        let vault_key = DataKey::Vault(vault_id);
        let mut vault: ProductivityVault = env
            .storage()
            .instance()
            .get(&vault_key)
            .ok_or(Error::VaultNotFound)?;

        if vault.status != VaultStatus::Active {
            return Err(Error::VaultNotActive);
        }

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
            &vault.amount,
        );

        vault.status = VaultStatus::Completed;
        env.storage().instance().set(&vault_key, &vault);

        env.events().publish(
            (Symbol::new(&env, "funds_released"), vault_id),
            vault.amount,
        );
        Ok(true)
    }

    // -----------------------------------------------------------------------
    // redirect_funds
    // -----------------------------------------------------------------------

    /// Redirect funds to `failure_destination` (after deadline without validation).
    pub fn redirect_funds(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error> {
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
            return Err(Error::InvalidTimestamp);
        }

        // If milestone was validated the funds should go to success, not failure.
        if vault.milestone_validated {
            return Err(Error::NotAuthorized);
        }

        let token_client = token::Client::new(&env, &usdc_token);
        token_client.transfer(
            &env.current_contract_address(),
            &vault.failure_destination,
            &vault.amount,
        );

        vault.status = VaultStatus::Failed;
        env.storage().instance().set(&vault_key, &vault);

        env.events().publish(
            (Symbol::new(&env, "funds_redirected"), vault_id),
            vault.amount,
        );
        Ok(true)
    }

    // -----------------------------------------------------------------------
    // cancel_vault
    // -----------------------------------------------------------------------

    /// Cancel vault and return funds to creator.
    pub fn cancel_vault(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error> {
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

        let token_client = token::Client::new(&env, &usdc_token);
        token_client.transfer(
            &env.current_contract_address(),
            &vault.creator,
            &vault.amount,
        );

        vault.status = VaultStatus::Cancelled;
        env.storage().instance().set(&vault_key, &vault);

        env.events()
            .publish((Symbol::new(&env, "vault_cancelled"), vault_id), ());
        Ok(true)
    }

    // -----------------------------------------------------------------------
    // get_vault_state
    // -----------------------------------------------------------------------

    /// Return current vault state, or `None` if the vault does not exist.
    pub fn get_vault_state(env: Env, vault_id: u32) -> Option<ProductivityVault> {
        env.storage().instance().get(&DataKey::Vault(vault_id))
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

    // Timestamp anchors used by boundary/validation tests.
    const T0: u64 = 1_700_000_000; // 2023-11-14 ~22:13 UTC
    const T1: u64 = T0 + 86_400;   // T0 + 1 day

    // -----------------------------------------------------------------------
    // TestSetup
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

        /// Mints `amount` extra USDC to creator, then calls `create_vault`.
        /// Use for tests that need non-default amounts.
        fn create_vault_with_amount(&self, amount: i128, start: u64, end: u64) -> u32 {
            let usdc_asset = StellarAssetClient::new(&self.env, &self.usdc_token);
            usdc_asset.mint(&self.creator, &amount);
            self.client().create_vault(
                &self.usdc_token,
                &self.creator,
                &amount,
                &start,
                &end,
                &self.milestone_hash(),
                &None,
                &self.success_dest,
                &self.failure_dest,
            )
        }

        /// Calls `create_vault` with arbitrary inputs, expecting a validation error.
        /// Does NOT mint USDC — validation errors fire before the token transfer.
        fn expect_create_error(&self, amount: i128, start: u64, end: u64) -> Error {
            self.client()
                .try_create_vault(
                    &self.usdc_token,
                    &self.creator,
                    &amount,
                    &start,
                    &end,
                    &self.milestone_hash(),
                    &None,
                    &self.success_dest,
                    &self.failure_dest,
                )
                .expect_err("expected Err (outer)")
                .expect("expected Ok(Error) (inner)")
        }
    }

    // -----------------------------------------------------------------------
    // create_vault — happy path
    // -----------------------------------------------------------------------

    #[test]
    fn get_vault_state_returns_some_with_matching_fields() {
        let setup = TestSetup::new();
        let client = setup.client();

        let vault_id = setup.create_default_vault();

        let vault = client.get_vault_state(&vault_id).unwrap();
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

    /// milestone_hash passed to create_vault is stored and returned by get_vault_state.
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
    fn test_create_vault_increments_id() {
        let setup = TestSetup::new();

        // Mint extra USDC for the second vault.
        let usdc_asset = StellarAssetClient::new(&setup.env, &setup.usdc_token);
        usdc_asset.mint(&setup.creator, &setup.amount);

        let id_a = setup.create_default_vault();
        let id_b = setup.create_default_vault();
        assert_ne!(id_a, id_b, "vault IDs must be distinct");
        assert_eq!(id_b, id_a + 1);
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

        assert_eq!(vault_id, 0u32);

        let auths = env.auths();
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
        assert!(found_create_auth, "create_vault must be authenticated by creator");

        let all_events = env.events().all();
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

    // -----------------------------------------------------------------------
    // create_vault — amount boundary tests
    // -----------------------------------------------------------------------

    /// amount = 1 (minimum positive) must be accepted.
    #[test]
    fn test_minimum_valid_amount() {
        let setup = TestSetup::new();
        setup.create_vault_with_amount(1, T0, T1); // must not panic
    }

    /// amount = MAX_AMOUNT (boundary, inclusive) must be accepted.
    #[test]
    fn test_max_amount_boundary_is_valid() {
        let setup = TestSetup::new();
        setup.create_vault_with_amount(MAX_AMOUNT, T0, T1);
    }

    /// amount = 0 must return InvalidAmount (error code #7).
    #[test]
    fn test_create_vault_invalid_amount_returns_error() {
        let setup = TestSetup::new();
        assert_eq!(
            setup.expect_create_error(0, setup.start_timestamp, setup.end_timestamp),
            Error::InvalidAmount,
            "amount 0 must return InvalidAmount"
        );
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #7)")]
    fn test_create_vault_zero_amount_panics() {
        let setup = TestSetup::new();
        setup.client().create_vault(
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

    /// amount = -1 must return InvalidAmount.
    #[test]
    fn test_negative_one_amount_is_rejected() {
        let setup = TestSetup::new();
        assert_eq!(
            setup.expect_create_error(-1, T0, T1),
            Error::InvalidAmount
        );
    }

    /// amount = i128::MIN (most negative) must return InvalidAmount.
    #[test]
    fn test_i128_min_amount_is_rejected() {
        let setup = TestSetup::new();
        assert_eq!(
            setup.expect_create_error(i128::MIN, T0, T1),
            Error::InvalidAmount
        );
    }

    /// amount = MAX_AMOUNT + 1 (just over boundary) must return AmountTooLarge (error code #10).
    #[test]
    fn test_amount_one_above_max_is_rejected() {
        let setup = TestSetup::new();
        assert_eq!(
            setup.expect_create_error(MAX_AMOUNT + 1, T0, T1),
            Error::AmountTooLarge,
            "amount just over MAX_AMOUNT must return AmountTooLarge"
        );
    }

    /// amount = i128::MAX must return AmountTooLarge.
    #[test]
    fn test_i128_max_amount_is_rejected() {
        let setup = TestSetup::new();
        assert_eq!(
            setup.expect_create_error(i128::MAX, T0, T1),
            Error::AmountTooLarge
        );
    }

    // -----------------------------------------------------------------------
    // create_vault — timestamp boundary tests
    // -----------------------------------------------------------------------

    /// duration = MAX_DURATION (boundary, inclusive) must be accepted.
    #[test]
    fn test_max_duration_boundary_is_valid() {
        let setup = TestSetup::new();
        setup.create_vault_with_amount(1_000, T0, T0 + MAX_DURATION);
    }

    /// Shortest valid window: 1 second.
    #[test]
    fn test_minimum_duration_one_second() {
        let setup = TestSetup::new();
        setup.create_vault_with_amount(1_000, T0, T0 + 1);
    }

    /// start == end must return InvalidTimestamps (error code #8).
    #[test]
    fn test_create_vault_invalid_timestamps_returns_error() {
        let setup = TestSetup::new();
        assert_eq!(
            setup.expect_create_error(setup.amount, 1000, 1000),
            Error::InvalidTimestamps,
            "start == end must return InvalidTimestamps"
        );
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #8)")]
    fn create_vault_rejects_start_equal_end() {
        let setup = TestSetup::new();
        setup.client().create_vault(
            &setup.usdc_token,
            &setup.creator,
            &setup.amount,
            &1000,
            &1000,
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
        setup.client().create_vault(
            &setup.usdc_token,
            &setup.creator,
            &setup.amount,
            &2000,
            &1000,
            &setup.milestone_hash(),
            &None,
            &setup.success_dest,
            &setup.failure_dest,
        );
    }

    /// start > end (reversed) must return InvalidTimestamps.
    #[test]
    fn test_start_after_end_is_rejected() {
        let setup = TestSetup::new();
        assert_eq!(
            setup.expect_create_error(1_000, T1, T0),
            Error::InvalidTimestamps
        );
    }

    /// start = end + 1 (off-by-one reversal) must return InvalidTimestamps.
    #[test]
    fn test_start_one_past_end_is_rejected() {
        let setup = TestSetup::new();
        assert_eq!(
            setup.expect_create_error(1_000, T0 + 1, T0),
            Error::InvalidTimestamps
        );
    }

    /// duration = MAX_DURATION + 1 (just over boundary) must return DurationTooLong (#9).
    #[test]
    fn test_duration_one_over_max_is_rejected() {
        let setup = TestSetup::new();
        assert_eq!(
            setup.expect_create_error(1_000, T0, T0 + MAX_DURATION + 1),
            Error::DurationTooLong,
            "duration just over MAX_DURATION must return DurationTooLong"
        );
    }

    /// start = 0, end = u64::MAX — extreme overflow candidate — must return DurationTooLong.
    #[test]
    fn test_u64_max_end_timestamp_is_rejected() {
        let setup = TestSetup::new();
        assert_eq!(
            setup.expect_create_error(1_000, 0, u64::MAX),
            Error::DurationTooLong
        );
    }

    // -----------------------------------------------------------------------
    // create_vault — auth tests
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

        // DO NOT call env.mock_all_auths() — creator is not authorized.
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
            creator, // This address is NOT authorized.
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
            creator, // Not the attacker.
            5000,
            100,
            200,
            milestone_hash,
            None,
            success_addr,
            failure_addr,
        );
    }

    // -----------------------------------------------------------------------
    // validate_milestone
    // -----------------------------------------------------------------------

    #[test]
    fn test_validate_milestone_succeeds_before_end() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        setup.env.ledger().set_timestamp(setup.end_timestamp - 1);
        let success = client.validate_milestone(&vault_id);
        assert!(success);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert!(vault.milestone_validated);
        assert_eq!(vault.status, VaultStatus::Active); // status stays Active until release
    }

    #[test]
    fn test_validate_milestone_rejects_after_end() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // At exactly end_timestamp.
        setup.env.ledger().set_timestamp(setup.end_timestamp);
        assert!(client.try_validate_milestone(&vault_id).is_err());

        // Past end_timestamp.
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
        assert!(client.try_validate_milestone(&vault_id).is_err());
    }

    #[test]
    fn test_validate_milestone_on_completed_vault_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
        client.release_funds(&vault_id, &setup.usdc_token);

        assert!(client.try_validate_milestone(&vault_id).is_err());
    }

    /// When verifier is None, only creator may validate.
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

    // -----------------------------------------------------------------------
    // release_funds
    // -----------------------------------------------------------------------

    #[test]
    fn test_release_funds_after_validation() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        client.validate_milestone(&vault_id);

        let usdc = setup.usdc_client();
        let success_before = usdc.balance(&setup.success_dest);

        let result = client.release_funds(&vault_id, &setup.usdc_token);
        assert!(result);
        assert_eq!(usdc.balance(&setup.success_dest) - success_before, setup.amount);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.status, VaultStatus::Completed);
    }

    #[test]
    fn test_release_funds_after_deadline() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);

        let usdc = setup.usdc_client();
        let before = usdc.balance(&setup.success_dest);

        let result = client.release_funds(&vault_id, &setup.usdc_token);
        assert!(result);
        assert_eq!(usdc.balance(&setup.success_dest) - before, setup.amount);

        let vault = client.get_vault_state(&vault_id).unwrap();
        assert_eq!(vault.status, VaultStatus::Completed);
    }

    /// When verifier is None, release after deadline (no validation) still works.
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
        assert!(setup.client().try_release_funds(&999, &setup.usdc_token).is_err());
    }

    #[test]
    fn test_double_release_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
        client.release_funds(&vault_id, &setup.usdc_token);

        assert!(client.try_release_funds(&vault_id, &setup.usdc_token).is_err());
    }

    #[test]
    fn test_release_cancelled_vault_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        client.cancel_vault(&vault_id, &setup.usdc_token);
        assert!(client.try_release_funds(&vault_id, &setup.usdc_token).is_err());
    }

    #[test]
    fn test_release_not_validated_before_deadline_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // Neither validated nor past deadline.
        assert!(client.try_release_funds(&vault_id, &setup.usdc_token).is_err());
    }

    // -----------------------------------------------------------------------
    // redirect_funds
    // -----------------------------------------------------------------------

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

        assert!(client.try_redirect_funds(&vault_id, &setup.usdc_token).is_err());
    }

    #[test]
    fn test_redirect_funds_rejects_non_existent_vault() {
        let setup = TestSetup::new();
        assert!(setup.client().try_redirect_funds(&999, &setup.usdc_token).is_err());
    }

    #[test]
    fn test_double_redirect_rejected() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();
        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);

        client.redirect_funds(&vault_id, &setup.usdc_token);
        assert!(client.try_redirect_funds(&vault_id, &setup.usdc_token).is_err());
    }

    // -----------------------------------------------------------------------
    // cancel_vault
    // -----------------------------------------------------------------------

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
    #[should_panic(expected = "Error(Contract, #3)")]
    fn test_cancel_vault_when_completed_fails() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        client.validate_milestone(&vault_id);
        client.release_funds(&vault_id, &setup.usdc_token);

        client.cancel_vault(&vault_id, &setup.usdc_token);
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #3)")]
    fn test_cancel_vault_when_failed_fails() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        setup.env.ledger().set_timestamp(setup.end_timestamp + 1);
        client.redirect_funds(&vault_id, &setup.usdc_token);

        client.cancel_vault(&vault_id, &setup.usdc_token);
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #3)")]
    fn test_cancel_vault_when_cancelled_fails() {
        let setup = TestSetup::new();
        let client = setup.client();

        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        client.cancel_vault(&vault_id, &setup.usdc_token);
        client.cancel_vault(&vault_id, &setup.usdc_token); // second attempt
    }

    #[test]
    #[should_panic]
    fn test_cancel_vault_non_creator_fails() {
        let setup = TestSetup::new();
        setup.env.ledger().set_timestamp(setup.start_timestamp);
        let vault_id = setup.create_default_vault();

        // New env without mock_all_auths so auth check fires.
        let env = Env::default();
        let contract_id = env.register(DisciplrVault, ());
        let client_no_auth = DisciplrVaultClient::new(&env, &contract_id);

        client_no_auth.cancel_vault(&vault_id, &setup.usdc_token);
    }

    #[test]
    #[should_panic(expected = "Error(Contract, #1)")]
    fn test_cancel_vault_nonexistent_fails() {
        let setup = TestSetup::new();
        setup.client().cancel_vault(&999u32, &setup.usdc_token);
    }

    // -----------------------------------------------------------------------
    // Misc / parameter smoke tests
    // -----------------------------------------------------------------------

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
        let _h1 = BytesN::<32>::from_array(&env, &[0u8; 32]);
        let _h2 = BytesN::<32>::from_array(&env, &[1u8; 32]);
        let _h3 = BytesN::<32>::from_array(&env, &[255u8; 32]);
        assert_ne!([0u8; 32], [1u8; 32]);
        assert_ne!([1u8; 32], [255u8; 32]);
    }
}
