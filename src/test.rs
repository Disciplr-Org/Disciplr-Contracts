#![cfg(test)]

use crate::{DisciplrVault, DisciplrVaultClient, ProductivityVault, VaultStatus};
use soroban_sdk::{
    testutils::{Address as _, Ledger, LedgerInfo},
    token, Address, BytesN, Env,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Spin up a fresh environment with a mock USDC token and the vault contract.
/// Returns (env, vault_client, token_admin_client, token_client, token_address).
fn setup() -> (
    Env,
    DisciplrVaultClient<'static>,
    token::StellarAssetClient<'static>,
    token::Client<'static>,
    Address,
) {
    let env = Env::default();
    // Mock all auth so we don't have to sign manually in tests.
    env.mock_all_auths();

    // Set a baseline ledger timestamp.
    env.ledger().set(LedgerInfo {
        timestamp: 1_000_000,
        protocol_version: 22,
        sequence_number: 100,
        network_id: [0u8; 32],
        base_reserve: 10,
        min_temp_entry_ttl: 1_000_000,
        min_persistent_entry_ttl: 1_000_000,
        max_entry_ttl: 3_110_400,
    });

    // Deploy a mock Stellar asset (USDC stand-in).
    let token_admin = Address::generate(&env);
    let token_address = env
        .register_stellar_asset_contract_v2(token_admin.clone())
        .address();
    let token_admin_client = token::StellarAssetClient::new(&env, &token_address);
    let token_client = token::Client::new(&env, &token_address);

    // Deploy the vault contract.
    let vault_address = env.register(DisciplrVault, ());
    let vault_client = DisciplrVaultClient::new(&env, &vault_address);

    // Initialise contract with the token address.
    vault_client.initialize(&token_address);

    (
        env,
        vault_client,
        token_admin_client,
        token_client,
        token_address,
    )
}

/// Convenience: generate a dummy 32-byte milestone hash.
fn dummy_hash(env: &Env) -> BytesN<32> {
    BytesN::from_array(env, &[0xABu8; 32])
}

// ---------------------------------------------------------------------------
// Integration test: Create → Cancel
// ---------------------------------------------------------------------------

#[test]
fn test_create_and_cancel_vault() {
    let (env, client, admin_client, token_client, _token_addr) = setup();

    let creator = Address::generate(&env);
    let success_dest = Address::generate(&env);
    let failure_dest = Address::generate(&env);

    // Mint 1 000 USDC to creator.
    admin_client.mint(&creator, &1_000);

    // Sanity check initial balance.
    assert_eq!(token_client.balance(&creator), 1_000);

    // 1. Create vault locking 500 USDC.
    let vault_id = client.create_vault(
        &creator,
        &500,
        &1_000_000,           // start = current ledger timestamp
        &(1_000_000 + 86400), // end = +24 h
        &dummy_hash(&env),
        &None::<Address>,
        &success_dest,
        &failure_dest,
    );
    assert_eq!(vault_id, 0);

    // Verify balances after creation.
    assert_eq!(token_client.balance(&creator), 500);
    assert_eq!(token_client.balance(&client.address), 500);

    // Verify vault state.
    let vault: ProductivityVault = client.get_vault_state(&vault_id).unwrap();
    assert_eq!(vault.status, VaultStatus::Active);
    assert_eq!(vault.amount, 500);
    assert_eq!(vault.creator, creator);

    // 2. Cancel the vault.
    let cancelled = client.cancel_vault(&vault_id);
    assert!(cancelled);

    // Verify funds returned to creator.
    assert_eq!(token_client.balance(&creator), 1_000);
    assert_eq!(token_client.balance(&client.address), 0);

    // Verify vault status is Cancelled.
    let vault: ProductivityVault = client.get_vault_state(&vault_id).unwrap();
    assert_eq!(vault.status, VaultStatus::Cancelled);
}

// ---------------------------------------------------------------------------
// Integration test: Create → Validate Milestone (happy path)
// ---------------------------------------------------------------------------

#[test]
fn test_create_and_validate_milestone() {
    let (env, client, admin_client, token_client, _) = setup();

    let creator = Address::generate(&env);
    let verifier = Address::generate(&env);
    let success_dest = Address::generate(&env);
    let failure_dest = Address::generate(&env);

    admin_client.mint(&creator, &1_000);

    let vault_id = client.create_vault(
        &creator,
        &750,
        &1_000_000,
        &(1_000_000 + 86400),
        &dummy_hash(&env),
        &Some(verifier.clone()),
        &success_dest,
        &failure_dest,
    );

    // Validate milestone (verifier-approved).
    let validated = client.validate_milestone(&vault_id);
    assert!(validated);

    // Funds should be at the success destination.
    assert_eq!(token_client.balance(&success_dest), 750);
    assert_eq!(token_client.balance(&client.address), 0);

    // Status should be Completed.
    let vault = client.get_vault_state(&vault_id).unwrap();
    assert_eq!(vault.status, VaultStatus::Completed);
}

// ---------------------------------------------------------------------------
// Integration test: Create → Redirect (deadline expired)
// ---------------------------------------------------------------------------

#[test]
fn test_create_and_redirect_after_deadline() {
    let (env, client, admin_client, token_client, _) = setup();

    let creator = Address::generate(&env);
    let success_dest = Address::generate(&env);
    let failure_dest = Address::generate(&env);

    admin_client.mint(&creator, &1_000);

    let vault_id = client.create_vault(
        &creator,
        &600,
        &1_000_000,
        &(1_000_000 + 86400),
        &dummy_hash(&env),
        &None::<Address>,
        &success_dest,
        &failure_dest,
    );

    // Advance ledger past the deadline.
    env.ledger().set(LedgerInfo {
        timestamp: 1_000_000 + 86400 + 1, // 1 second past deadline
        protocol_version: 22,
        sequence_number: 101,
        network_id: [0u8; 32],
        base_reserve: 10,
        min_temp_entry_ttl: 1_000_000,
        min_persistent_entry_ttl: 1_000_000,
        max_entry_ttl: 3_110_400,
    });

    let redirected = client.redirect_funds(&vault_id);
    assert!(redirected);

    // Funds should be at the failure destination.
    assert_eq!(token_client.balance(&failure_dest), 600);
    assert_eq!(token_client.balance(&client.address), 0);

    let vault = client.get_vault_state(&vault_id).unwrap();
    assert_eq!(vault.status, VaultStatus::Failed);
}

// ---------------------------------------------------------------------------
// Vault counter / multiple vaults
// ---------------------------------------------------------------------------

#[test]
fn test_vault_counter_increments() {
    let (env, client, admin_client, _token_client, _) = setup();

    let creator = Address::generate(&env);
    let dest = Address::generate(&env);
    admin_client.mint(&creator, &10_000);

    assert_eq!(client.vault_count(), 0);

    let id0 = client.create_vault(
        &creator,
        &100,
        &1_000_000,
        &2_000_000,
        &dummy_hash(&env),
        &None::<Address>,
        &dest,
        &dest,
    );
    assert_eq!(id0, 0);
    assert_eq!(client.vault_count(), 1);

    let id1 = client.create_vault(
        &creator,
        &200,
        &1_000_000,
        &2_000_000,
        &dummy_hash(&env),
        &None::<Address>,
        &dest,
        &dest,
    );
    assert_eq!(id1, 1);
    assert_eq!(client.vault_count(), 2);
}

// ---------------------------------------------------------------------------
// Negative / edge-case tests
// ---------------------------------------------------------------------------

/// Cancelling an already-cancelled vault should panic.
#[test]
#[should_panic(expected = "vault is not active")]
fn test_cancel_already_cancelled_vault() {
    let (env, client, admin_client, _token_client, _) = setup();
    let creator = Address::generate(&env);
    let dest = Address::generate(&env);
    admin_client.mint(&creator, &1_000);

    let vault_id = client.create_vault(
        &creator,
        &500,
        &1_000_000,
        &2_000_000,
        &dummy_hash(&env),
        &None::<Address>,
        &dest,
        &dest,
    );
    client.cancel_vault(&vault_id);
    // Second cancel must fail.
    client.cancel_vault(&vault_id);
}

/// Validating a completed vault should panic.
#[test]
#[should_panic(expected = "vault is not active")]
fn test_validate_completed_vault() {
    let (env, client, admin_client, _token_client, _) = setup();
    let creator = Address::generate(&env);
    let dest = Address::generate(&env);
    admin_client.mint(&creator, &1_000);

    let vault_id = client.create_vault(
        &creator,
        &500,
        &1_000_000,
        &2_000_000,
        &dummy_hash(&env),
        &None::<Address>,
        &dest,
        &dest,
    );
    client.validate_milestone(&vault_id);
    // Second validation must fail.
    client.validate_milestone(&vault_id);
}

/// Cannot validate milestone after the deadline.
#[test]
#[should_panic(expected = "deadline has passed")]
fn test_validate_after_deadline() {
    let (env, client, admin_client, _token_client, _) = setup();
    let creator = Address::generate(&env);
    let dest = Address::generate(&env);
    admin_client.mint(&creator, &1_000);

    let vault_id = client.create_vault(
        &creator,
        &500,
        &1_000_000,
        &(1_000_000 + 86400),
        &dummy_hash(&env),
        &None::<Address>,
        &dest,
        &dest,
    );

    // Move past deadline.
    env.ledger().set(LedgerInfo {
        timestamp: 1_000_000 + 86400 + 1,
        protocol_version: 22,
        sequence_number: 101,
        network_id: [0u8; 32],
        base_reserve: 10,
        min_temp_entry_ttl: 1_000_000,
        min_persistent_entry_ttl: 1_000_000,
        max_entry_ttl: 3_110_400,
    });

    client.validate_milestone(&vault_id);
}

/// Cannot redirect funds before the deadline.
#[test]
#[should_panic(expected = "deadline has not passed yet")]
fn test_redirect_before_deadline() {
    let (env, client, admin_client, _token_client, _) = setup();
    let creator = Address::generate(&env);
    let dest = Address::generate(&env);
    admin_client.mint(&creator, &1_000);

    let vault_id = client.create_vault(
        &creator,
        &500,
        &1_000_000,
        &(1_000_000 + 86400),
        &dummy_hash(&env),
        &None::<Address>,
        &dest,
        &dest,
    );

    // Timestamp is still within window – should panic.
    client.redirect_funds(&vault_id);
}

/// Creating a vault with zero amount should panic.
#[test]
#[should_panic(expected = "amount must be positive")]
fn test_create_vault_zero_amount() {
    let (env, client, _admin_client, _token_client, _) = setup();
    let creator = Address::generate(&env);
    let dest = Address::generate(&env);

    client.create_vault(
        &creator,
        &0,
        &1_000_000,
        &2_000_000,
        &dummy_hash(&env),
        &None::<Address>,
        &dest,
        &dest,
    );
}

/// Creating a vault with end_timestamp <= start_timestamp should panic.
#[test]
#[should_panic(expected = "end must be after start")]
fn test_create_vault_invalid_timestamps() {
    let (env, client, _admin_client, _token_client, _) = setup();
    let creator = Address::generate(&env);
    let dest = Address::generate(&env);

    client.create_vault(
        &creator,
        &100,
        &2_000_000,
        &1_000_000, // end before start
        &dummy_hash(&env),
        &None::<Address>,
        &dest,
        &dest,
    );
}

/// Querying a non-existent vault returns None.
#[test]
fn test_get_nonexistent_vault() {
    let (_env, client, _admin_client, _token_client, _) = setup();
    assert!(client.get_vault_state(&999).is_none());
}

/// Re-initialising the contract should panic.
#[test]
#[should_panic(expected = "already initialized")]
fn test_double_initialize() {
    let (_env, client, _admin_client, _token_client, token_addr) = setup();
    // `setup()` already called initialize. Calling again must fail.
    client.initialize(&token_addr);
}
