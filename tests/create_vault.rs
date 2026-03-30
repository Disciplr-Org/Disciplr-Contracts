#![cfg(test)]

extern crate std;

use soroban_sdk::{
    testutils::{Address as _, Ledger},
    token::StellarAssetClient,
    Address, BytesN, Env,
};

use disciplr_vault::{
    DisciplrVault, DisciplrVaultClient, VaultStatus, MAX_AMOUNT, MAX_VAULT_DURATION, MIN_AMOUNT,
};

fn setup() -> (
    Env,
    DisciplrVaultClient<'static>,
    Address,
    StellarAssetClient<'static>,
) {
    let env = Env::default();
    env.mock_all_auths();

    let contract_id = env.register(DisciplrVault, ());
    let client = DisciplrVaultClient::new(&env, &contract_id);

    let usdc_admin = Address::generate(&env);
    let usdc_token = env.register_stellar_asset_contract_v2(usdc_admin.clone());
    let usdc_addr = usdc_token.address();
    let usdc_asset = StellarAssetClient::new(&env, &usdc_addr);

    (env, client, usdc_addr, usdc_asset)
}

#[test]
fn test_create_vault_valid_boundary_values() {
    let (env, client, usdc, usdc_asset) = setup();

    let creator = Address::generate(&env);
    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);

    usdc_asset.mint(&creator, &MIN_AMOUNT);

    let success = Address::generate(&env);
    let failure = Address::generate(&env);
    let milestone = BytesN::from_array(&env, &[0u8; 32]);

    let vault_id = client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &now,
        &(now + MAX_VAULT_DURATION),
        &milestone,
        &None,
        &success,
        &failure,
    );

    assert_eq!(vault_id, 0u32);
}

#[test]
#[should_panic(expected = "Error(Contract, #7)")]
fn test_amount_below_minimum() {
    let (env, client, usdc, _usdc_asset) = setup();

    let creator = Address::generate(&env);
    let now = env.ledger().timestamp();

    client.create_vault(
        &usdc,
        &creator,
        &(MIN_AMOUNT - 1),
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[0u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );
}

#[test]
#[should_panic(expected = "Error(Contract, #7)")]
fn test_amount_above_maximum() {
    let (env, client, usdc, _usdc_asset) = setup();

    let creator = Address::generate(&env);
    let now = env.ledger().timestamp();

    client.create_vault(
        &usdc,
        &creator,
        &(MAX_AMOUNT + 1),
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[0u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );
}

#[test]
#[should_panic(expected = "Error(Contract, #9)")]
fn test_duration_exceeds_max() {
    let (env, client, usdc, _usdc_asset) = setup();

    let creator = Address::generate(&env);
    let now = env.ledger().timestamp();

    client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &now,
        &(now + MAX_VAULT_DURATION + 1),
        &BytesN::from_array(&env, &[0u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );
}

#[test]
#[should_panic(expected = "Error(Contract, #4)")]
fn test_start_timestamp_in_past() {
    let (env, client, usdc, _usdc_asset) = setup();

    let creator = Address::generate(&env);
    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);

    client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &(now - 3_600),
        &(now + 86_400),
        &BytesN::from_array(&env, &[0u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );
}

#[test]
#[should_panic(expected = "Error(Contract, #8)")]
fn test_end_before_or_equal_start() {
    let (env, client, usdc, _usdc_asset) = setup();

    let creator = Address::generate(&env);
    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);

    client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &(now + 200),
        &(now + 100),
        &BytesN::from_array(&env, &[0u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );
}

#[test]
fn test_amount_exactly_max_allowed() {
    let (env, client, usdc, usdc_asset) = setup();

    let creator = Address::generate(&env);
    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);

    usdc_asset.mint(&creator, &MAX_AMOUNT);

    let vault_id = client.create_vault(
        &usdc,
        &creator,
        &MAX_AMOUNT,
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[0u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );

    assert_eq!(vault_id, 0u32);
}

#[test]
#[should_panic(expected = "Error(Contract, #7)")]
fn test_amount_zero() {
    let (env, client, usdc, _usdc_asset) = setup();

    let creator = Address::generate(&env);
    let now = env.ledger().timestamp();

    client.create_vault(
        &usdc,
        &creator,
        &0_i128,
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[0u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );
}

#[test]
fn test_minimum_valid_duration() {
    let (env, client, usdc, usdc_asset) = setup();

    let creator = Address::generate(&env);
    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);

    usdc_asset.mint(&creator, &MIN_AMOUNT);

    let vault_id = client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &now,
        &(now + 1),
        &BytesN::from_array(&env, &[0u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );

    assert_eq!(vault_id, 0u32);
}

#[test]
fn test_valid_zero_verifier_and_normal_duration() {
    let (env, client, usdc, usdc_asset) = setup();

    let creator = Address::generate(&env);
    let now = env.ledger().timestamp();

    usdc_asset.mint(&creator, &5_000_000_000_i128);

    client.create_vault(
        &usdc,
        &creator,
        &5_000_000_000_i128,
        &now,
        &(now + 7 * 24 * 60 * 60),
        &BytesN::from_array(&env, &[1u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );
}

#[test]
fn test_get_vault_state_never_created_id_returns_none() {
    let (_env, client, _usdc, _usdc_asset) = setup();

    assert_eq!(client.vault_count(), 0u32);
    assert!(client.get_vault_state(&0u32).is_none());
    assert!(client.get_vault_state(&42u32).is_none());
}

// ---------------------------------------------------------------------------
// Issue #124: success_destination vs failure_destination equality
// ---------------------------------------------------------------------------

/// Verifica que create_vault rechaza cuando success_destination == failure_destination.
/// Implicación UX: si ambas direcciones fueran iguales, el resultado de éxito y fracaso
/// sería indistinguible para el creador, eliminando el incentivo de cumplir el milestone.
#[test]
#[should_panic(expected = "Error(Contract, #10)")]
fn test_same_destination_rejected() {
    let (env, client, usdc, usdc_asset) = setup();

    let creator = Address::generate(&env);
    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);

    usdc_asset.mint(&creator, &MIN_AMOUNT);

    // Misma dirección para success y failure
    let same_dest = Address::generate(&env);

    client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[0u8; 32]),
        &None,
        &same_dest,
        &same_dest,
    );
}

/// Verifica que create_vault acepta cuando success_destination != failure_destination.
/// Caso explícito del constraint introducido en el issue #124.
#[test]
fn test_different_destinations_accepted() {
    let (env, client, usdc, usdc_asset) = setup();

    let creator = Address::generate(&env);
    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);

    usdc_asset.mint(&creator, &MIN_AMOUNT);

    let success = Address::generate(&env);
    let failure = Address::generate(&env);

    // Las dos direcciones son distintas: debe crearse sin error
    let vault_id = client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[0u8; 32]),
        &None,
        &success,
        &failure,
    );

    assert_eq!(vault_id, 0u32);

    let vault = client.get_vault_state(&vault_id).unwrap();
    assert_ne!(vault.success_destination, vault.failure_destination);
}

// ---------------------------------------------------------------------------
// Issue #125: Zero-address / dummy address validation
// ---------------------------------------------------------------------------

/// Verifica que create_vault rechaza cuando creator == success_destination.
/// Un creador que es también el destino de éxito puede recuperar fondos
/// trivialmente sin importar si completó el milestone.
#[test]
#[should_panic(expected = "Error(Contract, #11)")]
fn test_creator_as_success_destination_rejected() {
    let (env, client, usdc, usdc_asset) = setup();

    let creator = Address::generate(&env);
    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);

    usdc_asset.mint(&creator, &MIN_AMOUNT);

    let failure = Address::generate(&env);

    client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[0u8; 32]),
        &None,
        &creator, // success_destination == creator
        &failure,
    );
}

/// Verifica que create_vault rechaza cuando creator == failure_destination.
/// Un creador que es también el destino de fracaso recupera fondos
/// sin consecuencia por no completar el milestone.
#[test]
#[should_panic(expected = "Error(Contract, #11)")]
fn test_creator_as_failure_destination_rejected() {
    let (env, client, usdc, usdc_asset) = setup();

    let creator = Address::generate(&env);
    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);

    usdc_asset.mint(&creator, &MIN_AMOUNT);

    let success = Address::generate(&env);

    client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[0u8; 32]),
        &None,
        &success,
        &creator, // failure_destination == creator
    );
}

/// Verifica que create_vault rechaza cuando verifier == creator.
/// Un verificador igual al creador no provee validación independiente,
/// permitiendo al creador auto-validar y liberar fondos sin control externo.
#[test]
#[should_panic(expected = "Error(Contract, #11)")]
fn test_verifier_same_as_creator_rejected() {
    let (env, client, usdc, usdc_asset) = setup();

    let creator = Address::generate(&env);
    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);

    usdc_asset.mint(&creator, &MIN_AMOUNT);

    let success = Address::generate(&env);
    let failure = Address::generate(&env);

    client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[0u8; 32]),
        &Some(creator.clone()), // verifier == creator
        &success,
        &failure,
    );
}

/// Verifica que create_vault acepta cuando creator, verifier, success y failure
/// son todos direcciones distintas generadas independientemente.
#[test]
fn test_all_distinct_addresses_accepted() {
    let (env, client, usdc, usdc_asset) = setup();

    let creator = Address::generate(&env);
    let verifier = Address::generate(&env);
    let success = Address::generate(&env);
    let failure = Address::generate(&env);
    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);

    usdc_asset.mint(&creator, &MIN_AMOUNT);

    let vault_id = client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[0u8; 32]),
        &Some(verifier.clone()),
        &success,
        &failure,
    );

    assert_eq!(vault_id, 0u32);

    let vault = client.get_vault_state(&vault_id).unwrap();
    assert_ne!(vault.creator, vault.success_destination);
    assert_ne!(vault.creator, vault.failure_destination);
    assert_ne!(vault.success_destination, vault.failure_destination);
    assert_eq!(vault.verifier, Some(verifier));
}

#[test]
fn test_get_vault_state_cancelled_vault_remains_readable() {
    let (env, client, usdc, usdc_asset) = setup();

    let creator = Address::generate(&env);
    let now = 1_725_000_000u64;
    env.ledger().set_timestamp(now);
    usdc_asset.mint(&creator, &(MIN_AMOUNT * 2));

    let vault_id = client.create_vault(
        &usdc,
        &creator,
        &MIN_AMOUNT,
        &now,
        &(now + 86_400),
        &BytesN::from_array(&env, &[9u8; 32]),
        &None,
        &Address::generate(&env),
        &Address::generate(&env),
    );

    assert_eq!(client.vault_count(), 1u32);
    client.cancel_vault(&vault_id, &usdc);

    let vault = client.get_vault_state(&vault_id).unwrap();
    assert_eq!(vault.status, VaultStatus::Cancelled);
    assert!(client.get_vault_state(&1u32).is_none());
}
