# Disciplr Vault Contract Documentation

## Overview

The Disciplr Vault is a Soroban smart contract deployed on the Stellar blockchain that enables **programmable time-locked USDC vaults** for productivity-based milestone funding. It allows creators to lock USDC tokens with specific milestones and conditions, ensuring funds are only released upon verified completion or redirected to a failure destination if milestones are not met.

### Use Cases

- **Vesting schedules**: Lock tokens that vest over time based on milestone completion
- **Grant funding**: Enable grant providers to fund projects with accountability
- **Team incentives**: Align team compensation with deliverable completion
- **Bug bounties**: Create time-bound bounty programs with predefined payout conditions

---

## Data Model

### VaultStatus Enum

Represents the current state of a vault:

```rust
#[contracttype]
pub enum VaultStatus {
    Active = 0,      // Vault created and funds locked
    Completed = 1,  // Milestone validated, funds released to success destination
    Failed = 2,     // Milestone not completed by deadline, funds redirected
    Cancelled = 3,  // Vault cancelled by creator, funds returned
}
```

| Status | Description |
|--------|-------------|
| `Active` | Vault is live, waiting for milestone validation or deadline |
| `Completed` | Milestone verified, funds released to success destination |
| `Failed` | Deadline passed without validation, funds redirected |
| `Cancelled` | Creator cancelled vault, funds returned |

### ProductivityVault Struct

The main data structure representing a vault:

```rust
#[contracttype]
pub struct ProductivityVault {
    pub creator: Address,           // Address that created the vault
    pub amount: i128,                // Amount of USDC locked (in stroops)
    pub start_timestamp: u64,       // Unix timestamp when vault becomes active
    pub end_timestamp: u64,          // Unix deadline for milestone validation
    pub milestone_hash: BytesN<32>, // SHA-256 hash of milestone requirements
    pub verifier: Option<Address>,  // Optional trusted verifier address
    pub success_destination: Address, // Address for fund release on success
    pub failure_destination: Address, // Address for fund redirect on failure
    pub status: VaultStatus,        // Current vault status
}
```

| Field | Type | Description |
|-------|------|-------------|
| `creator` | `Address` | Wallet address that created the vault |
| `amount` | `i128` | Total USDC amount locked (in stroops, 1 USDC = 10^7 stroops) |
| `start_timestamp` | `u64` | Unix timestamp (seconds) when vault becomes active |
| `end_timestamp` | `u64` | Unix timestamp (seconds) deadline for milestone validation |
| `milestone_hash` | `BytesN<32>` | SHA-256 hash documenting milestone requirements |
| `verifier` | `Option<Address>` | Optional trusted party who can validate milestones |
| `success_destination` | `Address` | Recipient address on successful milestone completion |
| `failure_destination` | `Address` | Recipient address when milestone is not completed |
| `status` | `VaultStatus` | Current lifecycle state of the vault |

---

## Contract Methods

### `create_vault`

Creates a new productivity vault and locks USDC funds.

```rust
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
) -> u32
```

**Parameters:**
- `creator`: Address of the vault creator (must authorize transaction)
- `amount`: USDC amount to lock (in stroops)
- `start_timestamp`: When vault becomes active (unix seconds)
- `end_timestamp`: Deadline for milestone validation (unix seconds)
- `milestone_hash`: SHA-256 hash of milestone document
- `verifier`: Optional verifier address (None = anyone can validate)
- `success_destination`: Address to receive funds on success
- `failure_destination`: Address to receive funds on failure

**Returns:** `u32` - Unique vault identifier

**Requirements:**
- Caller must authorize the transaction (`creator.require_auth()`)
- `end_timestamp` must be greater than `start_timestamp`
- USDC transfer must be approved by creator before calling

**Emits:** [`vault_created`](#vault_created) event

---

### `validate_milestone`

Allows the verifier (or authorized party) to validate milestone completion and release funds.

```rust
pub fn validate_milestone(env: Env, vault_id: u32) -> bool
```

**Parameters:**
- `vault_id`: ID of the vault to validate

**Returns:** `bool` - True if validation successful

**Requirements (TODO):**
- Vault must exist and be in `Active` status
- Caller must be the designated verifier (if set)
- Current timestamp must be before `end_timestamp`

**Emits:** [`milestone_validated`](#milestone_validated) event

---

### `release_funds`

Releases locked funds to the success destination (typically after validation).

```rust
pub fn release_funds(env: Env, vault_id: u32) -> bool
```

**Parameters:**
- `vault_id`: ID of the vault to release funds from

**Returns:** `bool` - True if release successful

**Requirements (TODO):**
- Vault status must be `Active`
- Caller must be authorized (verifier or contract logic)
- Transfers USDC to `success_destination`
- Sets status to `Completed`

---

### `redirect_funds`

Redirects funds to the failure destination when milestone is not completed by deadline.

```rust
pub fn redirect_funds(env: Env, vault_id: u32) -> bool
```

**Parameters:**
- `vault_id`: ID of the vault to redirect funds from

**Returns:** `bool` - True if redirect successful

**Requirements (TODO):**
- Vault status must be `Active`
- Current timestamp must be past `end_timestamp`
- Transfers USDC to `failure_destination`
- Sets status to `Failed`

---

### `cancel_vault`

Allows the creator to cancel the vault and retrieve locked funds.

```rust
pub fn cancel_vault(env: Env, vault_id: u32) -> bool
```

**Parameters:**
- `vault_id`: ID of the vault to cancel

**Returns:** `bool` - True if cancellation successful

**Requirements (TODO):**
- Caller must be the vault creator
- Vault status must be `Active`
- Returns USDC to creator
- Sets status to `Cancelled`

---

### `get_vault_state`

Retrieves the current state of a vault.

```rust
pub fn get_vault_state(env: Env, vault_id: u32) -> Option<ProductivityVault>
```

**Parameters:**
- `vault_id`: ID of the vault to query

**Returns:** `Option<ProductivityVault>` - Stored vault data when a record exists for that ID.

**Behavior:** Created vault records are not deleted during normal contract execution. Completed, failed, and cancelled vaults still return `Some(ProductivityVault)` with their terminal status. `None` therefore means the ID was never assigned (`vault_id >= vault_count()`) or storage was cleared outside the contract's normal lifecycle.

---

## Events

### `vault_created`

Emitted when a new vault is created.

**Topic:**
```
("vault_created", vault_id)
```

**Data:**
```rust
ProductivityVault {
    creator: Address,
    amount: i128,
    start_timestamp: u64,
    end_timestamp: u64,
    milestone_hash: BytesN<32>,
    verifier: Option<Address>,
    success_destination: Address,
    failure_destination: Address,
    status: VaultStatus::Active,
}
```

---

### `milestone_validated`

Emitted when a milestone is successfully validated.

**Topic:**
```
("milestone_validated", vault_id)
```

**Data:** `()` (empty tuple)

---

## Lifecycle

```
                    ┌──────────────┐
                    │   CREATED    │
                    │              │
                    │ create_vault │
                    └──────┬───────┘
                           │
                           ▼
                    ┌──────────────┐
         ┌─────────│    ACTIVE    │─────────┐
         │         │              │         │
         │         └──────────────┘         │
         │                                    │
         ▼                                    ▼
┌─────────────────┐              ┌─────────────────────┐
│ validate_       │              │  redirect_funds     │
│ milestone()     │              │  (deadline passed)  │
└────────┬────────┘              └──────────┬──────────┘
         │                                   │
         ▼                                   ▼
┌─────────────────┐              ┌─────────────────────┐
│   COMPLETED    │              │      FAILED        │
│                │              │                     │
└─────────────────┘              └─────────────────────┘

         │
         ▼
┌─────────────────┐
│ cancel_vault()  │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│   CANCELLED    │
│                │
└─────────────────┘
```

---

## Security and Trust Model

This section outlines the security assumptions, trust model, and known limitations of the Disciplr Vault contract. For production USDC issuer and admin assumptions, also review [USDC_INTEGRATION.md](USDC_INTEGRATION.md).

### Trust Model

1. **Verifier Trust (Critical)**: When a `verifier` is designated, that address has decisive power over milestone validation before the deadline.
2. **Creator Power**: If no `verifier` is set, only the `creator` can validate the milestone. The `creator` can also cancel an active vault and reclaim funds.
3. **Immutable Destinations**: `success_destination` and `failure_destination` are fixed at vault creation.
4. **No Administrative Override Inside Disciplr**: The contract has no owner role that can arbitrarily sweep funds outside the encoded lifecycle.

### Security Assumptions

1. **Stellar Ledger Integrity**: Soroban authorization and storage semantics are assumed to be enforced correctly.
2. **Ledger Timestamp Reliability**: Time-based logic depends on `env.ledger().timestamp()`.
3. **Token Contract Behavior**: The integrated USDC token contract is assumed to implement the expected Soroban token interface correctly.
4. **Issuer / Admin Powers Remain External**: Disciplr does not remove or constrain powers held by the underlying USDC issuer or asset administrator.

### Known Limitations and Risks

1. **Per-Call Token Address**: `usdc_token` is passed into release, redirect, and cancel flows instead of being pinned into vault state.
2. **External Asset Governance Risk**: A vault can be locally valid while the external asset is frozen, paused, blacklisted, migrated, or otherwise restricted by issuer policy.
3. **CEI Pattern Deviation**: Some methods transfer tokens before updating internal status. Soroban atomicity reduces risk, but stricter checks-effects-interactions ordering would still be preferable.
4. **No Emergency Pause**: There is currently no circuit breaker for operational emergencies.

### Recommendations for Integration

- Use a well-reviewed production USDC asset and verify its issuer/admin model.
- Use a multisig verifier for higher-value vaults.
- Treat issuer rotations, admin-key changes, and asset migrations as security-significant events.
- Ensure the off-chain milestone document represented by `milestone_hash` is clear and durable.

---

## Usage Examples

### Example 1: Create a Milestone-Based Funding Vault

A project owner wants to lock 1000 USDC for a bug bounty program with a 30-day deadline.

```rust
// Parameters
let creator: Address = Address::from_string("GA7..."); // Creator wallet
let amount: i128 = 1000 * 10_000_000; // 1000 USDC in stroops
let start_timestamp: u64 = 1704067200; // Jan 1, 2024 00:00:00 UTC
let end_timestamp: u64 = 1706640000;    // Jan 30, 2024 00:00:00 UTC (30 days)

// Hash of milestone requirements (off-chain document)
let milestone_hash: BytesN<32> = BytesN::from_array(&env, &[
    0x4d, 0x69, 0x6c, 0x65, 0x73, 0x74, 0x6f, 0x6e,
    0x65, 0x5f, 0x72, 0x65, 0x71, 0x75, 0x69, 0x72,
    0x65, 0x6d, 0x65, 0x6e, 0x74, 0x73, 0x5f, 0x68,
    0x61, 0x73, 0x68, 0x5f, 0x65, 0x78, 0x61, 0x6d
]);

let verifier: Option<Address> = Some(Address::from_string("GB7..."));
let success_destination: Address = Address::from_string("GC7..."); // Project wallet
let failure_destination: Address = Address::from_string("GD7..."); // Funder wallet

// Create vault
let vault_id = DisciplrVaultClient::new(&env, &contract_address)
    .create_vault(
        &creator,
        &amount,
        &start_timestamp,
        &end_timestamp,
        &milestone_hash,
        &verifier,
        &success_destination,
        &failure_destination,
    );
// vault_id = 0
```

### Example 2: Validate Milestone and Release Funds

The verifier validates that milestone requirements were met and releases funds.

```rust
let verifier: Address = Address::from_string("GB7..."); // Designated verifier

let result = DisciplrVaultClient::new(&env, &contract_address)
    .with_source_account(&verifier)
    .validate_milestone(&vault_id);
// result = true

// Funds now transferred to success_destination
// Vault status changed to Completed
```

### Example 3: Handle Deadline Without Validation

After the deadline passes without milestone validation, funds are redirected.

```rust
// Assume end_timestamp has passed and no validation occurred

let result = DisciplrVaultClient::new(&env, &contract_address)
    .redirect_funds(&vault_id);
// result = true

// Funds transferred to failure_destination
// Vault status changed to Failed
```

### Example 4: Cancel Vault Before Deadline

Creator decides to cancel the vault before the deadline.

```rust
let creator: Address = Address::from_string("GA7..."); // Original creator

let result = DisciplrVaultClient::new(&env, &contract_address)
    .with_source_account(&creator)
    .cancel_vault(&vault_id);
// result = true

// Funds returned to creator
// Vault status changed to Cancelled
```

### Example 5: Query Vault State

Check the current state of a vault.

```rust
let vault_state = DisciplrVaultClient::new(&env, &contract_address)
    .get_vault_state(&vault_id);

// Returns Some(ProductivityVault) or None
match vault_state {
    Some(vault) => {
        // Access vault fields
        let current_status = vault.status;
        let amount_locked = vault.amount;
    }
    None => {
        // Vault not found or not initialized
    }
}
```

---

## Testing

Run the test suite to verify contract functionality:

```bash
cargo test
```

Expected output should include tests for:
- Vault creation with valid parameters
- Vault creation authorization
- Event emission on vault creation
- Milestone validation logic
- Fund release and redirect logic
- Vault cancellation
- State retrieval

---

## File Structure

```
disciplr-contracts/
├── src/
│   └── lib.rs           # DisciplrVault contract implementation
├── Cargo.toml           # Project dependencies
├── README.md            # Project overview
└── vesting.md           # This documentation
```

---

## Related Documentation

- [Soroban SDK Documentation](https://developers.stellar.org/docs/smart-contracts)
- [Stellar Smart Contracts Guide](https://developers.stellar.org/docs/smart-contracts/getting-started)
- [Token Interface (Soroban)](https://developers.stellar.org/docs/tokens)

---

## Changelog

| Version | Changes |
|---------|---------|
| 0.1.0 | Initial release with basic vault structure, stubbed implementations |
