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
    pub creator: Address,              // Address that created the vault
    pub amount: i128,                  // Amount of USDC locked (in stroops)
    pub start_timestamp: u64,          // Unix timestamp when vault becomes active
    pub end_timestamp: u64,            // Unix deadline for milestone validation
    pub milestone_hash: BytesN<32>,    // SHA-256 hash of milestone requirements
    pub verifier: Option<Address>,     // Optional trusted verifier address
    pub success_destination: Address,  // Address for fund release on success
    pub failure_destination: Address,  // Address for fund redirect on failure
    pub status: VaultStatus,           // Current vault status
    pub milestone_validated: bool,     // True once validate_milestone succeeds
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
| `milestone_validated` | `bool` | Set to `true` once `validate_milestone` is called successfully |

---

## Contract Methods

### `create_vault`

Creates a new productivity vault and locks USDC funds.

```rust
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
) -> Result<u32, Error>
```

**Parameters:**
- `usdc_token`: Address of the USDC token contract (used to pull funds from creator)
- `creator`: Address of the vault creator (must authorize transaction)
- `amount`: USDC amount to lock (in stroops)
- `start_timestamp`: When vault becomes active (unix seconds)
- `end_timestamp`: Deadline for milestone validation (unix seconds)
- `milestone_hash`: SHA-256 hash of milestone document
- `verifier`: Optional verifier address (`None` = only the creator may validate)
- `success_destination`: Address to receive funds on success
- `failure_destination`: Address to receive funds on failure

**Returns:** `Result<u32, Error>` - `Ok(vault_id)` on success; unique vault identifier

**Requirements:**
- Caller must authorize the transaction (`creator.require_auth()`)
- `end_timestamp` must be greater than `start_timestamp`
- USDC transfer must be approved by creator before calling

**Emits:** [`vault_created`](#vault_created) event

---

### `validate_milestone`

Allows the verifier (or authorized party) to validate milestone completion and release funds.

```rust
pub fn validate_milestone(env: Env, vault_id: u32) -> Result<bool, Error>
```

**Parameters:**
- `vault_id`: ID of the vault to validate

**Returns:** `Result<bool, Error>` - `Ok(true)` if validation successful

**Requirements:**
- Vault must exist; otherwise returns `Error::VaultNotFound`
- Vault must be in `Active` status; otherwise returns `Error::VaultNotActive`
- If `verifier` is `Some(addr)`, only that address may call this; if `None`, only the creator may call it
- Current timestamp must be strictly before `end_timestamp`; otherwise returns `Error::MilestoneExpired`
- Sets `milestone_validated = true`; vault status remains `Active` until `release_funds` is called

**Emits:** [`milestone_validated`](#milestone_validated) event

---

### `release_funds`

Releases locked funds to the success destination (typically after validation or deadline reached).

```rust
pub fn release_funds(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error>
```

**Parameters:**
- `vault_id`: ID of the vault to release funds from
- `usdc_token`: Address of the USDC token contract

**Returns:** `Result<bool, Error>` - `Ok(true)` if release successful

**Requirements:**
- Vault must exist; otherwise returns `Error::VaultNotFound`
- Vault status must be `Active`; otherwise returns `Error::VaultNotActive`
- Either `milestone_validated == true` **or** `current timestamp >= end_timestamp`; otherwise returns `Error::NotAuthorized`
- No caller authorization required — release is state-driven
- Transfers USDC to `success_destination`; sets status to `Completed`

**Emits:** `funds_released` event with topic `(Symbol("funds_released"), vault_id)` and data `amount`.

---

### `redirect_funds`

Redirects funds to the failure destination when milestone is not completed by deadline.

```rust
pub fn redirect_funds(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error>
```

**Parameters:**
- `vault_id`: ID of the vault to redirect funds from
- `usdc_token`: Address of the USDC token contract

**Returns:** `Result<bool, Error>` - `Ok(true)` if redirect successful

**Requirements:**
- Vault must exist; otherwise returns `Error::VaultNotFound`
- Vault status must be `Active`; otherwise returns `Error::VaultNotActive`
- Current timestamp must be `>= end_timestamp`; otherwise returns `Error::InvalidTimestamp`
- `milestone_validated` must be `false`; if already validated returns `Error::NotAuthorized` (use `release_funds` instead)
- Transfers USDC to `failure_destination`; sets status to `Failed`

**Emits:** `funds_redirected` event with topic `(Symbol("funds_redirected"), vault_id)` and data `amount`.

---

### `cancel_vault`

Allows the creator to cancel the vault and retrieve locked funds.

```rust
pub fn cancel_vault(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error>
```

**Parameters:**
- `vault_id`: ID of the vault to cancel
- `usdc_token`: Address of the USDC token contract

**Returns:** `Result<bool, Error>` - `Ok(true)` if cancellation successful

**Requirements:**
- Caller must be the vault creator (`creator.require_auth()`)
- Vault status must be `Active`; otherwise returns `Error::VaultNotActive`
- Milestone must **not** have been validated; if `milestone_validated == true` returns `Error::MilestoneAlreadyValidated`
- Returns USDC to creator
- Sets status to `Cancelled`

**Emits:** `vault_cancelled` event with topic `(Symbol("vault_cancelled"), vault_id)` and data `()`.

> **Security note:** Once the verifier (or authorised party) has called
> `validate_milestone`, the escrow outcome is determined. The creator is
> blocked from cancelling so that validated funds can only flow to
> `success_destination` via `release_funds`. This preserves the escrow
> invariant and prevents a malicious or regretful creator from reclaiming
> funds after a valid completion has been certified.

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
                    │ create_vault │
                    └──────┬───────┘
                           │
                           ▼
                    ┌──────────────┐
         ┌─────────│    ACTIVE    │──────────────────────┐
         │         │              │                      │
         │         └──────┬───────┘                      │
         │                │                              │
         │        validate_milestone()                   │
         │         (sets milestone_validated=true)       │
         │                │                              │
         │                ▼                              ▼
         │         ┌──────────────┐         ┌──────────────────────┐
         │         │  VALIDATED   │         │  redirect_funds      │
         │         │ (still Active│         │  (deadline passed,   │
         │         │  flag only)  │         │   not validated)     │
         │         └──────┬───────┘         └──────────┬───────────┘
         │                │                            │
         │          release_funds()                    │
         │                │                            ▼
         │                ▼                 ┌──────────────────────┐
         │         ┌──────────────┐         │       FAILED         │
         │         │  COMPLETED   │         └──────────────────────┘
         │         └──────────────┘
         │
         │  cancel_vault()
         │  (only if milestone_validated == false)
         ▼
┌─────────────────┐
│   CANCELLED     │
└─────────────────┘
```

---

## Security and Trust Model


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
        &usdc_token,
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

// milestone_validated is now true; vault status is still Active
// Call release_funds to transfer funds to success_destination

let released = DisciplrVaultClient::new(&env, &contract_address)
    .release_funds(&vault_id, &usdc_token);
// released = true

// Funds now transferred to success_destination
// Vault status changed to Completed
```

### Example 3: Handle Deadline Without Validation

After the deadline passes without milestone validation, funds are redirected.

```rust
// Assume end_timestamp has passed and no validation occurred

let result = DisciplrVaultClient::new(&env, &contract_address)
    .redirect_funds(&vault_id, &usdc_token);
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
    .cancel_vault(&vault_id, &usdc_token);
// result = true

// Funds returned to creator
// Vault status changed to Cancelled
// Note: cancellation is only possible if milestone_validated == false
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
