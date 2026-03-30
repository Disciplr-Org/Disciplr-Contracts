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

| Status      | Description                                                 |
| ----------- | ----------------------------------------------------------- |
| `Active`    | Vault is live, waiting for milestone validation or deadline |
| `Completed` | Milestone verified, funds released to success destination   |
| `Failed`    | Deadline passed without validation, funds redirected        |
| `Cancelled` | Creator cancelled vault, funds returned                     |

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
    pub milestone_validated: bool,  // True if milestone has been verified
}
```

| Field                 | Type              | Description                                                  |
| --------------------- | ----------------- | ------------------------------------------------------------ |
| `creator`             | `Address`         | Wallet address that created the vault                        |
| `amount`              | `i128`            | Total USDC amount locked (in stroops, 1 USDC = 10^7 stroops) |
| `start_timestamp`     | `u64`             | Unix timestamp (seconds) when vault becomes active           |
| `end_timestamp`       | `u64`             | Unix timestamp (seconds) deadline for milestone validation   |
| `milestone_hash`      | `BytesN<32>`      | SHA-256 hash documenting milestone requirements              |
| `verifier`            | `Option<Address>` | Optional trusted party who can validate milestones           |
| `success_destination` | `Address`         | Recipient address on successful milestone completion         |
| `failure_destination` | `Address`         | Recipient address when milestone is not completed            |
| `status`              | `VaultStatus`     | Current lifecycle state of the vault                         |
| `milestone_validated` | `bool`            | Internal flag indicating milestone completion                |

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

- `usdc_token`: Address of the USDC token contract
- `creator`: Address of the vault creator
- `amount`: USDC amount to lock (must be within `MIN_AMOUNT` and `MAX_AMOUNT`)
- `start_timestamp`: When vault becomes active (must not be in the past)
- `end_timestamp`: Deadline for milestone validation
- `milestone_hash`: SHA-256 hash of milestone document
- `verifier`: Optional verifier address (None = creator validates)
- `success_destination`: Address to receive funds on success
- `failure_destination`: Address to receive funds on failure

**Returns:** `Result<u32, Error>` - Unique vault identifier or an Error

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

**Returns:** `Result<bool, Error>` - True if validation successful

**Requirements:**

- Vault must exist and be in `Active` status
- Caller must be the designated verifier (or creator if no verifier set)
- Current timestamp must be before `end_timestamp`

**Emits:** [`milestone_validated`](#milestone_validated) event

---

### `release_funds`

Releases locked funds to the success destination (typically after validation).

```rust
pub fn release_funds(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error>
```

**Parameters:**

- `vault_id`: ID of the vault to release funds from
- `usdc_token`: Address of the USDC token contract

**Returns:** `Result<bool, Error>` - True if release successful

**Requirements:**

- Vault status must be `Active`
- Release is authorized if milestone is validated OR deadline has passed
- Transfers USDC to `success_destination`
- Sets status to `Completed`

---

### `redirect_funds`

Redirects funds to the failure destination when milestone is not completed by deadline.

```rust
pub fn redirect_funds(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error>
```

**Parameters:**

- `vault_id`: ID of the vault to redirect funds from
- `usdc_token`: Address of the USDC token contract

**Returns:** `Result<bool, Error>` - True if redirect successful

**Requirements:**

- Vault status must be `Active`
- Current timestamp must be past `end_timestamp`
- Milestone must NOT have been validated
- Transfers USDC to `failure_destination`
- Sets status to `Failed`

---

### `cancel_vault`

Allows the creator to cancel the vault and retrieve locked funds.

```rust
pub fn cancel_vault(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error>
```

**Parameters:**

- `vault_id`: ID of the vault to cancel
- `usdc_token`: Address of the USDC token contract

**Returns:** `Result<bool, Error>` - True if cancellation successful

**Requirements:**

- Caller must be the original vault creator
- Vault status must be `Active`
- Returns locked USDC to creator
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

```text
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

```text
("milestone_validated", vault_id)
```

**Data:** `()` (empty tuple)

---

## Lifecycle

```text
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

This section outlines the security properties, trust assumptions, and known limitations of the Disciplr Vault contract. It is intended for auditors, developers, and users to understand the risks and guarantees provided by the system.

### Security and Trust Analysis

1. **Absolute Verifier Power**: If a `verifier` is designated (via `Some(Address)`), they hold absolute power over the milestone validation process. The contract cannot verify off-chain project completion; it relies entirely on the `verifier`'s authorization. For high-value vaults, we recommend using a multisig address or a DAO-controlled contract address as the `verifier`.
2. **Creator Authority**: The `creator` is the only address authorized to `create_vault` or `cancel_vault`. They must authorize the initial USDC funding. If no `verifier` is set (`None`), only the `creator` can validate the milestone.
3. **Immutable Destinations**: Once a vault is created, the `success_destination` and `failure_destination` are fixed and cannot be changed. This prevents "bait and switch" attacks on destination addresses.
4. **No Administrative Overrides**: There is no "admin" or "owner" role with the power to sweep funds or override the vault logic. Funds are strictly bound by the `end_timestamp` and authorization rules.

### External Dependencies

1. **USDC Token Contract**: The contract interacts with an external USDC token address (Stellar Asset Contract). The security of the vault depends on the integrity and availability of this external contract.
2. **Ledger Reliability**: The contract relies on the Stellar network's ledger timestamp for all timing constraints (`start_timestamp`, `end_timestamp`). We assume ledger timestamps are reasonably accurate and monotonic.

### Automated Checks

- **Double Release/Redirect Protection**: The contract checks the `status` (must be `Active`) before every state mutation, ensuring a vault cannot be released twice or redirected after cancellation.
- **Timestamp Integrity**: Milestone validation is strictly prohibited once the ledger timestamp reaches or exceeds `end_timestamp`.
- **Authorization**: All state-changing methods enforce `require_auth()` for the appropriate actors (creator or verifier).

### Known Limitations & Risks

1. **USDC Token Address Check**: The `usdc_token` address is passed as an argument to release/redirect functions. Users should verify that the token address used for interactions matches the intended asset.
2. **Atomic Transfers**: Some methods initiate token transfers before updating the internal status. While Soroban's atomicity mitigates traditional reentrancy risks, future versions may adopt the strict Checks-Effects-Interactions (CEI) pattern.
3. **No Emergency Stop**: There is currently no circuit breaker or emergency pause mechanism.

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
        let _current_status = vault.status;
        let _amount_locked = vault.amount;
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

| Version | Changes                                                             |
| ------- | ------------------------------------------------------------------- |
| 0.1.0   | Initial release with basic vault structure, stubbed implementations |
