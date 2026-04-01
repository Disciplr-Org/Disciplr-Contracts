# Disciplr Vault Contract Documentation

## Overview

The Disciplr Vault is a Soroban smart contract deployed on the Stellar blockchain that enables **programmable time-locked USDC vaults** for productivity-based milestone funding. It allows creators to lock USDC tokens with specific milestones and conditions, ensuring funds are only released upon verified completion or redirected to a failure destination if milestones are not met.

## Versioning Notice

The `DisciplrVault` contract includes a `version()` method to expose its current semantic version (as defined in `Cargo.toml`). Integrators should use this method to verify that the deployed bytecode matches the expected release.

```rust
pub fn version(env: Env) -> Symbol
```

The version string (e.g., `0.1.0`) maps directly to git tags in the repository (e.g., `v0.1.0`).

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
<<<<<<< doc/changelog
    pub milestone_hash: BytesN<32>, // Commitment metadata for milestone requirements
    pub verifier: Option<Address>,  // Optional trusted verifier address
    pub success_destination: Address, // Address for fund release on success
    pub failure_destination: Address, // Address for fund redirect on failure
    pub status: VaultStatus,          // Current lifecycle status
    pub milestone_validated: bool,    // True once verifier/creator calls validate_milestone
=======
    pub milestone_hash: BytesN<32>, // SHA-256 hash of milestone requirements
    pub verifier: Option<Address>,  // Optional trusted verifier address
    pub success_destination: Address, // Address for fund release on success
    pub failure_destination: Address, // Address for fund redirect on failure
    pub status: VaultStatus,        // Current vault status
>>>>>>> main
}
```

| Field | Type | Description |
|-------|------|-------------|
| `creator` | `Address` | Wallet address that created the vault |
| `amount` | `i128` | Total USDC amount locked (in stroops, 1 USDC = 10^7 stroops) |
| `start_timestamp` | `u64` | Unix timestamp (seconds) when vault becomes active |
| `end_timestamp` | `u64` | Unix timestamp (seconds) deadline for milestone validation |
<<<<<<< doc/changelog
| `milestone_hash` | `BytesN<32>` | Commitment metadata for an off-chain milestone description |
=======
| `milestone_hash` | `BytesN<32>` | SHA-256 hash documenting milestone requirements |
>>>>>>> main
| `verifier` | `Option<Address>` | Optional trusted party who can validate milestones |
| `success_destination` | `Address` | Recipient address on successful milestone completion |
| `failure_destination` | `Address` | Recipient address when milestone is not completed |
| `status` | `VaultStatus` | Current lifecycle state of the vault |
<<<<<<< doc/changelog
| `milestone_validated` | `bool` | Set to `true` once `validate_milestone` is called. Enables early fund release before deadline. |
=======
>>>>>>> main

---

## Contract Methods

### `create_vault`

Creates a new productivity vault and locks USDC funds.

```rust
pub fn create_vault(
    env: Env,
<<<<<<< doc/changelog
    usdc_token: Address,
=======
>>>>>>> main
    creator: Address,
    amount: i128,
    start_timestamp: u64,
    end_timestamp: u64,
    milestone_hash: BytesN<32>,
    verifier: Option<Address>,
    success_destination: Address,
    failure_destination: Address,
<<<<<<< doc/changelog
) -> Result<u32, Error>
```

**Parameters:**
- `usdc_token`: Address of the USDC token contract used for the transfer
=======
) -> u32
```

**Parameters:**
>>>>>>> main
- `creator`: Address of the vault creator (must authorize transaction)
- `amount`: USDC amount to lock (in stroops)
- `start_timestamp`: When vault becomes active (unix seconds)
- `end_timestamp`: Deadline for milestone validation (unix seconds)
<<<<<<< doc/changelog
- `milestone_hash`: commitment metadata for the off-chain milestone document
=======
- `milestone_hash`: SHA-256 hash of milestone document
>>>>>>> main
- `verifier`: Optional verifier address (None = anyone can validate)
- `success_destination`: Address to receive funds on success
- `failure_destination`: Address to receive funds on failure

<<<<<<< doc/changelog
**Returns:** `Result<u32, Error>` — unique vault ID on success

**Errors:**
- `Error::InvalidAmount` — `amount < MIN_AMOUNT` or `amount > MAX_AMOUNT`
- `Error::InvalidTimestamp` — `start_timestamp` is in the past
- `Error::InvalidTimestamps` — `end_timestamp <= start_timestamp`
- `Error::DurationTooLong` — duration exceeds `MAX_VAULT_DURATION`
=======
**Returns:** `u32` - Unique vault identifier

**Requirements:**
- Caller must authorize the transaction (`creator.require_auth()`)
- `end_timestamp` must be greater than `start_timestamp`
- USDC transfer must be approved by creator before calling
>>>>>>> main

**Emits:** [`vault_created`](#vault_created) event

---

### `validate_milestone`

<<<<<<< doc/changelog
Allows the verifier (or authorized party) to validate milestone completion.

```rust
pub fn validate_milestone(env: Env, vault_id: u32) -> Result<bool, Error>
=======
Allows the verifier (or authorized party) to validate milestone completion and release funds.

```rust
pub fn validate_milestone(env: Env, vault_id: u32) -> bool
>>>>>>> main
```

**Parameters:**
- `vault_id`: ID of the vault to validate

<<<<<<< doc/changelog
**Returns:** `Result<bool, Error>` - `Ok(true)` if validation successful

**Errors:**
- `Error::VaultNotFound` - Vault with given ID does not exist
- `Error::VaultNotActive` - Vault is not in `Active` status
- `Error::AlreadyValidated` - Milestone has already been validated for this vault
- `Error::MilestoneExpired` - Current timestamp is at or past `end_timestamp`

**Requirements:**
- Vault must exist and be in `Active` status
- Milestone must not have been previously validated
- Caller must be the designated verifier (if set) or creator (if no verifier)
=======
**Returns:** `bool` - True if validation successful

**Requirements (TODO):**
- Vault must exist and be in `Active` status
- Caller must be the designated verifier (if set)
>>>>>>> main
- Current timestamp must be before `end_timestamp`

**Emits:** [`milestone_validated`](#milestone_validated) event

---

### `release_funds`

<<<<<<< doc/changelog
Releases locked funds to `success_destination`. Allowed after milestone validation or once the deadline has passed.

```rust
pub fn release_funds(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error>
=======
Releases locked funds to the success destination (typically after validation).

```rust
pub fn release_funds(env: Env, vault_id: u32) -> bool
>>>>>>> main
```

**Parameters:**
- `vault_id`: ID of the vault to release funds from
<<<<<<< doc/changelog
- `usdc_token`: Address of the USDC token contract (must match the token used at creation)

**Returns:** `Result<bool, Error>` — `true` on success

**Errors:**
- `Error::VaultNotFound` — vault does not exist
- `Error::VaultNotActive` — vault is not in `Active` status
- `Error::NotAuthorized` — milestone not validated and deadline not yet reached
=======

**Returns:** `bool` - True if release successful

**Requirements (TODO):**
- Vault status must be `Active`
- Caller must be authorized (verifier or contract logic)
- Transfers USDC to `success_destination`
- Sets status to `Completed`
>>>>>>> main

---

### `redirect_funds`

<<<<<<< doc/changelog
Redirects funds to `failure_destination` when the deadline passes without milestone validation.

```rust
pub fn redirect_funds(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error>
=======
Redirects funds to the failure destination when milestone is not completed by deadline.

```rust
pub fn redirect_funds(env: Env, vault_id: u32) -> bool
>>>>>>> main
```

**Parameters:**
- `vault_id`: ID of the vault to redirect funds from
<<<<<<< doc/changelog
- `usdc_token`: Address of the USDC token contract (must match the token used at creation)

**Returns:** `Result<bool, Error>` — `true` on success

**Errors:**
- `Error::VaultNotFound` — vault does not exist
- `Error::VaultNotActive` — vault is not in `Active` status
- `Error::InvalidTimestamp` — deadline has not yet passed
- `Error::NotAuthorized` — milestone was already validated (funds should go to success)
=======

**Returns:** `bool` - True if redirect successful

**Requirements (TODO):**
- Vault status must be `Active`
- Current timestamp must be past `end_timestamp`
- Transfers USDC to `failure_destination`
- Sets status to `Failed`
>>>>>>> main

---

### `cancel_vault`

Allows the creator to cancel the vault and retrieve locked funds.

```rust
<<<<<<< doc/changelog
pub fn cancel_vault(env: Env, vault_id: u32, usdc_token: Address) -> Result<bool, Error>
=======
pub fn cancel_vault(env: Env, vault_id: u32) -> bool
>>>>>>> main
```

**Parameters:**
- `vault_id`: ID of the vault to cancel
<<<<<<< doc/changelog
- `usdc_token`: Address of the USDC token contract (must match the token used at creation)

**Authorization:** Only the vault `creator` may call this.

**Errors:**
- `Error::VaultNotFound` — vault does not exist
- `Error::VaultNotActive` — vault is not in `Active` status
=======

**Returns:** `bool` - True if cancellation successful

**Requirements (TODO):**
- Caller must be the vault creator
- Vault status must be `Active`
- Returns USDC to creator
- Sets status to `Cancelled`
>>>>>>> main

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
<<<<<<< doc/changelog
    milestone_validated: false,
=======
>>>>>>> main
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

<<<<<<< doc/changelog
### `funds_released`

Emitted when funds are released to `success_destination`.

**Topic:** `("funds_released", vault_id)`  
**Data:** `i128` — amount transferred

---

### `funds_redirected`

Emitted when funds are redirected to `failure_destination`.

**Topic:** `("funds_redirected", vault_id)`  
**Data:** `i128` — amount transferred

---

## API Payload Mapping for Backend Integration

This section maps contract methods to REST API payloads for backend integration. See [`src/doc.md`](./src/doc.md) for complete backend integration guide.

### REST API Endpoints

| Contract Method | HTTP Method | API Endpoint |
|----------------|-------------|--------------|
| `create_vault` | POST | `/api/v1/vaults` |
| `validate_milestone` | POST | `/api/v1/vaults/{vault_id}/validate` |
| `release_funds` | POST | `/api/v1/vaults/{vault_id}/release` |
| `redirect_funds` | POST | `/api/v1/vaults/{vault_id}/redirect` |
| `cancel_vault` | POST | `/api/v1/vaults/{vault_id}/cancel` |
| `get_vault_state` | GET | `/api/v1/vaults/{vault_id}` |
| `vault_count` | GET | `/api/v1/vaults/count` |

### Create Vault API Payload

**Request:**
```json
{
  "usdc_token": "CAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHK3M",
  "creator": "GAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA",
  "amount": "1000000000",
  "start_timestamp": 1704067200,
  "end_timestamp": 1706640000,
  "milestone_hash": "4d696c6573746f6e655f726571756972656d656e74735f68617368",
  "verifier": "GB7XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX",
  "success_destination": "GC7XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX",
  "failure_destination": "GD7XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX"
}
```

**Response:**
```json
{
  "vault_id": 42,
  "status": "Active",
  "transaction_hash": "db7e7f0e81dcde2f38b7c8d7b9c5c3a2b1d4e5f6a7b8c9d0e1f2a3b4c5d6e7f8",
  "ledger_sequence": 12345678,
  "created_at": "2024-01-01T00:00:00Z"
}
```

### Validate Milestone API Payload

**Request:**
```json
{
  "vault_id": 42,
  "verifier_signature": "signature_data_here"
}
```

**Response:**
```json
{
  "vault_id": 42,
  "milestone_validated": true,
  "transaction_hash": "a1b2c3d4e5f6a7b8c9d0e1f2a3b4c5d6e7f8a9b0c1d2e3f4a5b6c7d8e9f0a1b2",
  "ledger_sequence": 12345680,
  "validated_at": "2024-01-15T12:30:00Z"
}
```

### Release Funds API Payload

**Request:**
```json
{
  "vault_id": 42,
  "usdc_token": "CAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHK3M",
  "caller_signature": "signature_data_here"
}
```

**Response:**
```json
{
  "vault_id": 42,
  "status": "Completed",
  "amount_released": "1000000000",
  "destination": "GC7XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX",
  "transaction_hash": "b2c3d4e5f6a7b8c9d0e1f2a3b4c5d6e7f8a9b0c1d2e3f4a5b6c7d8e9f0a1b2c3",
  "ledger_sequence": 12345682,
  "released_at": "2024-01-20T00:00:00Z"
}
```

### Error Response Format

```json
{
  "error": {
    "code": "VAULT_NOT_FOUND",
    "message": "Vault with ID 42 does not exist",
    "contract_error": "VaultNotFound",
    "contract_error_code": 1,
    "details": {
      "vault_id": 42
    }
  }
}
```

=======
>>>>>>> main
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

<<<<<<< doc/changelog
This section outlines the security assumptions, trust model, and known limitations of the Disciplr Vault contract. It is intended for auditors, developers, and users to understand the risks and guarantees provided by the system.

### Trust Model

1. **Verifier Trust (Critical)**: When a `verifier` is designated (via `Some(Address)`), that address has **absolute power** to validate the milestone and cause funds to be released to the `success_destination` before the deadline. If the verifier is compromised or malicious, they can release funds prematurely or to a non-compliant recipient.
2. **Creator Power**: If no `verifier` is set (`None`), only the `creator` can validate the milestone. Additionally, the `creator` can cancel the vault at any time to reclaim funds, assuming the vault is still `Active`. 
3. **Immutable Destinations**: Once a vault is created, the `success_destination` and `failure_destination` are immutable. This prevents redirection of funds after the vault is funded, assuming the core contract logic remains secure.

### Security Assumptions

1. **Stellar Ledger Integrity**: We assume the underlying Stellar blockchain and Soroban runtime correctly enforce authorization (`require_auth`) and maintain state integrity.
2. **Ledger Timestamp**: The contract relies on `env.ledger().timestamp()` for all time-based logic (start/end windows). We assume ledger timestamps are reasonably accurate and monotonic as per Stellar network consensus.
3. **Token Contract Behavior**: The contract interacts with a USDC token contract (standard Soroban token interface). We assume the token contract is honest and follows the expected transfer behavior.

### Reentrancy and Token Callback Assumptions

The Disciplr Vault contract is protected against reentrancy attacks through the following mechanisms:

#### Soroban Token Transfer Atomicity

The Soroban token `transfer` operation is **atomic** — it completes entirely within a single contract invocation without invoking callbacks to the calling contract. Specifically:

- When `token_client.transfer(&from, &to, &amount)` is called, the token contract executes the transfer internally and returns immediately
- There is **no callback mechanism** that would allow the token contract to re-invoke the Disciplr Vault contract during a transfer
- This means there are no reentrancy vectors via malicious token contracts in standard Soroban token implementations

#### Custom Token Restrictions

For deployments using the standard Soroban token interface (including Stellar Asset Contracts and standard ERC-20-like tokens deployed on Soroban):

- **No custom token callbacks**: The contract assumes the token being used does not implement callback hooks to the caller
- **Assumption**: Custom tokens that implement reentrant callbacks are not supported in standard deployments
- **Mitigation**: If custom tokens are allowed, additional guards (e.g., reentrancy locks) should be implemented

#### Deployment-Specific Assumptions

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
=======
<<<<<<< doc/cei-soroban
### trust Model

1. **Absolute Verifier Power**: If a `verifier` is designated, they hold absolute power over the milestone validation process. The contract cannot verify off-chain project completion; it relies entirely on the `verifier`'s signature or authorization.
2. **Creator Authority**: The `creator` is the only address authorized to `create_vault` or `cancel_vault`. They must authorize the initial USDC funding.
3. **No Administrative Overrides**: There is no "admin" or "owner" role with the power to sweep funds or override the vault logic. Funds can only flow to the predefined `success_destination`, `failure_destination`, or back to the `creator` on cancellation.

### External Dependencies

1. **USDC Token Contract**: The contract interacts with an external USDC token address (Stellar Asset Contract). The security of the vault depends on the integrity and availability of this external contract.
2. **Ledger Reliability**: The contract relies on the Stellar network's ledger timestamp for all timing constraints (`start_timestamp`, `end_timestamp`).

### Checks-Effects-Interactions (CEI) Pattern

The Disciplr Vault strictly follows the **Checks-Effects-Interactions** pattern for all state-changing operations, especially token transfers. This is a critical security practice in smart contract development to prevent reentrancy attacks and ensure state consistency.

#### The Pattern in Practice:
=======
## Security and Trust Model

This section outlines the security properties, trust assumptions, and known limitations of the Disciplr Vault contract.
>>>>>>> main

1.  **Checks**: All prerequisites are validated first.
    *   Authorization (`require_auth`)
    *   Vault existence and status (`Active`)
    *   Timestamp constraints (deadlines, windows)
    *   Input validation (amounts, addresses)
2.  **Effects**: The contract's internal state is updated *before* any external interactions.
    *   Setting vault status to `Completed`, `Failed`, or `Cancelled`.
    *   Persisting the updated state to Soroban storage.
    *   This ensures that even if an execution is interrupted or a sub-call attempts to re-enter, the contract already reflects the terminal state.
3.  **Interactions**: External contract calls are performed last.
    *   `token_client.transfer(...)` to move USDC funds.
    *   If the interaction fails, the entire Soroban transaction reverts, ensuring the state update is also undone (atomicity).

<<<<<<< doc/cei-soroban
#### Why CEI?
While Soroban provides inherent atomicity (reverting all changes if any part fails), following CEI is essential for:
*   **Reentrancy Prevention**: Prevents a malicious recipient contract from re-entering the vault contract and attempting to double-release funds before the state is updated.
*   **Logical Clarity**: Makes the security properties of the contract easier to audit and verify.
*   **Resilience**: Protects against unexpected behavior in complex multi-contract interactions.

### Known Limitations & Security Notes

1. **USDC Token Address Consistency**: The `usdc_token` address is not pinned to the vault at creation. Instead, it is passed as an argument to release/redirect functions. While this provides flexibility, it requires callers to ensure they are interacting with the correct asset contract.
2. **No Emergency Stops**: There is currently no "pause" or circuit breaker mechanism. Once a vault is active, it follows the defined lifecycle until completion or cancellation.
3. **Storage Quotas**: Contract performance and cost are subject to Soroban storage fees and quotas.
=======
1. **Verifier Trust (Critical)**: When a `verifier` is designated (via `Some(Address)`), that address has **absolute power** to validate the milestone and cause funds to be released to the `success_destination` before the deadline. If the verifier is compromised or malicious, they can release funds prematurely.
2. **Creator Power**: If no `verifier` is set (`None`), only the `creator` can validate the milestone. Additionally, the `creator` can cancel the vault at any time to reclaim funds, assuming the vault is still `Active`. 
3. **Immutable Destinations**: Once a vault is created, the `success_destination` and `failure_destination` are immutable. This prevents redirection of funds after the vault is funded.

### Security Assumptions

1. **Stellar Ledger Integrity**: We assume the underlying Stellar blockchain and Soroban runtime correctly enforce authorization (`require_auth`) and maintain state integrity.
2. **Ledger Timestamp**: The contract relies on `env.ledger().timestamp()` for all time-based logic. We assume ledger timestamps are reasonably accurate.
3. **Token Contract Behavior**: The contract interacts with a USDC token contract (standard Soroban token interface).

### Known Limitations & Risks

1. **USDC Token Address Consistency**: The `usdc_token` address is not stored in the vault data. Instead, it is passed as an argument to methods.
   > [!WARNING]
   > There is a risk that a caller provides a different token address than the one used during vault creation.
2. **CEI Pattern Violations**: Some methods perform token transfers before updating the internal vault status.
3. **No Administrative Overrides**: There is no "admin" role with the power to rescue funds from a stalled vault.
4. **Lack of Reentrancy Guards**: The contract does not currently implement explicit reentrancy guards, relying on Soroban's atomicity.

### Recommendations for Production

1. **Use Soroban Token Interface**: Implement standard token operations for USDC.
2. **Add Access Control**: Implement `Ownable` pattern for admin functions.
3. **Circuit Breaker**: Add emergency pause functionality.
4. **Upgradeability**: Consider proxy pattern for contract upgrades.
5. **Comprehensive Tests**: Achieve 95%+ test coverage.
6. **External Audits**: Have security experts review before mainnet deployment.
>>>>>>> main
>>>>>>> main

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

<<<<<<< doc/changelog
For a complete history of all notable changes and versioned releases, please refer to [CHANGELOG.md](CHANGELOG.md).

| Version | Key Changes |
|---------|---------|
| 0.4.0   | CEI Pattern Refactor, Comprehensive Rustdoc |
| 0.3.0   | Idempotency Guards, Sequential ID Allocation |
| 0.2.0   | USDC Token Integration |
| 0.1.0   | Initial Release |
=======
| Version | Changes |
|---------|---------|
| 0.1.0 | Initial release with basic vault structure, stubbed implementations |
>>>>>>> main
