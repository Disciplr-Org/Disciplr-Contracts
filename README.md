# Disciplr Contracts

Soroban smart contracts for [Disciplr](https://github.com/your-org/Disciplr): programmable time-locked USDC vaults on Stellar.

## What it does

Single contract **disciplr-vault** with:

- **Data model:** `ProductivityVault` (creator, amount, start/end timestamps, milestone hash, optional verifier, success/failure destinations, status).
- **Status:** `Active`, `Completed`, `Failed`, `Cancelled`.
- **Methods (stubs):**
  - `create_vault(...)` — create vault and emit `vault_created` (USDC lock is TODO).
  - `validate_milestone(vault_id)` — verifier validates milestone (release logic TODO).
  - `release_funds(vault_id)` — release to success destination (TODO).
  - `redirect_funds(vault_id)` — redirect to failure destination (TODO).
  - `cancel_vault(vault_id)` — cancel and return to creator (TODO).
  - `get_vault_state(vault_id)` — return vault state (returns `Option`; placeholder returns `None`).

## Implementation Status

### ✅ Completed

- **`cancel_vault` implementation:**
  - Requires creator authentication (`require_auth`).
  - Only allows cancellation of vaults with `Active` status.
  - Refunds simulated USDC balance to creator (stored in persistent storage).
  - Sets status to `Cancelled` and persists state.
  - Emits `vault_cancelled` event with creator and refunded amount.
  - All 3 unit tests pass (creator cancel, non-creator fails, cannot cancel Completed).

### 📋 TODO

- Real USDC token transfer (currently simulated via storage).
- Timestamp validation (before/after cutoff rules).
- Milestone validation logic.
- Release/redirect funds operations.
- Multi-sig / admin controls.

## Security & Design Notes

### Cancellation Rules

- **Allowed:** Only when vault status == `Active`.
- **Restriction:** Only the vault creator can cancel.
- **Effect:** Refunds stored balance, sets status to `Cancelled`.
- **Event:** Emits `vault_cancelled` with amount and creator.

### Token Refund Approach

Currently uses **simulated balance storage** (`vault_balance` key per vault ID):
- On `create_vault`: stores amount in persistent storage as proxy for locked funds.
- On `cancel_vault`: retrieves balance and zeros it, emits refund event.
- **Future:** Integrate real Soroban token contract (e.g., Stellar Asset or custom).

### Auth & Access Control

- All state-changing functions require `require_auth()` on relevant parties (creator for cancel).
- Storage is contract-scoped (only this contract can read/write vault data).
- No admin override; only creator can cancel their own vault.

### Test Coverage

- **3 passing tests** covering:
  1. Creator cancellation success.
  2. Non-creator cancellation rejection (panics via `require_auth`).
  3. Cannot cancel already-completed/failed vaults (returns false).
- **>90% code coverage** for `cancel_vault` path.
- Tests use Soroban SDK `mock_auths` and contract clients.

## Documentation

For detailed contract documentation, see [vesting.md](vesting.md).

---

# Contract Documentation

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
    pub status: VaultStatus,        // Current lifecycle state of the vault
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

**Emits:** `vault_created` event

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

**Emits:** `milestone_validated` event

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

**Returns:** `Option<ProductivityVault>` - Vault data if exists, None otherwise

**Note:** Current implementation returns `None` as placeholder. Full implementation will read from persistent storage.

---

## Events

### `vault_created`

Emitted when a new vault is created.

**Topic:** `("vault_created", vault_id)`

**Data:** Full `ProductivityVault` struct

---

### `milestone_validated`

Emitted when a milestone is successfully validated.

**Topic:** `("milestone_validated", vault_id)`

**Data:** `()` (empty tuple)

---

## Lifecycle

```
                    +--------------+
                    |   CREATED    |
                    |              |
                    | create_vault |
                    +------+-------+
                           |
                           v
                    +--------------+
         +---------|    ACTIVE    |---------+
         |         |              |         |
         |         +--------------+         |
         |                                |
         v                                v
+-----------------+              +---------------------+
| validate_       |              |  redirect_funds     |
| milestone()     |              |  (deadline passed)  |
+--------+--------+              +----------+----------+
         |                                   |
         v                                   v
+-----------------+              +---------------------+
|   COMPLETED    |              |      FAILED        |
|                |              |                     |
+-----------------+              +---------------------+

         |
         v
+-----------------+
| cancel_vault()  |
+--------+--------+
         |
         v
+-----------------+
|   CANCELLED    |
|                |
+-----------------+
```

---

## Security Assumptions

### Authentication & Authorization

1. **Creator Authorization**: The vault creator must authorize transactions via `require_auth()`. This ensures only the creator can initiate vault creation or cancellation.

2. **Verifier Role**: An optional verifier can be designated during vault creation. If set, only the verifier can validate milestones. If not set, anyone can validate (which may be useful for decentralized verification).

3. **Destination Addresses**: Once set, success and failure destinations cannot be modified. This prevents fund redirection attacks.

### Timing Constraints

1. **Start Timestamp**: Vault funds are locked from `start_timestamp`. Before this time, the vault exists but is not active.

2. **End Timestamp**: After `end_timestamp`:
   - If milestone is validated → funds release to success destination
   - If not validated → funds redirect to failure destination

3. **Timestamp Validation**: All time-sensitive operations must check that the current block timestamp is within the valid window.

### Token Handling

1. **USDC Integration**: The contract expects USDC (or similar token) to be transferred to the contract before vault creation. This requires:
   - Creator approves token transfer
   - Contract pulls tokens from creator (via `transfer_from`)

2. **Non-Custodial**: The contract holds tokens in escrow but never has withdrawal authority beyond the defined destination addresses.

### Current Limitations (TODOs)

The following security features are not yet implemented:

- [ ] **Storage Persistence**: Vaults are not persisted between contract calls
- [ ] **Token Transfer**: Actual USDC transfer logic is not implemented
- [ ] **Timestamp Validation**: Methods don't validate timestamps
- [ ] **Verifier Authorization**: No check that caller is the designated verifier
- [ ] **Reentrancy Protection**: No guards against reentrancy attacks
- [ ] **Access Control**: Basic auth only; no complex role-based access

### Recommendations for Production

1. **Use Soroban Token Interface**: Implement standard token operations for USDC
2. **Add Access Control**: Implement `Ownable` pattern for admin functions
3. **Circuit Breaker**: Add emergency pause functionality
4. **Upgradeability**: Consider proxy pattern for contract upgrades
5. **Comprehensive Tests**: Achieve 95%+ test coverage
6. **External Audits**: Have security experts review before mainnet deployment

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

## Tech Stack

- **Rust** (edition 2021)
- **Soroban SDK** (22.x) for Stellar smart contracts
- Build target: **WASM** (cdylib)

---

## Local Setup

### Prerequisites

- [Rust](https://rustup.rs/) (stable)
- [Stellar Soroban CLI](https://developers.stellar.org/docs/tools/developer-tools/soroban-cli) (optional, for build/deploy)

### Build

```bash
# From repo root
cd disciplr-contracts
cargo build
```

WASM build (for deployment):

```bash
cargo build --target wasm32-unknown-unknown --release
```

Output: `target/wasm32-unknown-unknown/release/disciplr_vault.wasm`

### Test

```bash
cargo test
```

---

## Project Layout

```
disciplr-contracts/
├── src/
│   └── lib.rs       # DisciplrVault contract + ProductivityVault type
├── Cargo.toml
├── README.md
└── vesting.md       # Detailed contract documentation
```

---

# Contributors Workflow

We welcome contributions from the community! Please follow this workflow to ensure a smooth collaboration.

## Getting Started

### 1. Fork the Repository

Click the "Fork" button on the GitHub repository to create your own copy.

### 2. Clone Your Fork

```bash
git clone https://github.com/YOUR_USERNAME/disciplr-contracts.git
cd disciplr-contracts
```

### 3. Add Upstream Remote

```bash
git remote add upstream https://github.com/your-org/disciplr-contracts.git
```

### 4. Create a Feature Branch

```bash
git checkout -b feature/your-feature-name
```

## Making Changes

### Development Process

1. **Keep your fork in sync**: Regularly pull from upstream to stay current
   ```bash
   git fetch upstream
   git checkout main
   git merge upstream/main
   ```

2. **Make your changes**: Implement your feature or fix

3. **Write tests**: Aim for 95%+ test coverage
   ```bash
   # Add tests to src/lib.rs
   cargo test
   ```

4. **Build and verify**:
   ```bash
   cargo build
   cargo build --target wasm32-unknown-unknown --release
   ```

### Code Style

- Follow standard Rust conventions
- Use meaningful variable and function names
- Add comments for complex logic
- Document public functions with doc comments

### Commit Messages

Use clear, descriptive commit messages:

```
type: short description

Detailed description of changes.

Fixes #issue-number
```

Types:
- `feat`: New feature
- `fix`: Bug fix
- `docs`: Documentation
- `test`: Adding tests
- `refactor`: Code restructuring
- `chore`: Maintenance tasks

Example:
```
feat: add milestone validation logic

- Implement validate_milestone() with verifier authorization
- Add timestamp checks to prevent late validations
- Emit milestone_validated event on success

Fixes #42
```

## Submitting Changes

### 1. Push Your Branch

```bash
git push origin feature/your-feature-name
```

### 2. Create a Pull Request

1. Navigate to your fork on GitHub
2. Click "Compare & pull request"
3. Fill in the PR template:
   - **Title**: Clear description of the change
   - **Description**: Explain what, why, and how
   - **Testing**: Document test results
   - **Screenshots**: If applicable

### 3. PR Review Process

- All PRs require review before merging
- Address feedback promptly
- Keep PRs focused and atomic

## Testing Requirements

Before submitting a PR:

1. **Run all tests**:
   ```bash
   cargo test
   ```

2. **Build for release**:
   ```bash
   cargo build --target wasm32-unknown-unknown --release
   ```

3. **Verify no warnings**:
   ```bash
   cargo clippy
   ```

### Test Coverage

- Aim for 95%+ test coverage
- Test all public functions
- Include edge cases
- Test error conditions

## Security Considerations

When contributing code:

1. **Never commit secrets**: Don't include API keys, passwords, or private keys
2. **Validate inputs**: Always validate user inputs
3. **Follow best practices**: 
   - Use `require_auth()` for authorization
   - Check for overflow/underflow
   - Avoid reentrancy vulnerabilities
4. **Document security implications**: Add security notes in PR description

## Reporting Issues

Found a bug or have a feature request?

1. **Search existing issues** to avoid duplicates
2. **Create a new issue** with:
   - Clear title
   - Detailed description
   - Steps to reproduce (for bugs)
   - Expected vs actual behavior

## Code of Conduct

- Be respectful and inclusive
- Welcome newcomers
- Provide constructive feedback
- Focus on what is best for the community

---

## Merging into a Remote

This directory is a separate git repo. To push to your own remote:

```bash
cd disciplr-contracts
git remote add origin <your-disciplr-contracts-repo-url>
git push -u origin main
```

## Security and Testing

### Security Notes

- **Timestamp Validation**: Milestone validation is strictly prohibited once the ledger timestamp reaches or exceeds `end_timestamp`. This prevents "late" validations and ensures the time-lock is honored.
- **Authentication**: `validate_milestone` requires authorization from the verifier (if specified) or the creator. This ensures only authorized parties can progress the vault state.
- **State Integrity**: Operations like `validate_milestone`, `release_funds`, and `cancel_vault` check the current `status` (must be `Active`) to prevent double-spending or invalid state transitions.

### Test Coverage

The project includes unit tests for core logic, specifically:
- Verification of milestone rejection after `end_timestamp`.
- Verification of successful milestone validation before `end_timestamp`.

To run tests:
```bash
cargo test
```
