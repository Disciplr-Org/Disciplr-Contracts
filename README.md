# disciplr-contracts

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

This repo is a **basic version**: logic is stubbed and storage is not persisted. Use it as a starting point for full implementation (USDC token integration, persistence, timestamp checks, auth).

## Tech stack

- **Rust** (edition 2021)
- **Soroban SDK** (22.x) for Stellar smart contracts
- Build target: **WASM** (cdylib)

## Local setup

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

### Scripts (optional)

You can add to `package.json` for consistency (requires `npm`/`yarn`):

- `build` → `cargo build --target wasm32-unknown-unknown --release`
- `test` → `cargo test`

## Project layout

```
disciplr-contracts/
├── src/
│   └── lib.rs       # DisciplrVault contract + ProductivityVault type
├── Cargo.toml
└── README.md
```

## Merging into a remote

This directory is a separate git repo. To push to your own remote:

```bash
cd disciplr-contracts
git remote add origin <your-disciplr-contracts-repo-url>
git push -u origin main
```

Replace `<your-disciplr-contracts-repo-url>` with your actual repository URL.
