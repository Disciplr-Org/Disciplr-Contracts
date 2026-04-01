# Changelog

All notable changes to the Disciplr Vault contract will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.4.0] - 2026-03-30

### Added
- Comprehensive NatSpec-style Rustdoc for all public contract methods in `src/lib.rs`.
- Detailed Checks-Effects-Interactions (CEI) pattern documentation in `vesting.md`.

### Changed
- Refactored `release_funds`, `redirect_funds`, and `cancel_vault` to strictly follow the **Checks-Effects-Interactions (CEI)** pattern, ensuring state updates occur before external token transfers.
- Resolved merge conflicts and restructured the "Security and Trust Model" in `vesting.md`.

## [0.3.0] - 2026-03-29

### Added
- Sequential vault ID management using `VaultCount` in persistent instance storage.
- Idempotency guards (`require_active`) to `release_funds`, `redirect_funds`, `cancel_vault`, and `validate_milestone` to prevent double-execution and ensure mutual exclusivity of terminal states.
- Standardized error handling using `panic_with_error!` and a dedicated `Error` enum.

### Fixed
- Fixed issue where `create_vault` always returned a placeholder ID of 0.

## [0.2.0] - 2026-03-28

### Added
- Initial **USDC Token Integration** in `create_vault`.
- Actual token transfers from creator to contract via `token_client.transfer`.
- Input validation for `amount` (must be positive) and `timestamps` (end > start).
- Authorization enforcement via `creator.require_auth()`.

## [0.1.0] - 2026-03-27

### Added
- Initial project structure for Disciplr Vault Soroban contract.
- Data models: `ProductivityVault` struct and `VaultStatus` enum.
- Function stubs: `create_vault`, `validate_milestone`, `release_funds`, `redirect_funds`, `cancel_vault`, `get_vault_state`.
- Basic unit test suite.
