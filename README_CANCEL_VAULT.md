Cancel Vault: Design, Security Notes, and Tests

Summary
- `cancel_vault` requires the caller to be the vault `creator` and only allows cancellation when the vault `status` is `Active`.
- On cancel it transfers the escrowed token amount from the vault contract back to the creator and emits a `vault_cancelled` event.

Behavior & rules
- Cancellation allowed only when `status == Active` (i.e., before validation/completion).
- Caller must be the `creator` (enforced via `Address::require_auth`).
- Refund uses the Soroban token client to transfer `vault.amount` from `env.current_contract_address()` to `vault.creator`.
- The vault record remains stored and its `status` is set to `Cancelled`.

Security notes
- Real token transfer: `create_vault` escrows funds in the contract token balance, and `cancel_vault` sends those funds back to the creator.
- Reentrancy: token transfers should continue to use Soroban token client patterns. Keep state updates and event emission explicit when changing this flow.
- Authorization: `creator.require_auth()` ensures only the vault owner can cancel.

Tests
- Unit tests cover successful cancel by creator, unauthorized cancel, nonexistent vaults, double cancel, and inactive `Completed` / `Failed` / `Cancelled` vault rejection.
- The lifecycle integration test asserts the real token refund by checking that the creator receives exactly `vault.amount`, the contract escrow balance returns to its pre-create value, and the vault status becomes `Cancelled`.

Next steps
- Keep README, `src/doc.md`, and `contract-interface.json` aligned if the event topic, refund amount, or lifecycle status changes.
- Preserve the balance-delta assertions when adding new token escrow paths.
