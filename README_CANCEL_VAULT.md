# Cancel Vault: Design, Security Notes, and Tests

## Summary

- `cancel_vault` requires the vault `creator` to authorize the call.
- Cancellation is only allowed while the vault status is `Active`.
- On cancel, the contract performs a real Soroban token transfer from the contract escrow balance back to the creator, then marks the vault as `Cancelled`.
- A successful cancellation emits `vault_cancelled`.

## Behavior and Rules

- `create_vault` transfers the escrow amount from the creator to the current contract address.
- `cancel_vault` transfers exactly `vault.amount` from the current contract address back to `vault.creator`.
- Funds are not sent to `success_destination` or `failure_destination` during cancellation.
- Cancelling a `Completed`, `Failed`, or already `Cancelled` vault returns `Error::VaultNotActive`.
- Cancelling a nonexistent vault returns `Error::VaultNotFound`.

## Security Notes

- Authorization: `vault.creator.require_auth()` ensures only the vault owner can cancel.
- Refund target: the caller cannot choose a refund recipient; funds always return to the stored `vault.creator`.
- Escrow accounting: tests assert the creator balance increases by exactly `vault.amount` and the contract token balance returns to its pre-create level after cancellation.
- Terminal-state safety: cancellation is rejected after release, redirect, or a prior cancellation, preventing double refunds.

## Tests

The lifecycle integration tests register a real Soroban token contract in `Env` and assert ledger balances with `TokenClient::balance`.

Run the focused coverage with:

```bash
cargo test test_cancel_vault_refunds_creator_and_empties_contract_escrow
cargo test test_cancel_vault_rejects_completed_failed_and_cancelled_vaults
```

The cancel coverage checks:

- creator balance decreases by `vault.amount` on create
- contract escrow balance increases by `vault.amount` on create
- creator balance increases by `vault.amount` on cancel
- contract escrow returns to its pre-create balance on cancel
- success and failure destinations remain untouched
- `vault_cancelled` is emitted
- non-active vaults reject cancellation with `Error::VaultNotActive`
