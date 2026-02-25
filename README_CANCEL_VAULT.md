Cancel Vault: Design, Security Notes, and Tests

Summary
- `cancel_vault` requires the caller to be the vault `creator` and only allows cancellation when the vault `status` is `Active`.
- On cancel it refunds the vault's stored token balance (simulated) back to the creator by clearing the contract-held balance and emitting a `vault_cancelled` event with the refunded amount.

Behavior & rules
- Cancellation allowed only when `status == Active` (i.e., before validation/completion).
- Caller must be the `creator` (enforced via `Address::require_auth`).
- Refund is performed against a simulated per-vault balance stored in persistent storage under key `("vault_balance", vault_id)`.

Security notes
- Real token transfer: the current implementation simulates token movement by updating contract-owned balance storage. For production, replace this with a real token transfer using the Soroban token client and ensure the contract has allowance/escrowed tokens before creating the vault.
- Reentrancy: token transfers must be performed using the recommended Soroban token client patterns; consider checks-effects-interactions ordering (we clear the stored balance and set status before emitting events).
- Authorization: `creator.require_auth()` ensures only the vault owner can cancel.

Tests
- Unit tests cover: successful cancel by creator, unauthorized cancel (panics), and cancel when status is Completed (returns false).
- A helper `get_vault_balance` exposes the simulated vault balance for assertions in tests.

Next steps
- Integrate with a real token contract: add a `token_contract: Address` per vault or instance-level token address and call the token `transfer` to move funds.
- Add more tests that register and interact with a real token contract in test `Env` to assert balances on ledger entries.
