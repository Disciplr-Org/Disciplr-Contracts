# Reentrancy and Terminal State Ordering

Disciplr vault settlement functions follow checks-effects-interactions ordering.
Each fund-moving terminal path writes its final vault status before invoking the
external token contract:

- `release_funds` writes `VaultStatus::Completed` before transferring to `success_destination`.
- `redirect_funds` writes `VaultStatus::Failed` before transferring to `failure_destination`.
- `cancel_vault` writes `VaultStatus::Cancelled` before transferring back to `creator`.

This matters because `usdc_token` is supplied as a contract address at call time.
If a malicious or non-standard token implementation attempted to re-enter the
vault during transfer, the nested call would observe a non-`Active` vault and fail
with `Error::VaultNotActive`.

The regression tests cover the terminal-state matrix by asserting that, after a
successful release, redirect, or cancel call, every second terminal path is
rejected and no second balance delta is paid.
