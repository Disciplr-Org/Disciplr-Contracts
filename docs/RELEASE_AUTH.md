# Release Authorization

`release_funds` sends the locked vault balance only to the vault's stored
`success_destination`. The caller does not provide a destination, so triggering a
release cannot redirect funds to the caller or another address.

## Authorization Matrix

| Vault state | Release condition | Required caller |
| --- | --- | --- |
| Active, before `end_timestamp`, not validated | Rejected with `Error::NotAuthorized` | None |
| Active, before `end_timestamp`, validated | Allowed | Any caller |
| Active, at or after `end_timestamp` | Allowed | Any caller |
| Completed, Failed, or Cancelled | Rejected with `Error::VaultNotActive` | None |

Milestone validation remains restricted: the configured verifier must validate
when `verifier` is `Some`, and the creator must validate when `verifier` is
`None`. Once that validation has been recorded, `release_funds` only checks the
vault state and destination invariants before transferring to `success_destination`.

This keeps the post-deadline path permissionless. If the creator disappears,
any account can still trigger the success transfer after the deadline, while the
funds remain bound to the pre-committed destination.
