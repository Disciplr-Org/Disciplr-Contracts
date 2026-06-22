# Release Funds Authorization

`release_funds` is a permissionless trigger once the vault has met a success
condition. The caller cannot choose where funds go: every successful release
transfers the escrowed amount to the vault's pre-committed
`success_destination`.

## Authorization Matrix

| Vault condition | Who may call `release_funds` | Result |
| --- | --- | --- |
| Active, milestone not validated, before `end_timestamp` | No one | Rejects with `Error::NotAuthorized` |
| Active, milestone validated, before `end_timestamp` | Anyone | Transfers to `success_destination` |
| Active, at or after `end_timestamp` | Anyone | Transfers to `success_destination` |
| Completed, Failed, or Cancelled | No one | Rejects with `Error::VaultNotActive` |

Validation authorization remains separate:

- If `verifier` is `Some(address)`, only that verifier can call
  `validate_milestone`.
- If `verifier` is `None`, only the creator can call `validate_milestone`.

This avoids a liveness failure where a creator disappears after funding the
vault. Once the milestone has been validated or the deadline has arrived, any
account can finalize the successful path, but funds still only reach the
configured `success_destination`.
