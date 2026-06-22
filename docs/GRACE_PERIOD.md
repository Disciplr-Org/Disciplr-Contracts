# Redirect Grace Period

Vault creators can configure a `grace_period` in seconds when calling
`create_vault`. The value gives late-but-valid milestone completions a buffer
after `end_timestamp` before funds can be redirected to `failure_destination`.

## Rules

| Rule | Behavior |
| --- | --- |
| `grace_period == 0` | Preserves the original behavior: redirect succeeds only when `now > end_timestamp`. |
| `0 < grace_period <= MAX_VAULT_DURATION` | Redirect succeeds only when `now > end_timestamp + grace_period`. |
| `grace_period > MAX_VAULT_DURATION` | `create_vault` rejects with `DurationTooLong`. |
| `end_timestamp + grace_period` overflow | `redirect_funds` rejects with `InvalidTimestamp`. |
| Milestone already validated | `redirect_funds` rejects with `NotAuthorized`, even after the grace period. |

The redirect boundary is strict. At exactly `end_timestamp + grace_period`,
redirection is still too early. One second later, redirection is allowed if the
vault remains active and unvalidated.

## Example

```text
start_timestamp = 1_700_000_000
end_timestamp   = 1_700_086_400
grace_period    = 3_600
redirect_after  = 1_700_090_000
```

`redirect_funds` rejects at `1_700_090_000` and succeeds at `1_700_090_001`.
