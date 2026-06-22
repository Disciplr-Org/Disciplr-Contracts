# Paginated Vault Enumeration

`list_vaults(start_id, limit)` is a read-only enumeration view for frontends and
indexers that need to fetch vault records without probing every ID one call at a
time.

## Contract

```rust
pub fn list_vaults(
    env: Env,
    start_id: u32,
    limit: u32,
) -> Result<Vec<(u32, ProductivityVault)>, Error>
```

## Behavior

- Returns existing `(vault_id, ProductivityVault)` records in the half-open range
  `[start_id, start_id + limit)`.
- Stops at `vault_count()` so it does not read beyond the assigned ID range.
- Skips missing records gracefully.
- Requires no authorization and does not mutate storage.
- Allows `limit = 0`, which returns an empty page.
- Rejects `limit > MAX_LIST_VAULTS_LIMIT` with `Error::LimitTooLarge`.

The current maximum page size is `100` records.

## Example

To enumerate every vault, callers can start at `0`, request at most
`MAX_LIST_VAULTS_LIMIT` records, and continue with the next start ID until an
empty page is returned or `vault_count()` has been reached.
