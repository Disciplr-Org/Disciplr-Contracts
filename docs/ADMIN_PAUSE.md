# Admin Emergency Pause

`DisciplrVault` supports an optional contract-level emergency pause for incident
response. Existing vault flows remain unpaused by default, but once an admin is
initialized that admin can halt mutating entrypoints while investigation or a fix
is prepared.

## Admin Setup

| Entrypoint | Authorization | Behavior |
| --- | --- | --- |
| `initialize(admin)` | `admin.require_auth()` | Stores the admin once and initializes `Paused = false`. |
| `set_paused(paused)` | Stored admin | Toggles the pause flag and emits `paused` or `unpaused`. |

Initialization is one-time. A second `initialize` call returns
`AlreadyInitialized`; calling `set_paused` before initialization returns
`NotInitialized`.

## Pause Scope

When paused, these mutating entrypoints return `ContractPaused` before auth,
storage mutation, or token transfer work:

- `create_vault`
- `validate_milestone`
- `release_funds`
- `redirect_funds`
- `cancel_vault`

Read-only entrypoints remain callable while paused:

- `get_vault_state`
- `vault_count`

This keeps operators able to inspect vault state during an incident while
preventing new vault creation and terminal fund movements.
