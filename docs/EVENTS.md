# Disciplr Vault Event Schema

Lifecycle events use stable names with a consistent indexed topic layout:

```text
(event_name, vault_id, creator)
```

The event data is always `VaultLifecycleEventData`:

| Field | Type | Description |
| --- | --- | --- |
| `amount` | `i128` | Vault amount in the token's smallest unit. |
| `destination` | `Option<Address>` | Destination affected by the transition, when one exists. |
| `status` | `VaultStatus` | Vault status after the transition. |

## Lifecycle Events

| Event | Topics | Data |
| --- | --- | --- |
| `vault_created` | `("vault_created", vault_id, creator)` | `{ amount, destination: None, status: Active }` |
| `milestone_validated` | `("milestone_validated", vault_id, creator)` | `{ amount, destination: None, status: Active }` |
| `funds_released` | `("funds_released", vault_id, creator)` | `{ amount, destination: Some(success_destination), status: Completed }` |
| `funds_redirected` | `("funds_redirected", vault_id, creator)` | `{ amount, destination: Some(failure_destination), status: Failed }` |
| `vault_cancelled` | `("vault_cancelled", vault_id, creator)` | `{ amount, destination: Some(creator), status: Cancelled }` |

Event names are unchanged for backward compatibility. Consumers that previously
filtered by `(event_name, vault_id)` can keep using those first two topics, while
new consumers can filter by the third `creator` topic without decoding payloads.
