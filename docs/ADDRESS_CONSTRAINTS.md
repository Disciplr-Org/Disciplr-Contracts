# Address Constraints

`create_vault` accepts four participant addresses:

- `creator`: funds the vault and may cancel it while active.
- `verifier`: optional milestone validator.
- `success_destination`: receives funds when the vault succeeds.
- `failure_destination`: receives funds when the vault fails.

The verifier must not also be a payout destination. A verifier who can validate
their own payout creates a conflict of interest, so `create_vault` rejects that
configuration with `Error::ConflictingAddresses`.

## Matrix

| Configuration | Result | Rationale |
| --- | --- | --- |
| `verifier == success_destination` | Rejected | Verifier would be able to approve their own success payout. |
| `verifier == failure_destination` | Rejected | Verifier would have a payout interest in the failure path. |
| `verifier == creator` | Allowed | This is an explicit creator-validation mode and is covered by tests. |
| `verifier == None` and `success_destination == failure_destination` | Allowed | No third-party verifier conflict exists; both terminal paths pay the configured destination. |
| Distinct verifier, success, and failure addresses | Allowed | Standard third-party validation setup. |

These checks run before the USDC escrow transfer, so rejected configurations do
not move funds into the contract.
