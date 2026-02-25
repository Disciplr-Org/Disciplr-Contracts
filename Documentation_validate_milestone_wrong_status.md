## Test: validate_milestone rejects non-Active vaults

### Purpose
- Ensure `validate_milestone` cannot be used once a vault leaves `Active`.
- Prevent invalid state transitions and repeated milestone validation.

### Covered statuses
- `Completed`
- `Failed`
- `Cancelled`

### Security impact
- Enforces lifecycle integrity: only `Active` vaults can be validated.
- Reduces risk of double-processing milestone outcomes after completion, failure, or cancellation.

### Verification
- Added test: `test_validate_milestone_rejects_non_active_statuses`
- Expected error for each case: `Error::VaultNotActive`
