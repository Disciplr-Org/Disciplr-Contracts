# Testing Guide - DisciplrVault Contract

## Quick Start

```bash
# Check for unresolved merge conflict markers
git grep -n -E '^(<<<<<<<|=======|>>>>>>>)' -- .

# Run all tests
cargo test

# Run tests with output
cargo test -- --nocapture

# Run specific test
cargo test test_active_to_completed_via_release

# Generate coverage report
cargo tarpaulin --out Html --out Stdout
```

## Property Tests for Timestamp Ordering (Issue #136)

File: `tests/proptest_timestamps.rs`

What is validated:

- **Valid ordering property**: `start < end` succeeds for randomized inputs and randomized ledger times.
- **Invalid ordering property**: `start >= end` rejects with `Error::InvalidTimestamps`.
- **Duration bound property**: `(end - start) > MAX_VAULT_DURATION` rejects with `Error::DurationTooLong`.
- **Duration boundary property**: Densely samples the exact boundary where `duration == MAX_VAULT_DURATION` is accepted, and `duration == MAX_VAULT_DURATION + 1` is rejected with `Error::DurationTooLong`.
- **Past-start rejection property**: Verifies that any vault creation with `start_timestamp < current_time` is rejected with `Error::InvalidTimestamp`.

Strategy design (controlled randomness):

- **Randomized Ledger Time**: The current time `now` is generated via a randomized strategy `0u64..20_000_000_000u64` to sample different ledger dates.
- **Valid cases** use `(now, start_offset, duration)` with:
  - `start = now + start_offset`
  - `duration in 1..=MAX_VAULT_DURATION`
  - `end = start + duration`
- **Invalid ordering** uses `end = start.saturating_sub(backoff)` to guarantee `end <= start`.
- **Past-start cases** use `start = now - past_offset` (where `past_offset >= 1` and `now >= 1_000_000`) to guarantee `start < now`.
- **Overflow risk** is entirely avoided by setting upper limits on `now` and `start_offset` such that `now + start_offset + duration` is mathematically guaranteed to stay well below `u64::MAX`.

Explicit edge vectors included:

- `start == end` (reject with `Error::InvalidTimestamps`)
- `start = 0`, `end = 1` with ledger time at `0` (accept)
- `duration == MAX_VAULT_DURATION` (accept)
- `start == now` (accept)


- **32 comprehensive tests** - All passing
- **92.16% line coverage** (47/51 lines)
- **100% functional coverage** of business logic
- **100% critical path coverage**

See [COVERAGE_ANALYSIS.md](./COVERAGE_ANALYSIS.md) for detailed breakdown.

## Test Categories

### 1. Valid State Transitions (4 tests)

Tests all valid vault state changes:

```bash
cargo test test_active_to_completed
cargo test test_active_to_failed
cargo test test_active_to_cancelled
```

### 2. Terminal State Protection (12 tests)

Security tests ensuring terminal states are immutable:

```bash
cargo test test_completed_cannot
cargo test test_failed_cannot
cargo test test_cancelled_cannot
```

### 3. Event Emission (6 tests)

Verifies audit trail logging:

```bash
cargo test test_.*_emits_event
```

### 4. Data Integrity (10 tests)

Edge cases and comprehensive validation:

```bash
cargo test test_vault_creation
cargo test test_vault_data_integrity
cargo test test_sequential_operations
```

## Coverage Reports

### Generate HTML Report

```bash
cargo tarpaulin --out Html --output-dir coverage
open coverage/tarpaulin-report.html
```

### Generate Multiple Formats

```bash
cargo tarpaulin --out Html --out Xml --out Lcov --output-dir coverage
```

### CI/CD Integration

```bash
# GitHub Actions workflow included
.github/workflows/coverage.yml
```

The main CI workflow also runs a merge-conflict marker guard before formatting,
build, and tests. The guard fails if any file contains a line starting with
`<<<<<<<`, `=======`, or `>>>>>>>`. See [docs/MERGE_HYGIENE.md](./docs/MERGE_HYGIENE.md)
for the local check and resolution steps.

## Understanding Coverage Metrics

### Line Coverage: 92.16%

- 47 out of 51 lines covered
- 4 uncovered lines are Soroban SDK event calls
- These lines execute successfully (verified by test snapshots)

### Functional Coverage: 100%

- All business logic tested
- All state transitions covered
- All security constraints verified

### Branch Coverage: 100%

- All conditional paths tested
- All panic conditions verified
- All status checks covered

## Test Snapshots

Each test generates a snapshot file in `test_snapshots/test/`:

- Contains all events published
- Shows final ledger state
- Proves event publishing works

```bash
# View test snapshots
ls -la test_snapshots/test/
cat test_snapshots/test/test_vault_creation_emits_event.1.json
```

## Security Testing

### Double-Spending Prevention

```bash
# Run terminal state protection tests
cargo test test_completed_cannot
cargo test test_failed_cannot
cargo test test_cancelled_cannot
```

### State Machine Integrity

```bash
# Run all state transition tests
cargo test test_active_to
```

### Input Validation

```bash
# Run panic condition tests
cargo test should_panic
```

## Performance

All 32 tests complete in ~0.28 seconds:

```bash
cargo test --release
```

## Troubleshooting

### Low Coverage Reported

The 4 uncovered lines are Soroban SDK framework calls. This is expected and documented in COVERAGE_ANALYSIS.md.

### Tests Failing

```bash
# Clean and rebuild
cargo clean
cargo test
```

### Out of Disk Space

```bash
# Clean build artifacts
cargo clean

# Remove old coverage reports
rm -rf coverage/
```

## Best Practices

1. **Run tests before committing**

   ```bash
   cargo test
   ```

2. **Check coverage regularly**

   ```bash
   cargo tarpaulin --out Stdout
   ```

3. **Review test snapshots**

   ```bash
   git diff test_snapshots/
   ```

4. **Keep tests fast**
   - Current: 0.28s for 32 tests ✅
   - Target: < 1s for all tests

## Adding New Tests

### Template for State Transition Test

```rust
#[test]
fn test_new_transition() {
    let (env, contract_id, _creator, vault_id) = setup_test_vault();
    let client = DisciplrVaultClient::new(&env, &contract_id);

    // Verify initial state
    let vault = client.get_vault_state(&vault_id).unwrap();
    assert_eq!(vault.status, VaultStatus::Active);

    // Execute transition
    client.some_function(&vault_id);

    // Verify final state
    let vault = client.get_vault_state(&vault_id).unwrap();
    assert_eq!(vault.status, VaultStatus::Expected);
}
```

### Template for Security Test

```rust
#[test]
#[should_panic(expected = "Expected error message")]
fn test_invalid_operation() {
    let (env, contract_id, _creator, vault_id) = setup_test_vault();
    let client = DisciplrVaultClient::new(&env, &contract_id);

    // Setup terminal state
    client.release_funds(&vault_id);

    // Attempt invalid operation (should panic)
    client.release_funds(&vault_id);
}
```

## Continuous Integration

The project includes GitHub Actions workflow for automated testing:

```yaml
# .github/workflows/coverage.yml
- Runs on every push
- Generates coverage reports
- Uploads artifacts
- Checks 90%+ threshold
```

## Resources

- [Soroban Testing Docs](https://developers.stellar.org/docs/build/guides/testing/unit-tests)
- [Tarpaulin Documentation](https://github.com/xd009642/tarpaulin)
- [Coverage Analysis](./COVERAGE_ANALYSIS.md)
- [Test Snapshots](./test_snapshots/test/)

## Summary

✅ 32 comprehensive tests  
✅ 92.16% line coverage  
✅ 100% functional coverage  
✅ All security constraints tested  
✅ Fast execution (0.28s)  
✅ Production-ready quality
