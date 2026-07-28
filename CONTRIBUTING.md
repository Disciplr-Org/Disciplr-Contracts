# Contributing

Thanks for helping improve Disciplr Vault. This guide collects the contributor
workflow, testing commands, and pull request expectations that are otherwise
spread across the repository docs and bounty issues.

## Before You Start

- Fork the repository and create a focused branch for one issue or change.
- Introduce yourself in the project Discord when working on a bounty issue so a
  reviewer can be paired with your work.
- Read the issue acceptance criteria before editing. Keep pull requests narrow
  and avoid unrelated formatting churn.
- Do not commit secrets, wallet keys, private user data, or generated artifacts
  that are not required for review.

Suggested branch names:

```text
fix/<short-issue-name>
test/<short-issue-name>
docs/<short-issue-name>
```

Examples:

```text
fix/validate-milestone-deadline
test/create-vault-zero-amount
docs/contributor-guide
```

## Local Setup

Install the Rust toolchain and the Soroban-compatible dependencies used by the
contract. Then fetch the project dependencies with Cargo:

```bash
cargo fetch
```

The contract source lives in [`src/lib.rs`](src/lib.rs). Integration and
property tests live in [`tests/`](tests/). The main testing reference is
[`TESTING_GUIDE.md`](TESTING_GUIDE.md).

## Required Checks

Run these checks before opening a pull request:

```bash
git grep -n -E '^(<<<<<<<|=======|>>>>>>>)' -- .
cargo fmt -- --check
cargo clippy -- -D warnings
cargo test
```

For changes that touch contract logic, state transitions, or tests, also run a
coverage check when `cargo-tarpaulin` is available:

```bash
cargo tarpaulin --out Html --out Stdout
```

If `cargo tarpaulin` is not installed, mention that in the pull request and run
the standard Cargo checks above. See [`tarpaulin.toml`](tarpaulin.toml) and
[`COVERAGE_ANALYSIS.md`](COVERAGE_ANALYSIS.md) for the repository's coverage
expectations.

## Testing Guidance

- Add or update tests for every behavior change.
- Keep state-machine tests explicit about the initial state, action, and final
  state.
- Prefer exact error assertions for failure paths when possible.
- Review changes under `test_snapshots/` when tests update event snapshots.
- Keep tests fast and deterministic.

Useful commands:

```bash
cargo test
cargo test -- --nocapture
cargo test test_active_to_completed_via_release
cargo test should_panic
```

## Formatting And Style

- Use the repository's [`rustfmt.toml`](rustfmt.toml).
- Keep public API and event changes reflected in docs when relevant.
- Keep contract semantics synchronized across:
  - [`src/lib.rs`](src/lib.rs)
  - [`contract-interface.json`](contract-interface.json)
  - [`src/doc.md`](src/doc.md)
  - [`README.md`](README.md)
- Do not mix large refactors with bounty fixes unless the issue explicitly asks
  for it.

## Pull Request Expectations

Every pull request should include:

- The issue it fixes, such as `Fixes #123`.
- A short summary of the behavior or documentation change.
- The checks you ran and their results.
- Any checks you could not run, with the reason.
- Screenshots, sample output, or test evidence when requested by the issue.
- A note about reviewer pairing if the issue asks contributors to coordinate in
  Discord.

For bounty work, follow the issue-specific claim and payout instructions. Do not
assume a bounty is awarded until the maintainer reviews, tests, and merges the
pull request.

## Merge Hygiene

Before pushing, check for unresolved conflict markers:

```bash
git grep -n -E '^(<<<<<<<|=======|>>>>>>>)' -- .
```

The CI workflow runs this guard on every push and pull request. If it fails,
resolve the conflict locally, rerun formatting, build, and tests, then ask for
review again. See [`docs/MERGE_HYGIENE.md`](docs/MERGE_HYGIENE.md) for details.

## Documentation Updates

Update documentation whenever a change affects:

- Entrypoint behavior or error codes.
- Vault lifecycle semantics.
- Backend integration payloads.
- Testing or coverage expectations.
- Contributor or bounty workflow.

Small documentation-only fixes should still pass the merge-conflict marker
check. Run the full Cargo checks when documentation changes are coupled to code
or tests.

