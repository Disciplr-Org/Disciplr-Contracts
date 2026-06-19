# Merge Hygiene

Unresolved merge conflict markers make the contract source invalid and can hide
which side of a change reviewers are actually approving. Before pushing a branch,
run:

```bash
git grep -n -E '^(<<<<<<<|=======|>>>>>>>)' -- .
```

The CI workflow runs the same check on every push and pull request. If the check
fails, resolve the conflict locally, keep the intended code or documentation, and
rerun `cargo fmt -- --check`, `cargo build`, and `cargo test` before asking for
review.
