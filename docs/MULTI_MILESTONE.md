# Multi-Milestone Vaults

Vaults store an ordered `milestones: Vec<BytesN<32>>` plus a parallel
`milestone_validations: Vec<bool>`. Both vectors have the same length and index
`0` preserves the previous single-milestone behavior when callers submit a
one-item vector.

## Validation

`validate_milestone(vault_id, milestone_index)` marks exactly one milestone as
validated. The verifier authorization model is unchanged: a configured verifier
must authorize validation, and creator authorization is used when no verifier is
set.

The contract rejects:

- empty milestone vectors at creation
- out-of-range milestone indexes
- duplicate validation of the same milestone index
- validation at or after `end_timestamp`

## Release And Redirect

Before the deadline, `release_funds` requires every milestone validation flag to
be `true`. After the deadline, the existing deadline release path still applies.

`redirect_funds` remains available only after the deadline and only while not
every milestone has been validated, so a partially completed vault can still be
routed to `failure_destination` after the window closes.
