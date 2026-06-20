# Redirect Guards

`redirect_funds` is only valid for an active vault whose deadline has passed and
whose milestone was not validated. Once `milestone_validated` is true, the
failure path is closed: a redirect attempt returns `Error::NotAuthorized` and
must not move funds or change vault status.

This preserves the payout invariant:

- validated vaults can still be completed through `release_funds`, including
  after `end_timestamp`;
- unvalidated vaults can be redirected only after `end_timestamp`;
- a rejected redirect keeps the vault `Active` so the valid success path remains
  available.

The integration coverage for this invariant lives in
`tests/redirect_validation.rs`.
