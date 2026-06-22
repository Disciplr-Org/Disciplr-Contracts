# Partial Release

Disciplr vaults support tranche-based success payouts through `release_partial`.
A vault still records the original escrowed `amount`, and it also tracks
`remaining_amount` as the source of truth for future payouts, redirects, or
cancellation refunds.

## Invariants

- `remaining_amount` starts equal to `amount`.
- Every partial release must be positive and no greater than `remaining_amount`.
- A partial release transfers only the requested tranche to `success_destination`.
- The vault stays `Active` while `remaining_amount > 0`.
- The vault becomes `Completed` when `remaining_amount == 0`.
- `release_funds` preserves the old full-release behavior by releasing the
  current `remaining_amount` in one call.
- `redirect_funds` and `cancel_vault` transfer only `remaining_amount`, so prior
  success tranches cannot be paid twice.

## Worked Example

A creator funds a vault with `30_000_000` stroops.

1. `remaining_amount = 30_000_000` after creation.
2. The verifier validates the milestone.
3. `release_partial(..., 10_000_000)` sends `10_000_000` to
   `success_destination` and stores `remaining_amount = 20_000_000`.
4. The vault remains `Active`.
5. A final `release_funds(...)` sends the remaining `20_000_000` and marks the
   vault `Completed`.

Deadline-based releases use the same authorization gate as `release_funds`. If
a creator releases a partial tranche after the deadline without milestone
validation, the unreleased remainder can still be redirected to
`failure_destination` because the milestone remains unvalidated.
