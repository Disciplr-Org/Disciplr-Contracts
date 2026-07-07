# Partial Milestone Release

`release_partial` lets a vault pay a tranche of its escrowed USDC balance to the
`success_destination` while keeping the vault `Active` for the unreleased
balance.

## Balance Model

- `amount`: original escrowed amount.
- `remaining`: unreleased balance still held by the vault.

A partial release must satisfy:

```text
0 < release_amount <= remaining
new_remaining = remaining - release_amount
```

The contract uses checked subtraction and rejects invalid release amounts with
`Error::InvalidAmount`.

## Lifecycle

1. `create_vault` sets `amount` and `remaining` to the initial escrow amount.
2. `release_partial` transfers `release_amount` to `success_destination`.
3. The vault remains `Active` while `remaining > 0`.
4. The final tranche sets `remaining = 0` and moves the vault to `Completed`.
5. `release_funds` preserves legacy behavior by releasing all `remaining` funds.

## Worked Example

A creator escrows 10,000 USDC:

| Step | Action | Paid | Remaining | Status |
| --- | --- | ---: | ---: | --- |
| 1 | create vault | 0 | 10,000 | Active |
| 2 | release_partial(2,500) | 2,500 | 7,500 | Active |
| 3 | release_partial(3,000) | 3,000 | 4,500 | Active |
| 4 | release_funds() | 4,500 | 0 | Completed |

`cancel_vault` and `redirect_funds` only transfer `remaining`, so cumulative
payouts can never exceed the original `amount`.
