# Protocol Fees

Each vault stores an optional protocol fee configuration at creation time:

- `fee_bps`: basis-point fee charged when `release_funds` or `redirect_funds` settles the vault.
- `fee_recipient`: address that receives the protocol fee.

`fee_bps` must be between `0` and `MAX_FEE_BPS` (`1000`, or 10%). Values above the cap return `Error::InvalidFee` before the creator's funds are transferred into escrow.

## Formula

The settlement fee is rounded up in the protocol's favor:

```text
fee = ceil(amount * fee_bps / 10_000)
net = amount - fee
```

When `fee_bps == 0`, the fee is `0` and settlement matches the original behavior exactly: the full vault amount goes to the success or failure destination and no `fee_collected` event is emitted.

## Example

For a vault with `amount = 1_000_000_000` stroops and `fee_bps = 250`:

```text
fee = ceil(1_000_000_000 * 250 / 10_000) = 25_000_000
net = 975_000_000
```

On success, `release_funds` sends `25_000_000` to `fee_recipient`, sends `975_000_000` to `success_destination`, emits `fee_collected`, and then emits `funds_released` with the net amount.

On failure, `redirect_funds` applies the same fee split but sends the net amount to `failure_destination`.
