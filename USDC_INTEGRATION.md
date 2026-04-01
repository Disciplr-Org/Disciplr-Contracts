# USDC Integration and Trust Model

This document describes both:

- The current USDC token integration used by the Disciplr vault contract.
- The external trust assumptions that still apply when production USDC is used on Stellar.

## Overview

`create_vault` currently transfers USDC from the creator into the vault contract using the Soroban token interface. That means Disciplr now depends on two layers of security:

- The local contract logic in this repository.
- The issuer/admin controls and operational policies of the external USDC asset.

Disciplr can enforce escrow workflow rules, but it cannot remove powers held by the underlying USDC issuer or asset administrator.

## Current On-Chain Integration

### Function signature

```rust
pub fn create_vault(
    env: Env,
    usdc_token: Address,
    creator: Address,
    amount: i128,
    start_timestamp: u64,
    end_timestamp: u64,
    milestone_hash: BytesN<32>,
    verifier: Option<Address>,
    success_destination: Address,
    failure_destination: Address,
) -> Result<u32, Error>
```

### Token transfer mechanism

The contract pulls USDC into escrow during vault creation:

```rust
let token_client = token::Client::new(&env, &usdc_token);
token_client.transfer(&creator, &env.current_contract_address(), &amount);
```

Properties:

- The creator must authorize the call.
- The transfer and vault creation happen atomically.
- If the transfer fails, the vault is not created.

## Core Trust Assumptions

### 1. Disciplr does not control USDC monetary policy

Disciplr is an application-layer escrow workflow. It does not mint, redeem, freeze, claw back, pause, or upgrade the USDC asset. Those powers remain with the issuer and any admin-capable roles defined by the production asset.

Implications:

- A correct Disciplr contract cannot remove issuer-level powers from the underlying asset.
- Users still inherit the operational, governance, and compliance risk of the integrated USDC asset.

### 2. Issuer and admin powers may override escrow expectations

On Stellar, asset-level controls may affect transferability depending on the asset configuration and issuer policy.

Implications:

- A vault reaching `Completed`, `Failed`, or `Cancelled` does not guarantee settlement if the asset itself is frozen, paused, blacklisted, or otherwise restricted.
- Incident response must treat issuer-side actions as a separate failure domain from Disciplr contract bugs.

### 3. Asset migrations and admin-key changes are security events

If production USDC is migrated to a new issuer, a new Stellar Asset Contract, or a new operational policy, the integration assumptions here must be re-reviewed before new vaults are created.

Implications:

- Treat issuer rotations, admin-key rotations, and asset-address changes as release-blocking events.
- Re-validate the exact asset identifier and admin model before deployment and after any issuer-announced migration.

## Deployment Checks

Before using production USDC, operators should confirm:

1. The exact Stellar asset or Stellar Asset Contract address being integrated.
2. The issuer account and any admin-capable roles attached to that asset.
3. Whether the asset can be frozen, clawed back, blacklisted, paused, or migrated.
4. Whether issuer compliance or redemption workflows can delay settlement.
5. Whether the token address passed to contract calls matches the intended production asset.

## Contract-Level Guarantees

The contract can currently guarantee only local properties such as:

- creator authorization
- amount and timestamp validation
- vault state persistence
- milestone validation timing rules
- status-transition checks for release, redirect, and cancel flows

The contract cannot guarantee:

- that the USDC asset remains transferable
- that issuer/admin policies remain unchanged after deployment
- that off-chain redemption or compliance workflows settle instantly

## Security Notes for Auditors

- The `usdc_token` address is supplied at call time and is not pinned inside vault state.
- The integrated token contract is therefore part of the effective security boundary.
- Production review should include both the Disciplr contract and the chosen Stellar USDC asset configuration.

## Related Documentation

- [README.md](README.md)
- [vesting.md](vesting.md)
- [src/lib.rs](src/lib.rs)

## Primary References

- Stellar Docs: https://developers.stellar.org/docs/tokens/how-to-issue-an-asset
- Soroban token interface: https://developers.stellar.org/docs/tokens/token-interface
- Circle USDC risk factors: https://www.circle.com/legal/usdc-risk-factors
