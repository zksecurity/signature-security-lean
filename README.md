# Signature Security in Lean

Lean definitions, explicit reductions, and security proofs for BLS, OOPS, and Proximity signatures.

**Four security endpoints:** BLS to co-CDH, plus BLS/OOPS/Proximity in the query-only lazy AGM.
All four have checked axiom footprints without `sorryAx`. AGM bounds include both DLog
reductions and `1/|F|`; Proximity also includes the probability of a fresh linear collision.

Each public statement derives concrete arithmetic-machine solver budgets from a source-code
certificate, then applies hardness at those budgets. Hash/sign/random query caps and local work
are included, along with both AGM branches.
Concrete operation ledgers cover all four routes. See
[computational-security status](docs/COMPUTATIONAL-SECURITY.md).

Start with the [GitHub review guide](docs/review-guide.md) or the
[security-game ledger](docs/SECURITY-GAMES.md). Reviews and checklists can be recorded with the
[review issue template](https://github.com/zksecurity/signature-security-lean/issues/new?template=security-review.md).

## Build

Requires Lean `v4.34.0`, installed by elan from `lean-toolchain`.
The AGM library is the public
[`zksecurity/agm-lean`](https://github.com/zksecurity/agm-lean) dependency.

```sh
lake exe cache get
lake build Signatures SignaturesTest
```

CI runs both targets, including the endpoint axiom guards. A successful build does not
establish correspondence with the papers.

Pinned upstreams:
- [ArkLib](https://github.com/Verified-zkEVM/ArkLib): `7653a901ed466c88a2e61a3075011b73d7bb2316`
- [VCVio](https://github.com/Verified-zkEVM/VCVio): `f5119c64ebb055d69c143704e12eba6df7dc386c`
- [AGM Lean](https://github.com/zksecurity/agm-lean): `c207f29d1bba8b36fd6c09a0a3a6b4e82148b402`

## Scope

- The source games use lazy random oracles.
- Hashing, signing, and verification share a cache; internal lookups create no representation tokens.
- AGM reductions sample private finite tables. Their coupling to the lazy source is proved;
  no PPT-preservation or efficient lazy-reduction theorem is claimed.
- OOPS and Proximity use oracle-derived bases, not standard-model public setup parameters.
- ArkLib's representation API is compatibility-tested, not proved equivalent to the local model.
- The indexed AGM interface lives in `agm-lean`; token/output adapters, hash/signing access,
  and security proofs remain here.
- `Spec/` and `Model/` contain definitions; `Statement.lean` exposes the bounds; `Proofs/`
  contains extraction and coupling arguments; `SignaturesTest/` checks assumptions and regressions.
