# Signature Security in Lean

Lean definitions, explicit reductions, and security proofs for BLS, OOPS, Proximity, and Schnorr signatures.

**Security routes:** BLS to co-CDH, BLS/OOPS/Proximity in the query-only lazy AGM,
Schnorr ROM security to DLog with costed rewinding, and adaptive Schnorr AGM security
with a single-pass DLog solver. Schnorr also has a separate nonzero-nonce ROM theorem.
The endpoints have checked axiom footprints without `sorryAx`. The pairing-based AGM bounds
include both DLog reductions and `1/|F|`; Proximity also includes the probability of a fresh
linear collision. Schnorr AGM has loss `(qH+1)/|F| + qS*(qS+qH)/|F|`.

The pairing-based and full-field Schnorr ROM statements derive concrete arithmetic-machine
solver budgets from a source-code certificate, then apply hardness at those budgets. Hash/sign/random query caps and local work
are included, along with both AGM branches.
Schnorr also has a concrete bit-heap-machine theorem, charging both replay runs,
input loading, arithmetic, memory scans, and sampling, with explicit rejection error
and a separate stored-code/data bound;
see the [Schnorr review path](docs/SCHNORR.md). The Schnorr AGM and nonzero-nonce theorems
are probability reductions, with no machine-time certificate claimed for those variants.
Operation ledgers also cover the four pairing-based routes. See
[computational-security status](docs/COMPUTATIONAL-SECURITY.md).

The [general adversary reduction plan](docs/GENERAL-ADVERSARY-REDUCTION-PLAN.md)
records the broader efficiency work. BLS co-CDH now has a public security theorem
for general realized attacker code in a fixed quantitative backend, with derived
solver runtime/code bounds and a nonuniform asymptotic security corollary. It covers
arbitrary message types under explicit primitive/encoding contracts.
BLS AGM now also has complete lazy native solver runtime/code certificates and
a [short public statement](Signatures/BLS/GeneralAGMStatement.lean), including a
version indexed by the security parameter. Its
[supporting parameters and adversary records](Signatures/BLS/GeneralAGMParameters.lean)
expose query limits, general attacker resources, and primitive/encoding contracts.
The bound is the sum of two resource-indexed DLog advantages plus `1/|F|`.
Conventional-machine instantiation, the BLS AGM asymptotic corollary, and
general-attacker overhead for the other routes remain in progress.

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
- The original pairing-based AGM reductions sample private finite tables. BLS additionally has
  lazy reductions with sparse extraction, finite-list cache refinement, and the same probability
  bound over arbitrary message types. Their complete native runtime/code certificates
  and general-caller composition are proved under explicit backend contracts;
  no PPT-preservation claim follows from query bounds alone.
- The Schnorr AGM solver records each fresh hash point's affine representation before its
  challenge, retaining the first record on cache hits.
- OOPS and Proximity use oracle-derived bases, not standard-model public setup parameters.
- ArkLib's representation API is compatibility-tested, not proved equivalent to the local model.
- The indexed AGM interface lives in `agm-lean`; token/output adapters, hash/signing access,
  and security proofs remain here.
- `Spec/` and `Model/` contain definitions; `Statement.lean` exposes the bounds; `Proofs/`
  contains extraction and coupling arguments; `SignaturesTest/` checks assumptions and regressions.
