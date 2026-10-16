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
see the [Schnorr review path](docs/SCHNORR.md). The general-caller endpoints for
Schnorr AGM and both ROM nonce conventions are described below.
Operation ledgers also cover the four pairing-based routes. See
[computational-security status](docs/COMPUTATIONAL-SECURITY.md).

The [general adversary reduction plan](docs/GENERAL-ADVERSARY-REDUCTION-PLAN.md)
records the broader efficiency work. BLS co-CDH now has a public security theorem
for general realized attacker code in a fixed quantitative backend, with derived
solver runtime/code bounds and a nonuniform asymptotic security corollary. It covers
arbitrary message types under explicit primitive/encoding contracts.
The [public BLS statements](Signatures/BLS/Statement.lean) now distinguish
`agm_security` (an algebraic attacker, twice one DLog bound plus `1/|F|`) from
`cocdh_security` (an unrestricted attacker, Coron factor times a co-CDH bound).
Each takes the curve, security parameter, query allowances, and adversary.
The DLog time allowance is the maximum of the two derived reduction times;
`agm_security_two_budgets` preserves the sharper bound using each time separately.
The [model and game definitions](Signatures/BLS/GeneralSecurityModel.lean) expose
attacker resources, primitive/encoding contracts, and explicit hardness suprema.
The [proofs](Signatures/BLS/Proofs/GeneralSecurity.lean) combine the original
probability reductions with derived native solver runtime/code certificates.
The [BLS AGM family corollary](Signatures/BLS/GeneralAGMFamilyStatement.lean)
also gives negligible forgery success from polynomial component resources,
nonuniform DLog hardness in one fixed backend, and negligible `1/|F|`.
Both reduction families' time and stored-code bounds are derived.
OOPS and Proximity also have general-caller concrete statements and nonuniform
family corollaries, with derived solver time/code bounds. Their degree/dimension
must grow polynomially; OOPS retains admissibility and Proximity retains its
fresh-collision probability. Schnorr AGM now has complete native runtime/code
certificates and a [short public theorem](Signatures/Schnorr/Statement.lean),
with exact finite-list execution, arbitrary messages and query-dependent storage.
It takes a single-group curve, security parameter, query allowances and algebraic
adversary, and displays DLog success plus the original query losses.
Its [polynomial-family corollary](Signatures/Schnorr/GeneralAGMFamilyStatement.lean)
derives negligible forgery from polynomial component resources, DLog hardness
and negligible inverse field size in one fixed backend. The same public file now
also exposes `Schnorr.rom_security` for unrestricted attackers, with the full-field
nonce signing/forking losses and a square-root DLog bound. Its complete replaying
solver has derived runtime/code bounds, and its
[nonuniform family corollary](Signatures/Schnorr/GeneralROMFamilyStatement.lean)
concludes negligible forgery from polynomial original resources in one fixed
backend. The same file now exposes `Schnorr.NonzeroNonce.rom_security`, with
signing denominator `|F|-1`, derived complete solver resources, and a separate
[nonuniform family corollary](Signatures/Schnorr/GeneralNonzeroROMFamilyStatement.lean).
Its family proof needs the same negligible inverse-field-size assumption.
All general-attacker route endpoints are proved; API retirement and final
integration checks remain tracked in the plan.
A conventional machine instantiation is separate from these conditional results.

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
