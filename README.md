# Signature Security in Lean

Lean definitions, explicit reductions, and security proofs for BLS, OOPS, Proximity, and Schnorr signatures.

**Security routes:** BLS to co-CDH, BLS/OOPS/Proximity in the query-only lazy AGM,
Schnorr ROM security to DLog with costed rewinding, and adaptive Schnorr AGM security
with a single-pass DLog solver. Schnorr also has a separate nonzero-nonce ROM theorem.
The endpoints have checked axiom footprints without `sorryAx`. The pairing-based AGM bounds
include both DLog reductions and `1/|F|`; Proximity also includes the probability of a fresh
linear collision. Schnorr AGM has loss `(qH+1)/|F| + qS*(qS+qH)/|F|`.

The general-attacker statements derive complete reduction runtime and stored-code
bounds from the attacker's measured resources and explicit backend contracts.
They also have nonuniform polynomial-family corollaries. The superseded eager-table
AGM wrappers are retired; see the [API migration guide](docs/API-MIGRATION.md).
Arithmetic-source BLS co-CDH and Schnorr statements remain for their distinct
implementation models. Schnorr also has a bit-heap theorem charging replay,
input loading, arithmetic, scans and sampling, with explicit rejection error
and a separate stored-code/data bound. See the [Schnorr review path](docs/SCHNORR.md)
and [computational-security status](docs/COMPUTATIONAL-SECURITY.md).

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
All general-attacker route endpoints are proved and the eager AGM API is retired.
Full integration checks and the completion audit remain tracked in the plan.
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
- [Caliper](https://github.com/zksecurity/caliper): `b62f7c8be35df0aa728e5a6aac7bae85eef67449`,
  [vendored with the minimal Lean 4.34 port](vendor/caliper/UPSTREAM.md).

## Scope

- The source games use lazy random oracles.
- The separate [Caliper execution layer](Signatures/Runtime/Caliper.lean) supplies
  word programs, encoded field/group routine contracts, concrete local quantitative
  realizers, bounded layouts and local control, charged saved-state composition,
  mailbox transfers and tape replay. Bounded local loops have proved linear time
  and generated-code bounds. Bounded-source layouts retain the original source
  types with explicit capacity invariants. A charged word I/O adapter implements
  typed oracle calls with a proved equality to the source query. Interactive
  compilation covers every constructor of the existing reduction language,
  including loops controlled by a stored input counter. Decoding the compiled
  execution recovers the original source computation, including adaptive queries.
  Uniform time and additional-buffer bounds follow from bounds on actual local
  implementations, with copying and oracle-interface work included.
  The machine-memory account includes stored code, register and descriptor slots,
  initial data, and buffer capacity at every intermediate instruction boundary.
  Checked emission verifies generated names; all buffer lengths and capacities
  stay within the word width throughout accepted execution.
  Bounded list construction, empty/head-tail case analysis, and capacity growth
  have actual implementations with linear time and code bounds; copies, padding,
  and stored length updates are charged. Their source types remain ordinary lists.
  List folds now execute compiled bodies with retained tails and environments.
  Their proved polynomial bounds include every copy and stored branch; source
  refinement also supports entries and accumulators with bounded domains.
  Bounded natural arithmetic, comparisons, Boolean selection and finite-index
  conversions now have executed implementations. Addition requires a proved
  no-overflow bound; subtraction saturates at zero. Pairing two computations
  preserves their shared input through charged copying, with linear overhead
  bounds in the stored input and output widths.
  Checked expression compilation now covers variables, constructors, arithmetic
  instructions, branches, local bindings and folds. Accumulator domains and
  storage widths may grow at successive fold iterations; early returns execute
  the conversion to the final layout. Its result implements the original source
  expression; generated scratch names are checked before accepting a composition.
  Complete staged folds have uniform polynomial time and stored-code bounds
  derived from their layout widths and individual body/conversion budgets.
  Uniform budgets now cover the complete original-expression compiler, including
  fold input construction. Only primitive instructions and final-layout
  conversions supply budgets; all constructor overhead is derived structurally.
  Attaching the budget proof preserves the original accepted code and rejections.
  The compiler also derives dense register/descriptor reservations from primitive
  name limits and generated code size. Complete expression memory budgets count
  code, metadata, all initial capacity and dynamic growth at every intermediate
  and final state. Scheme families must still bound the primitive resources and
  layout sizes as functions of the security parameter.
  Equality now compares the stored encodings with a linear word scan. The original
  association-list lookup has a constructed compilation certificate and explicit
  polynomial time/code budgets in stored-entry capacity and encoding widths.
  Its retained-environment copies are charged, giving quadratic worst-case overhead.
  Structured-key lookup is compiled to the same code through a proved equality
  of source results, with complete memory bounds retained.
  Encoded lookup now has a total implementation for every admitted layout:
  compilation succeeds and uses at most seven buffer slots, independently of capacity.
  The original cache-programming expression also has a total implementation on
  its proved hit-or-room domain, preserving fixed capacity. Full-table hits keep
  existing entries, including cached zero. Insertions charge for copying and
  require a proved free slot. Time/code overhead beyond lookup is linear in
  stored widths; the complete operation uses at most eight buffer slots and has
  a proved memory bound including code, metadata and all initial capacity.
  Effectful cache reads also match the original source computation, including
  oracle calls. Hits return the stored value without a draw; misses save their
  frame across the primitive draw and insert its returned value. The proved
  overhead charges all copying and I/O, with explicit primitive draw resources.
  The sampling law remains a separate obligation of that primitive.
  This same cache code now refines the BLS AGM private list oracle. Both BLS
  reductions have a proved cache-capacity invariant at every adaptive source
  request, using their existing `2*q+1` query bound and represented-message
  assumptions. Complete reduction compilation remains to be connected.
  BLS's pair-valued cache now derives its sampler from two scalar draws, with
  proved independence, executed retention/permutation and complete memory bounds.
  It requires only the scalar sampler's implementation and sampling law.
  The BLS AGM response arithmetic also has constructed Caliper code, derived
  time/code budgets and complete memory bounds linked to the original source.
  Only scalar multiplication and group addition supply primitive implementations;
  the surrounding selection and saved-input copying are generated and charged.
  Recording the returned point in the transcript and joining this code to the
  private cache remain part of complete reply compilation.
  Cryptographic routines require Caliper code and proofs; encoded values remain
  inspectable by bit operations.
  [Remaining integration work](docs/CALIPER-BACKEND-PLAN.md) includes completing
  scheme compilation and capacity invariants, and linking
  replay controllers. The signature
  security models still use their explicit backend contracts; this layer does not
  yet discharge them.
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
- BLS, OOPS, and Proximity accept the shared `agm-lean` interactive adversary directly.
  It supplies actual group outputs and chronological explanations; the games run it directly.
  [Internal regrouping](Signatures/Model/Proofs/DirectAGM.lean) transfers the existing
  extraction proofs and query bounds. Backend caller budgets include producing the derived
  coefficient encoding. Hash/signing access and security proofs remain here.
- `Spec/` and `Model/` contain definitions; `Statement.lean` exposes the bounds; `Proofs/`
  contains extraction and coupling arguments; `SignaturesTest/` checks assumptions and regressions.
