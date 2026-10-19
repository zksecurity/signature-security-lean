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
The concrete and nonuniform asymptotic BLS AGM statements now use Caliper. The
other routes retain abstract-backend family corollaries during migration. The
superseded eager-table AGM wrappers are retired; see the [API migration guide](docs/API-MIGRATION.md).
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
probability reductions with derived solver certificates. The public AGM theorem
now uses actual Caliper programs with stored-code, runtime and total-memory bounds.
Its [parameters](Signatures/BLS/CaliperAGMParameters.lean) fix layouts, implemented
primitives, sampling and caller allowances before the attacker is chosen; the
attacker supplies its local code and correspondence proofs. Complete reduction
efficiency follows from those components. The co-CDH theorem still uses the
abstract backend.
The [Caliper BLS AGM family corollary](Signatures/BLS/CaliperAGMFamilyStatement.lean)
gives negligible forgery success from polynomial component resources,
nonuniform Caliper DLog hardness, and negligible `1/|F|`. Both reduction families'
time, stored code and total memory are derived from primitive/caller bounds,
encoding widths and capacities. Word width must also grow polynomially; field
cardinality and numerical sampling ranges need not. The earlier
[abstract-backend family theorem](Signatures/BLS/GeneralAGMFamilyStatement.lean)
remains a separate result.
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
  assumptions. The complete reductions are now connected through `BLSFull` below.
  BLS's pair-valued cache now derives its sampler from two scalar draws, with
  proved independence, executed retention/permutation and complete memory bounds.
  It requires only the scalar sampler's implementation and sampling law.
  The BLS AGM response arithmetic also has constructed Caliper code, derived
  time/code budgets and complete memory bounds linked to the original source.
  Only scalar multiplication and group addition supply primitive implementations;
  the surrounding selection and saved-input copying are generated and charged.
  Recording the returned point in either transcript also has constructed code,
  derived copying budgets and complete memory bounds. The original adaptive
  source's query allowance proves that a slot remains before each delivered
  reply, including repeated queries. Both complete BLS AGM reply handlers now
  join the lazy cache, response arithmetic and recorder in executed word code.
  The refinement preserves the reply, stored challenge configuration, cache and
  both logs jointly. Derived time, code and complete intermediate-memory bounds
  charge every saved-frame copy. The bad branch constructs its pair sampler
  from two scalar draws. A stored-tag dispatcher now executes either reply,
  charging time for the selected branch and code space for both branches.
  A shared invariant preserves configuration, cache and transcript domains and
  reserves room along every supported adaptive source prefix. The query allowance
  supplies the complete reply guard; no per-call capacity certificate is assumed.
  Supported dispatcher returns carry the updated store and remaining reservation.
  Two-call word-execution tests choose the next request from the first reply's
  encoded bits, preserving cache/log storage through executed copies.
  The full BLS AGM query service also forwards runtime-selected random queries
  through a common word port. Its source equality and derived resource bounds
  cover random/hash/sign branches jointly, including their stored tags and
  padding. Tests interleave private scalar draws and adversary randomness in
  one program. Generated caller steps now preserve caller state across a handler
  call and the private store across a local continuation, with linear time/code
  overhead from executed copies. Interactive loops can carry decreasing capacity
  reservations, and retain time and complete memory bounds on their reachable
  domains. Regressions execute adaptive next-request selection across two calls.
  Complete generated controllers now include initialization, early return and
  observable cutoff, with proved time, stored-code and complete memory bounds.
  A bridge to the original attacker machine preserves its final private store;
  the original implementation certificate identifies the source program and
  excludes cutoff. BLS request/reply packet conversions now execute their tag,
  padding and private-store copies with linear overhead bounds. The composed BLS
  handler has proved original-oracle correspondence, including dependent random
  reply ranges, and preserves the remaining cache/transcript reservations.
  The constructed BLS caller now connects this handler to actual local initialization
  and continuation code. Its executed word program agrees with the original source
  computation, and its time, stored code and every intermediate memory state are
  bounded from primitive and local caller resources. Its returned store retains
  the configuration and has at most one new cache entry and transcript token per
  call, including early returns and cutoffs. From an empty store, cache capacity
  `2*q + 1` leaves room for extraction after `q` calls; transcript capacity remains
  `q`. Both BLS AGM setup branches
  now execute their runtime challenge selection and empty-store construction;
  the sampled branch also executes scalar sampling and public-key multiplication.
  Their source correspondence and resource bounds are proved. BLS transcript
  reversal now executes charged list folds, with proved chronological ordering,
  time, stored-code and intermediate-memory bounds. Bounded coefficient lookup
  now also has executed Caliper code and derived resource bounds, including
  scanning the suffix after a match and returning the runtime default on a miss.
  Chronological coefficient-row assembly now executes both reversals, bounded
  indexing, counter increments and row allocation, with a proof that it implements
  the original AGM row expression. Missing coefficients use zero; surplus entries
  remain charged and create no rows. A private read followed by scalar or pair
  accumulation now has executed code, source agreement, and derived time, code
  and intermediate-memory bounds. Pair sampling and arithmetic are constructed
  from the scalar routines. The bounded row-evaluation loop now executes request
  construction, private reads and these updates in source order, with time,
  stored-code and all-visited-memory bounds. Its cache reservation counts actual
  remaining rows, and its source equality preserves the final private cache.
  Row preparation, zero creation and evaluation now compose into complete
  scalar and pair transcript evaluators, with source `evalTerms` equality and
  derived resource bounds. Missing coefficients still perform their lookups;
  surplus coefficients cause no additional queries.
  The final private lookup and scalar extraction arithmetic now also execute
  constructed programs, with original-oracle equality and time, code and
  intermediate-memory bounds. Both branches preserve total division semantics
  and the updated cache. Final-request packing now also executes its copies,
  default construction and the good branch's `beta + hashes` addition, with
  derived resource bounds. Signature-transcript evaluation, physically saved
  forgery context and final extraction now compose in both branches, with exact
  original-oracle semantics, a proved remaining-slot invariant, accepted word
  operands, and time, code and all-visited-memory bounds. Initial forgery/log/cache
  routing and the handoff after hash evaluation now also execute charged word
  copies, with exact encoding, time/code and all-visited-memory proofs. Their
  bounded inputs include both explanations and both logs, even when the bad
  branch discards hash data. Both complete BLS AGM extractors now compose these
  routes, transcript evaluation and final extraction. The good branch retains
  the signature transcript across its hash pass, and every supported hash result
  preserves the remaining cache reservation. Their erased results equal the
  original `goodFinish`/`badFinish` programs, including final cache and query
  order, with full time, code, intermediate-memory and operand-acceptance proofs.
  Caller-exit handling now executes tag dispatch, removal of padded configuration
  data, extraction, and scalar projection, with a literal zero for cutoff.
  The generated caller now composes with this terminal handler. Its growth proof
  supplies extraction room, and local source correspondence gives equality to
  the original caller followed by extraction. Combined time, stored-code,
  intermediate-memory and operand-acceptance bounds are proved. Executed tests
  instantiate both actual extractor programs, including adaptive queries and
  cutoffs. Both complete BLS AGM programs now execute setup before this pipeline,
  using actual scalar/group primitives and local caller code. Their erased
  executions equal the original lazy reductions, including the bad-case setup
  scalar, and their bounds charge setup, stored code and initial challenge data.
  Both original reductions now have certificates in a fixed Caliper DLog class
  that bounds stored code, online time and total memory. A concrete BLS AGM
  security theorem derives the usual probability bound from those certificates,
  including the shared AGM source game. The public `BLS.agm_security` wrapper now
  uses these Caliper certificates and a model fixed before attacker choice.
  Its polynomial-family corollary now uses the same Caliper model, with complete
  derived resource bounds. The caller's oracle-machine presentation can now be
  constructed from its local transitions and branchwise query termination; its
  private state need not duplicate the separately stored pending query. For BLS,
  the convenient constructor requires complete key and point representations.
  Local code certificates and correspondence with the algebraic source remain
  explicit; broader caller coverage remains to be proved.
  Cryptographic routines require Caliper code and proofs; encoded values remain
  inspectable by bit operations.
  [Remaining integration work](docs/CALIPER-BACKEND-PLAN.md) includes completing
  scheme compilation and capacity invariants, and linking
  replay controllers. BLS co-CDH, OOPS, Proximity and Schnorr still use their
  explicit abstract-backend contracts pending migration.
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
