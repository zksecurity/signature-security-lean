# Full Runtime Certification

Goal: discharge the runtime premises for all five security routes, not just count selected
operations. Both AGM branches and Schnorr's replay controller are certified. Existing probability statements and their
assumptions must be preserved, or any implementation replacement must have a proved probability
equivalence. The operation ledgers alone do not complete this goal.

The broader [general adversary plan](GENERAL-ADVERSARY-REDUCTION-PLAN.md) now has
a complete BLS co-CDH native solver and public conditional security endpoint.
Its general caller uses actual quantitative init/head/update code; `RunsWithin`
derives the caller invariants and budgets. Initialization, native handlers,
extraction, adapters, copying, and stored code have proved bounds in the same
fixed backend used by hardness. See
[`BackendCoronSecurity`](../Signatures/Runtime/BackendCoronSecurity.lean) and
[`BackendCoronPolynomial`](../Signatures/Runtime/BackendCoronPolynomial.lean).
[`BackendCoronFamilySecurity`](../Signatures/Runtime/BackendCoronFamilySecurity.lean)
connects those derived bounds to negligible forgery success for polynomial-time,
polynomial-code/advice nonuniform families. The backend remains fixed; group
types and representations may vary with the security parameter. This result is
conditional on primitive/encoding contracts and covers arbitrary message types
without any runtime dependence on the full message-domain cardinality.
The original arithmetic-source results documented below remain available.
Conventional-machine instantiation and the
remaining signature routes are still open.

For BLS AGM, both new lazy solvers now have exact probability correspondence and
a proved finite-list cache representation, with the same success bound over
arbitrary message types. Their query/transcript/cache-entry
bounds depend on attacker queries; no message-domain enumeration is performed.
Both [native private caches](../Signatures/Runtime/BackendLazyAGMCache.lean) now
have complete access-time, encoded-output, and stored-description bounds. The
bad branch's pair sampler is derived from two implemented scalar samplers,
with retention and construction charged. Exact semantics preserve the answer,
list update, and surrounding store; hits preserve the full costed run under
sampler replacement. The [native hash/sign replies](../Signatures/Runtime/BackendLazyAGMReply.lean)
preserve the joint adaptive output, cache, and transcript law. Their stored
descriptions, [encoded-store bounds](../Signatures/Runtime/BackendLazyAGMStateSize.lean),
and [complete runtime bounds](../Signatures/Runtime/BackendLazyAGMReplyBudget.lean)
are proved. Cache and reply-list lengths are counted separately; the cache scan
charges retention of the complete original argument environment. The runtime
bounds include initialization, sampling, arithmetic, transcript construction,
copying, and control, with no finite-message premise or assumed whole-reply
budget. Native [chronological coefficient matching](../Signatures/Runtime/BackendTokenRows.lean)
now composes the actual transcript reversal, zero initialization, positional
attachment, and final row reversal with complete time, stored-code, and output-size
bounds. Its coefficient scans charge the entire list, including surplus entries,
and every retained context contributes to the encoded-size cost. The
[output-size recovery](../Signatures/Runtime/BackendLazyAGMOutputSize.lean)
bounds these list lengths under an explicit positive-cell encoding law.
The [native row evaluators](../Signatures/Runtime/BackendLazyAGMEvaluate.lean)
and [complete good/bad extractors](../Signatures/Runtime/BackendLazyAGMExtraction.lean)
now have exact joint output/cache correspondence. Their source phases are the
suffixes of the established lazy solvers, and
[cache growth](../Signatures/Runtime/BackendLazyAGMExtractionGrowth.lean) is bounded
by processed rows plus the final target. The actual
[length fold](../Signatures/Runtime/BackendLengthCost.lean) has runtime and code
bounds. Private extraction reads have
[complete derived runtime](../Signatures/Runtime/BackendLazyAGMReadBudget.lean)
and [stored-description bounds](../Signatures/Runtime/BackendLazyAGMReadDescription.lean),
including routing, fallback construction, scanning, sampling, and copying.
Whole-evaluator/extractor [stored-code bounds](../Signatures/Runtime/BackendLazyAGMExtractionDescription.lean)
are now proved. Complete [good](../Signatures/Runtime/BackendLazyAGMGoodEvaluate.lean)
and [bad](../Signatures/Runtime/BackendLazyAGMBadEvaluate.lean) evaluator runtime
bounds instantiate the component and remaining-indexed loop certificates. They
charge count computation, initialization, row/cache scans, sampling, arithmetic,
retained context, loop tests, and projection. Bounds depend on actual row/cache
capacities and encodings, not the message universe. The only cost assumptions
are individual primitive, sampler, and control-instruction contracts. Complete
chronological [good](../Signatures/Runtime/BackendLazyAGMGoodTokens.lean) and
[bad](../Signatures/Runtime/BackendLazyAGMBadTokens.lean) preparation/evaluation
calls now have combined runtime/encoding bounds and key-validity/cache-growth
invariants. Complete [good](../Signatures/Runtime/BackendLazyAGMGoodExtractionBudget.lean)
and [bad](../Signatures/Runtime/BackendLazyAGMBadExtractionBudget.lean) extractor
runtime bounds now compose all chronological calls, default creation, final
target access, and field arithmetic. The bounds charge retained caller frames,
including all attacker output and both transcripts, and preserve cache growth
and key-size invariants. No finished-call or extractor runtime budget is assumed.
Both native general-request [dispatchers](../Signatures/Runtime/BackendLazyAGMHandler.lean)
now have derived [runtime](../Signatures/Runtime/BackendLazyAGMHandlerBudget.lean)
and [stored-code](../Signatures/Runtime/BackendLazyAGMHandlerDescription.lean)
bounds, including decoding, request retention, dependent reply tags, and one
dynamic random sampler. The native general-caller phase preserves adaptive source
semantics. Its [runtime/resource bounds](../Signatures/Runtime/BackendLazyAGMCallerResources.lean)
and complete stored-code bounds are now derived for both branches. Measured
attacker resources supply request/return sizes, reachability, local/query budgets,
and termination. The [AGM output bound](../Signatures/Runtime/BackendLazyAGMCallerOutput.lean)
covers the message and both coefficient lists, including surplus coefficients,
using the canonical output encoding and an explicit positive-cell list law.
Complete [native solver programs](../Signatures/Runtime/BackendLazyAGMSolver.lean)
now assemble setup, caller execution, output adaptation, and extraction. Their
[exact source correspondence](../Signatures/Runtime/BackendLazyAGMSolverCorrectness.lean)
is proved, including resource-derived termination. The complete
[setup bounds](../Signatures/Runtime/BackendLazyAGMSolverSetup.lean),
[terminal bounds](../Signatures/Runtime/BackendLazyAGMSolverTerminal.lean), and
[solver runtime composition](../Signatures/Runtime/BackendLazyAGMSolverBudget.lean)
are now proved from primitive contracts and the attacker's own resources.
Both complete [stored-code bounds](../Signatures/Runtime/BackendLazyAGMSolverDescription.lean)
charge all sampler, handler, extractor, adaptation, and cutoff code. The
[resource certificates](../Signatures/Runtime/BackendLazyAGMSolverWithin.lean)
construct actual executables for both named list reductions, and the
[security endpoint](../Signatures/Runtime/BackendLazyAGMSecurity.lean) supplies
them to DLog hardness in the same fixed backend. No finite-message or
finished-solver budget premise is added. The
[public statement](../Signatures/BLS/Statement.lean) names the curve, security
parameter, query allowances, and algebraic adversary. Its separate execution model
keeps setup and attacker obligations inspectable. The original three-term bound
uses DLog advantages indexed by the derived resource budgets. The theorem is
concrete at each security parameter; an AGM negligible-success
corollary still requires polynomial-family closure and asymptotic hardness.
The [general adversary plan](GENERAL-ADVERSARY-REDUCTION-PLAN.md#lazy-bls-agm-progress-2026-10-14)
tracks the remaining schemes, family corollaries, and interface work.
The complete AGM machine certificates documented below cover the older eager solvers.

OOPS and Proximity now have [native term generators](../Signatures/Runtime/BackendWeightedTerms.lean)
whose semantic indices are the original finite weighted term lists. Their
runtime and stored-code bounds are derived from primitive and structural
contracts, with explicit encoded-output bounds. They retain the constant term
and every zero-weight term, and charge all retained frames. These are verified
components. Proximity's tuple encoding is bounded from its coordinates, and
[structured key equality](../Signatures/Runtime/BackendWeightedKeyEquality.lean)
has native runtime/code bounds for both schemes. The
[native weighted private caches](../Signatures/Runtime/BackendWeightedCache.lean)
now charge both scalar and independent-pair sampling, the compiled comparison
and its input adapter, finite-list scan/insertion, and retained state. Exact
source-index encoding laws preserve Proximity's constant/coordinate distinction
and both cache branches. Cache hits preserve the entire costed run under
sampler replacement. No finite topic/slot premise or completed-cache budget is
assumed. Weighted hash/sign dispatch, extraction, and general-caller composition
remain in progress.

The working target is a first-order arithmetic/stack/list runtime with explicit cryptographic
primitive costs. It charges local computation, control flow, sampling, storage, and oracle
simulation. No arbitrary semantic function is a free instruction. A separate
[bit backend](BIT-COMPLEXITY.md) now supplies fixed primitive code,
execution, code-size, and local/program natural-range proofs. A shared bit-tape
heap and compiled expression controller have semantic, allocation, and actual
step bounds, including register-frame copies and folds. Argument frames and
binary counted loops have refinement/cost proofs. The whole-program controller
has query-tree, allocation, and aggregate bit-step refinement under concrete
handler refinement/cost premises, with width checks derived from source budgets.
The fair-bit rejection controller also has CPU/query bounds and exact output
and bad-event laws, including charged padding and a flagged zero fallback.
All four concrete machine effects now instantiate the program-body theorem,
using the original ideal-machine budget via support inclusion. Initialization
and input/fixed-data loading compose into a complete package theorem, instantiated
on the actual Schnorr two-pass extractor in `SchnorrBits`. Its online bound is
`(targetBudget + 4) * bitFactor`. Encoded inputs are the representation boundary;
compiler runtime and Lean VM timing are not covered. Adaptive sampling-tree
composition now bounds the accumulated error by `targetBudget * 2^(-k)`;
the exact whole-package probability bridges and final security substitution
are proved in `MachineProbability`, `HeapProbability`, `SchnorrBits`, and
`Schnorr.BitStatement`. The public bit theorem assumes DLog hardness for actual
compiled heap programs at `(targetBudget+4)*bitFactor`, with stored code/data
bounded by the actual compiled package's `cells`, and adds this sampling error
to the original forking inequality. Support refinement alone is not used
as a probability bridge.

## Completion gates

- [x] Executable first-order program language and accounting for all local steps, including
  loops and oracle continuations; erasure to `OracleComp` and operational soundness.
- [x] Fixed cryptographic primitive instruction set, with explicit field/group/equality/index
  and random-sampling costs. No whole-solver primitive or opaque free function.
- [x] Concrete private-table initialization and lookup implementations with proved costs and
  uniformity/equivalence to the existing AGM samplers.
- [x] Concrete persistent scalar/coin caches for Coron, including repeated queries, signing,
  and the automatically inserted final forgery hash; proved size and time bounds.
- [x] Source adversary implementation certificate including local computation, random requests,
  message sizes, and algebraic output sizes on every adaptive branch and generated key.
- [x] Compiled implementations of all reductions, including both AGM extractors, with exact
  behavior/probability correspondence to the named solvers in the security theorems.
- [x] Concrete total bounds derived from source and primitive budgets, with no assumed bound
  for the finished reduction and no uncharged pure computation.
- [x] Instantiate the hardness resource predicate with these implementations and discharge
  `hbudget`, `hgood`, and `hbad` in public concrete-runtime security corollaries.
- [x] Full regression build, axiom guards, and negative tests rejecting zero-cost arbitrary
  pure computation, omitted sampling/cache cost, and the wrong solver or generated key.

## Current evidence

Coron's complete closed-machine certificate is proved, including source input construction,
fixed-data loading, final extraction, exact named-solver equivalence, and discharge of the
public solver-budget premise. Both AGM branches have complete named-solver `Machine.Within`
certificates. The three public scheme-specific runtime corollaries discharge `hgood` and `hbad`
using the compiled BLS/OOPS/Proximity equality and weight functions. All four routes preserve
their original probability statements, with hardness and primitive costs remaining explicit
assumptions. The full regression build and public axiom/signature guards check these endpoints.

Schnorr's fifth endpoint is also complete: the source certificate derives the full
two-pass machine budget, and exact query-tree equality identifies that machine with
VCVio's named DLog reduction. Retained randomness, reset/re-execution, cache/tape scans,
verification, extraction, fallback, and fixed-data loading are all charged. See the
[Schnorr review path](SCHNORR.md) and
[`SourceCertificate.within`](../Signatures/Runtime/SchnorrReduction.lean).

- [`Language.lean`](../Signatures/Runtime/Language.lean): de Bruijn stack variables, constructors,
  branches, local bindings, primitive instructions, and list folds. Erasure is proved, and pure
  expressions have positive runtime. There is no arbitrary host-function expression constructor.
- [`Program.lean`](../Signatures/Runtime/Program.lean): first-order oracle calls, sequencing,
  branches, bounded loops, and first-order procedure calls. Call arguments and stack frames
  are evaluated and charged. The interpreter charges local computation as well as handler
  work. Erasure and a per-iteration runtime bound are proved. This intermediate interface is
  open; the final `Machine.Within` certificates close it with implemented handlers and only
  the fixed primitive sampling/store effects.
- [`Arithmetic.lean`](../Signatures/Runtime/Arithmetic.lean): a fixed instruction family for
  scalar/group arithmetic, scalar/group/key/message equality, and natural-number operations.
  Public-key equality permits key-dependent branching. No whole solver
  or adversary is an instruction. Named primitive prices are explicit contracts of this arithmetic
  model, not proved bit costs for arbitrary Lean typeclass instances.
- [`Lookup.lean`](../Signatures/Runtime/Lookup.lean): compiled first-match association-list lookup,
  with a presence flag distinguishing a cached zero from absence. Correctness and the bound
  `length * (equalityCost + 19) + 9` are proved. This replaces a random-access assumption for this
  component. The persistent-cache handler below uses this implementation.
- [`Sampling.lean`](../Signatures/Runtime/Sampling.lean): compiled table initialization with one
  scalar draw per cell, list allocation, and a charged final reversal. The total bound is
  `n * (scalarSampleCost + 17) + 10`. Its erased program is **exactly** the native vector sampler
  mapped to a list, so no independent probability argument or guessed whole-table price is used.
  The scalar sampler's bound is a primitive premise. Its exact output length is also proved.
- [`SamplingState.lean`](../Signatures/Runtime/SamplingState.lean),
  [`Table.lean`](../Signatures/Runtime/Table.lean), and
  [`AGMTable.lean`](../Signatures/Runtime/AGMTable.lean): embed that sampler in the closed machine
  while preserving ambient state and cost. Erasing the list representation gives exactly the
  native finite-function sampler, in its canonical enumeration order. The function view is
  proof-only, never an executable free lookup.
- [`Index.lean`](../Signatures/Runtime/Index.lean) and
  [`Weakening.lean`](../Signatures/Runtime/Weakening.lean): charged full-scan indexing, including
  missing entries and stored zeroes, and cost-preserving reuse of expressions in trailing frames.
- [`Weights.lean`](../Signatures/Runtime/Weights.lean): executable BLS, OOPS, and Proximity weights
  with exact native-value theorems. OOPS powers execute field operations and degree tests;
  Proximity coordinates execute list indexing. The encoded Proximity key is injective.
- [`Tuple.lean`](../Signatures/Runtime/Tuple.lean) and
  [`ProximityWeight.lean`](../Signatures/Runtime/ProximityWeight.lean): fixed-size first-order
  vectors equivalent to the paper's `Fin ell -> F` messages. Coordinate access executes tuple
  projections and natural operations, with a uniform bound for every typed message. The
  structural type enforces the dimension; no extra source message-length premise is needed.
  Loading a scalar vector costs exactly `2*ell+1` steps.
- [`AttachTable.lean`](../Signatures/Runtime/AttachTable.lean),
  [`WeightedSum.lean`](../Signatures/Runtime/WeightedSum.lean),
  [`LookupExpr.lean`](../Signatures/Runtime/LookupExpr.lean), and
  [`KeyEquality.lean`](../Signatures/Runtime/KeyEquality.lean): executable ordered table
  construction, scalar-weighted sums, and structured-key scans. Only ordinary arithmetic,
  list, and stack instructions are used. Key equality is compiled for all three families.
  [`TableRefinement.lean`](../Signatures/Runtime/TableRefinement.lean) proves exact correspondence
  to native table access and finite sums for canonical encoded keys. The canonical key list is
  fixed data; both complete AGM packages load it and charge its structural size.
- [`Runtime.lean` tests](../SignaturesTest/Runtime.lean): pure computations with equal values but
  different runtimes, absent/cached-zero/duplicate-key lookups, empty and nonempty sampling runs,
  native sampler correspondence, concrete bounds, and standard-axiom checks.
- [`Composition.lean`](../Signatures/Runtime/Composition.lean) and
  [`SourceBudget.lean`](../Signatures/Runtime/SourceBudget.lean): support-wise runtime substitution
  through adaptive branches, continuations, and loops. A source certificate prices every request
  uniformly over all nonnegative capability tariffs and includes local computation. Reply
  contracts require nonempty responses; impossible response types cannot vacuously certify code.
- [`GrowingState.lean`](../Signatures/Runtime/GrowingState.lean) and
  [`Refinement.lean`](../Signatures/Runtime/Refinement.lean): storage growth and quadratic total
  bounds for handlers whose cost grows linearly with storage. A proof-only call counter is erased
  with exact cost preservation. The implementation does not receive a free counter operation.
  Representation refinement and native oracle simulation commute with adaptive program execution.
- [`Cache.lean`](../Signatures/Runtime/Cache.lean) and
  [`CacheRefinement.lean`](../Signatures/Runtime/CacheRefinement.lean): compiled persistent cache,
  length growth, and `length*(equalityCost+19)+drawCost+36` handler cost. Hits do not draw again.
  Exact bridges to the existing BLS scalar cache and VCVio coin cache are proved. Function-valued
  cache abstractions are used only in proofs, never as uncharged executable lookups.
- [`CoronSimulation.lean`](../Signatures/Runtime/CoronSimulation.lean): implemented hash/sign
  handlers with two lazy caches, signed-message list, scalar/coin sampling, default initialization,
  bounded-coin conversion, group arithmetic, and explicitly priced fixed adapter frames.
  [`CoronRefinement.lean`](../Signatures/Runtime/CoronRefinement.lean) proves exact adaptive
  simulation correspondence, retaining both caches and the original signing set.
- [`CoronReduction.lean`](../Signatures/Runtime/CoronReduction.lean): executes the final forgery
  hash, charged extraction lookup, and group extraction. Its evaluator bound is derived from
  the source budget, not assumed for the finished solver. The initial input environment is
  supplied to this intermediate evaluator. The closed-machine certificate below additionally
  constructs the input and charges its complete setup.
- [`CoronErasure.lean`](../Signatures/Runtime/CoronErasure.lean): exact equality from the full
  evaluator, including the final hash and extraction, to
  `coronReductionLazyPK qS (cacheForgeryPK adv)`. This is a semantic theorem, not a premise
  assuming that the finished solver satisfies its target budget.
- [`Inlining.lean`](../Signatures/Runtime/Inlining.lean): compiles capabilities into ordinary
  first-order procedure calls. Both behavior and runtime are preserved exactly, with three
  extra call-frame steps relative to a source query node.
- [`Machine.lean`](../Signatures/Runtime/Machine.lean): a general closed implementation class.
  The only effects are primitive scalar/bounded-uniform sampling and typed store reads/writes.
  Initial storage is an expression over actual input registers, not an arbitrary initializer.
  `Within` requires exact behavior and a pathwise budget for code in this language; inhabited
  input types cannot certify zero-cost algorithms. There is no reduction-specific instruction.
- [`Data.lean`](../Signatures/Runtime/Data.lean): fixed first-order data loading and input-frame
  construction. Tuple/list structure is fully traversed, natural literals pay unary load cost,
  and atomic values are primitive words. `Machine.Package` fixes its data independently of
  the challenge and pays these costs before executing its code. No arbitrary initializer is
  accepted. This is not a bit-encoding theorem for abstract message atoms.
- [`CoronMachine.lean`](../Signatures/Runtime/CoronMachine.lean): compiled hash/sign/private-random
  procedures, with both caches and signing log in the explicit store. Exact instruction counts
  derive the adapter overhead. The inlined adaptive simulation has a proved total bound and
  exact result/state correspondence to the existing evaluator.
- [`CoronMachineReduction.lean`](../Signatures/Runtime/CoronMachineReduction.lean): compiled
  final verification hash, scalar-cache scan, extraction, and initial store construction.
  The complete target program has a derived bound and exact evaluator equivalence.
- [`CoronCertificate.lean`](../Signatures/Runtime/CoronCertificate.lean): source code and
  fixed-data certificate, exact trace semantics at the actual public key for every challenge,
  and an all-path source budget. The target package pays for all data and input preparation.
  `SourceCertificate.within` certifies the exact named solver in the general `Machine.Within`
  class. `BLS.Statement.bls_eufcma_of_cocdh_machine_hardness` uses that proved certificate,
  removing the caller-supplied `hbudget` premise for this concrete backend.
- [`RuntimeComposition.lean`](../SignaturesTest/RuntimeComposition.lean) and
  [`RuntimeCoron.lean`](../SignaturesTest/RuntimeCoron.lean): source sampler certificates,
  growing handlers, nonempty initial state, cached replies, repeated signing, a response-dependent
  hash/sign choice, zero-query source with positive finish cost, and standard-axiom guards.
- [`RuntimeMachine.lean`](../SignaturesTest/RuntimeMachine.lean): charged initialization,
  store access, first-order calls, public-key-dependent branches, and zero-budget rejection.
- [`RuntimeCertificate.lean`](../SignaturesTest/RuntimeCertificate.lean): a concrete complete
  Coron certificate with budget 309, exact named-solver correspondence on every challenge,
  charged fixed constants, rejection of wrong-key behavior, and public-corollary axiom guards.
- [`RuntimeAGM.lean`](../SignaturesTest/RuntimeAGM.lean): all three weight and key encodings,
  zero-degree/short-coordinate cases, empty tables, state-preserving sampling, exact native
  sampler equivalence, ordered construction, first-match cached zeroes, finite sums, concrete
  cost fixtures, and standard-axiom guards for the new load-bearing proofs.
- [`GroupWeightedSum.lean`](../Signatures/Runtime/GroupWeightedSum.lean) and
  [`AffineTable.lean`](../Signatures/Runtime/AffineTable.lean): executed group-valued sums
  and affine bases `a_i * X + b_i * g` for the bad branch, with exact native finite-table
  equalities. Every scalar multiplication, addition, list allocation, and reversal is charged.
- [`AGMReplies.lean`](../Signatures/Runtime/AGMReplies.lean): actual good/bad hash and signing
  expressions. Hashes execute compiled table lookup; signing executes scalar or group-valued
  weighted sums. Canonical-table correctness and concrete expression bounds are proved.
- [`AGMOracle.lean`](../Signatures/Runtime/AGMOracle.lean) and
  [`AGMSimulation.lean`](../Signatures/Runtime/AGMSimulation.lean): closed-machine oracle
  procedures, inlining into arbitrary adaptive source programs, immutable private configuration,
  and persistent reverse-order transcripts. Source-budget substitution derives both simulator
  bounds without assuming whole-reply or whole-simulator budgets.
- [`AGMOracleRefinement.lean`](../Signatures/Runtime/AGMOracleRefinement.lean): exact adaptive
  equivalence to the original `Model.LazyAGM.fixedImpl`, with decoded query representations
  and chronological transcripts, including nonempty initial logs. Decoding/reversal in the
  representation proof is not a free instruction in the eventual extractor.
- [`RuntimeAGMSimulation.lean`](../SignaturesTest/RuntimeAGMSimulation.lean): hash-answer-dependent
  signing/hash choices, exact execution costs, private randomness forwarding, unchanged tables,
  chronological token order, both source-derived simulator budgets, and standard-axiom guards.
- [`TokenCoefficients.lean`](../Signatures/Runtime/TokenCoefficients.lean),
  [`ExtractionWeights.lean`](../Signatures/Runtime/ExtractionWeights.lean),
  [`ExtractionCore.lean`](../Signatures/Runtime/ExtractionCore.lean), and
  [`Extraction.lean`](../Signatures/Runtime/Extraction.lean): both compiled final extractors,
  starting with the actual reversed simulator logs and structured source output. They execute
  chronological reversal, coefficient attachment with zero defaults, nested scalar sums, and
  total field division. Core native-formula theorems and complete expression bounds are proved.
  The good denominator's rearranged nested sum is proved equal to the original formula.
- [`RuntimeTuple.lean`](../SignaturesTest/RuntimeTuple.lean) and
  [`RuntimeExtraction.lean`](../SignaturesTest/RuntimeExtraction.lean): zero-dimensional vectors,
  every coordinate, uniform Proximity bounds, chronological repeated tokens, missing/surplus
  coefficients, both extraction outputs, zero-denominator behavior, concrete bounds, and
  standard-axiom guards.
- [`AGMSource.lean`](../Signatures/Runtime/AGMSource.lean): source implementation certificates
  at every public key, with fixed first-order data, adaptive source budgets, and coefficient
  length bounds on every allowed reply path. The source receives only its public key and data.
  `machineSimulation_supported` transports output-size evidence to actual simulator runs;
  the decoded source/output/transcript semantics equal the native fixed-run experiment.
- [`AGMExecution.lean`](../Signatures/Runtime/AGMExecution.lean),
  [`AGMExtractionRefinement.lean`](../Signatures/Runtime/AGMExtractionRefinement.lean), and
  [`AGMExecutionRefinement.lean`](../Signatures/Runtime/AGMExecutionRefinement.lean): both
  simulation-plus-extraction programs, exact native behavior through representation equivalences,
  and source-derived total phase bounds. Source call frames do not expose private tables.
- [`AGMInitialization.lean`](../Signatures/Runtime/AGMInitialization.lean): a compiled full-domain
  sampler followed by ordered keyed-table construction, preserving ambient state. Its erased
  output is exactly the native function sampler mapped to canonical keyed rows, not merely
  an equal distribution assumed for a whole-table opcode.
- [`AGMGoodMachine.lean`](../Signatures/Runtime/AGMGoodMachine.lean): complete good-branch
  setup, initialized store, compiled execution, fixed-data/canonical-enumeration loading,
  exact `Model.LazyAGM.goodReduction` erasure, and `SourceCertificate.goodWithin` in the general
  closed-machine resource class. Local equality/weight semantics and bounds are parameters;
  no whole-reduction budget is assumed.
- [`MaskedBases.lean`](../Signatures/Runtime/MaskedBases.lean): pairs independently sampled
  keyed tables using charged compiled lookup, then executes affine group construction. The
  output preserves canonical order and equals the native masked bases. Bounds also cover
  reordered, missing, duplicate, and zero-valued rows; canonical keys are injective.
- [`AGMBadMachine.lean`](../Signatures/Runtime/AGMBadMachine.lean): samples kappa, then the full
  a table, then the full b table; constructs masked bases and computes the source key `kappa*g2`.
  Both sampling passes, key construction, initialized store, adaptive execution, extraction,
  and fixed-data loading are charged. Exact `Model.LazyAGM.badReduction` erasure and
  `SourceCertificate.badWithin` are proved in the same general machine class as the good branch.
- [BLS](../Signatures/BLS/ArithmeticStatement.lean), [OOPS](../Signatures/OOPS/Statement.lean), and
  [Proximity](../Signatures/Proximity/Statement.lean): the public AGM machine-bounded statements,
  with compiled scheme-specific encodings, key comparisons,
  weights, and their bounds. Both solver-budget hypotheses are discharged. No original
  degree/freshness condition is changed, and the full domain size is retained. Proximity adds
  an actual fresh-collision probability instead of assuming noncollision on all source paths.
- [`RuntimeAGMSource.lean`](../SignaturesTest/RuntimeAGMSource.lean): a concrete one-hash source
  certificate and complete good/bad witnesses with budgets 1334/1932 at unit primitive prices.
  Tests cover all-key erasure, empty/nonempty setup, undersized coefficient-bound rejection,
  wrong-key behavior rejection, both execution phase bounds, all `2*N+1` bad scalar draws,
  table-order/default/duplicate-zero behavior, and load-bearing axiom guards.
  [`StatementAssumptions.lean`](../SignaturesTest/StatementAssumptions.lean) additionally checks
  exact standard-axiom footprints, source-certificate interfaces, both hardness assumptions,
  the explicit Proximity collision term, and absence of caller-supplied finished-solver budgets.

### AGM component bounds

Let `N` be the full key-domain size, `f` the field-operation price, `n` the natural-operation
price, `e` a compiled key-comparison bound, and `w` a compiled weight-evaluation bound.
The following are proved component bounds, **not total solver budgets**:

```text
scalar sampling:       N * (scalarSampleCost + 17) + 10
table construction:    N * (N * (2*n + 26) + n + 63) + 15
scalar table lookup:   N * (e + 22) + 9
scalar weighted sum:   N * (w + 2*f + 27) + f + 6
group weighted sum:    N * (w + scalarMulCost + groupCost + 27) + groupCost + 6
affine base mapping:   N * (2*scalarMulCost + groupCost + 35) + 11
```

Construction assumes the sampled scalar list has length `N`, as the sampler proves. The
general constructor theorem also handles unequal lengths with an explicit default. Loading
the fixed enumeration and procedure adapter frames is additional work. Construction is
quadratic because it uses charged linked-list scans, not a random-access array.

The compiled comparison bounds are `keyEqualityCost + 5` for BLS and
`keyEqualityCost + 3*n + 17` for both structured-key families. Weight bounds are:

```text
BLS:        keyEqualityCost + f + 8
OOPS:       d * (d + n + f + 13) + f + n + keyEqualityCost + 19
Proximity:  ell * (2*n + 16) + keyEqualityCost + 4*n + f + 30
```

These use the existing native weights; no new security-game assumption is introduced.
In particular, full-domain sampling is not replaced by the source hash-query budget.
The Proximity line uses the fixed-size structural vector implementation; the older list-based
helper remains available but is not needed for a uniform message bound.

### AGM adaptive simulator bounds

Write `s` for G1 scalar multiplication, `g` for group addition, and `dR` for the maximum
uniform-sampling cost over the source's permitted random arities. Using `N`, `e`, `w`, and
`f` above, the actual reply procedures have these bounds, including inlining and recording:

```text
H_good = N*(e+22) + f+s+76
S_good = N*(w+2*f+27) + f+s+68
H_bad  = N*(e+22) + g+66
S_bad  = N*(w+s+g+27) + g+s+66

T_sim_good <= T + qR*(dR+5) + qH*H_good + qS*S_good
T_sim_bad  <= T + qR*(dR+5) + qH*H_bad  + qS*S_bad
```

The source budget is uniform over every adaptive reply path. The fixed configuration is
preserved and the number of recorded replies is at most `qR+qH+qS`; private-random replies
do not enter either transcript. Each hash/sign procedure adds exactly 40 steps to its reply
expression; inlining adds three more. Reverse-order insertion avoids a per-query append scan.

These formulas **exclude setup, sampling the private tables, fixed-data loading, final
transcript processing, and both extractors**. They are not full AGM `Within` certificates.
The weight bound must hold uniformly over allowed machine messages. All three families now
have such bounds, using structural vectors for Proximity. Function-valued coordinates are
only a proof representation, never free host operations.

### AGM extraction bounds

Let `H` and `S` be the actual explicit hash/sign transcript lengths, and `G` and `X` the
lengths of the source's gamma/xi coefficient lists. Here `n` still prices natural operations,
`f` field operations, `v` division, `e` compiled key equality, and `w` weight evaluation.

```text
R(t,c) = t*(c*(2*n+26)+n+70) + f+29
C(H)   = H*(e+3*f+37) + f+6
D(S)   = S*(w+2*f+34) + w+2*f+35

E_good <= R(H,G) + R(S,X)
          + N*(C(H)+D(S)+4*f+54) + 3*f+v+88
E_bad  <= R(S,X) + 2*N*(D(S)+2*f+27) + 3*f+v+63
```

These bound the complete extraction expressions, including reversing the stored logs,
matching coefficients, and all nested sums. Missing coefficients contribute zero; surplus
coefficients do not create tokens. The bad extractor does not inspect the hash log or gamma.
No nonzero-denominator premise is added: division agrees with the native total field operation.
The general bad bound also permits different table lengths, replacing `2*N` with their sum.
Source certificates must still bound coefficient lengths on every adaptive path, and the
complete package must add setup, simulation, fixed-data loading, and procedure frames.

### Complete AGM certificates

The generic source certificate now supplies the all-path lengths above. With
`Q=qR+qH+qS`, `G`/`X` its gamma/xi bounds, and `D` the structural load of the fixed source data
and canonical key enumeration, the proved packages use these total bounds. Here `dF` is the
scalar-sampling price and `s2` is the G2 scalar-multiplication price:

```text
K(N) = N*(dF+17) + N*(N*(2*n+26)+n+63) + N+f+41
M(N) = N*(N*(e+22)+f+2*s+g+83) + 43
T_exec_good = T_sim_good + E_good(N,Q,Q,G,X) + 29
T_exec_bad  = T_sim_bad  + E_bad(N,Q,X) + 36
T_B_good <= K(N) + T_exec_good + D + 65
T_B_bad  <= 2*K(N) + M(N) + T_exec_bad + dF+f+s2 + D + 117
```

The 65 steps include initial store construction, setup and execution call frames, code
initialization/return, and attaching the four DLog input registers. `K(N)` also charges the
unary natural literal used for the sample count. Both transcript lengths are conservatively
bounded by `Q`; no undocumented distinct-query assumption is used. This is a complete
certificate for the exact named good solver, for every challenge input. `M(N)` includes pairing
the two scalar tables by charged key lookup, affine group construction, and their call frames.

The bad package preserves the exact kappa/a/b sampling order and runs the source at `kappa*g2`,
not the challenge's X2. `dF+f+s2+117` charges the extra scalar draw, initial zero, public-key
multiplication, and all remaining setup/package frames. Its behavior equals the exact named
bad solver on every input; the random-function view appears only in the erasure proof.

`N` is `|M|` for BLS, `|T|*(d+1)` for OOPS, and `(ell+1)*|S|` for Proximity. Use the compiled
scheme-specific `e` and `w` bounds above. The public `_of_dlog_machine_hardness` corollaries
instantiate both `SourceCertificate.goodBudget` and `SourceCertificate.badBudget` with these
constants. They do not replace `N` by `qH` or claim polynomial dependence on a security parameter.

### Coron evaluator formula

Let `Q = qR + qH + qS`, `e = messageEqualityCost + 19`, and `T` be the certified source local
time. Write `dF`, `dC`, `dR` for primitive scalar, coin, and bounded-private-random sampling costs;
`f`, `s`, `n`, `g` for field, G1 scalar multiplication, natural operation, and group costs.

```text
H = dF + dC + f + s + 2*n + 2*g + 118
S = dF + dC + f + s + 2*n + g + 112
T_eval <= T + qR*(dR+4) + qH*H + qS*S + 2*e*Q^2
          + H + f + s + g + 49 + e*(3*Q+1)
```

The final line includes the extra verification hash and extraction, not just source queries.
This is a conservative full-scan-list bound; it is not the paper's optimized dictionary bound.
The fixed frame charges (24 per reply, 12 at finish, 16 for setup/return) are rules of this
arithmetic/stack/list model, not measured Lean VM or compiled-machine costs. Sampling costs are
primitive contracts at the stated field/coin sizes and source random arity bound.

The source is an actual `Program` with a `SourceBudget`; this does not automatically classify
every extensional Lean adversary as efficiently implementable. The complete machine corollary
uses the larger bound below, including the implemented frames and fixed-data loading.

### Compiled adaptive simulation

For the closed-machine simulation, let `dR` be the maximum primitive uniform-sampling cost
over the source's permitted random arities, and let `dC` be its cost at `qS`. Using `H`, `S`,
`Q`, `e`, and `T` above:

```text
H_machine = H + n + 50
S_machine = S + n + 48
T_sim_machine <= T + qR*(dR+5) + qH*H_machine + qS*S_machine + 2*e*Q^2
```

These constants come from actual target instructions and procedure frames, not an assumed
whole-handler price. The exact reply overhead relative to the earlier evaluator is `n+47`
for hashing and `n+45` for signing; inlining adds another three steps. The target has no hash
or signing effect. This formula excludes initial store construction and final extraction;
it must not be presented as the complete solver bound. All bounds remain arithmetic-machine
bounds with explicit primitive sampling contracts, not bit-runtime bounds.

### Complete Coron certificate

Let `D` be the checked load cost of the source's fixed data. When the source signing budget
is `qS`, the certificate instantiates the preceding formulas as follows:

```text
T_B <= T_sim_machine + H + f + s + g + n + 145 + e*(3*Q+1) + D
```

The added terms include the extra forgery hash, extraction, store initialization, input-register
construction, and every procedure frame. `T` is measured on the actual padded source context;
there is no uncharged public-key-to-environment conversion. Exact source semantics must hold
on all challenge inputs, so padding cannot give the source hidden challenge-dependent behavior.
`coCDHWithin` ranges over arbitrary packages in the general closed machine, not just Coron code.
The original signing-query security premise and all original probability assumptions remain.

Both AGM packages and all three scheme-specific concrete-machine corollaries are also complete;
see [the total AGM bounds](#complete-agm-certificates). All four concrete endpoints infer the
adversary, primitive costs, and source resource indices from their source certificate. Their
hardness hypotheses and the original probability-game assumptions remain explicit. See
[the security status](COMPUTATIONAL-SECURITY.md) for the distinction from the earlier partial ledgers.

VCVio's pinned `OracleClosure.lean` currently provides semantic handler conformance, not a
quantitative machine-substitution theorem. Its own documentation leaves that theorem open.
Importing `IsOraclePPTBy` therefore cannot by itself complete the runtime argument here.

Verification: `lake build Signatures SignaturesTest` passes (2026-09-24), including the runtime
regressions, exact standard-axiom guards, and statement-application inference checks.
No new runtime-module warnings. Job totals depend on which targets need rebuilding.
