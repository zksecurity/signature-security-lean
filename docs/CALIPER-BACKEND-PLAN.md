# Caliper execution and abstract cryptographic routines

The execution layer uses Caliper word programs, registers, buffers and tapes.
Field/group routines operate on explicit word encodings and carry correctness,
time, buffer-memory and code-footprint contracts. Attacker code can inspect those
encodings. AGM explanations remain a separate restriction on group outputs.

The source is pinned to Caliper `b62f7c8be35df0aa728e5a6aac7bae85eef67449`, using
the existing Lean 4.34 compatibility port recorded in `vendor/caliper/UPSTREAM.md`.
Existing Mathlib, VCVio, PolyFun and AGM dependency revisions are retained.

Implemented and checked:

- [Program](../Signatures/Runtime/Caliper/Program.lean): ordinary Caliper code plus
  library-call syntax. Lowering expands each call into its selected Caliper body.
  There is no additional interpreter whose behavior or costs must be trusted.
- [Encoding](../Signatures/Runtime/Caliper/Encoding.lean) and
  [Crypto](../Signatures/Runtime/Caliper/Crypto.lean): explicit fixed-width scalar
  and group encodings, addresses, typed operations, and mathematical specifications.
  Decoding is a specification predicate, not an executable instruction.
- [Routine](../Signatures/Runtime/Caliper/Routine.lean): actual routine code,
  time/workspace bounds, scratch separation, slice-level frame conditions,
  preallocated output storage, unchanged tape cursor, and returned scratch capacity.
  A library instance must prove these contracts. No concrete curve library is
  assumed to exist or supplied by this change.
- [Hoare](../Signatures/Runtime/Caliper/Hoare.lean): call, sequence, branch and loop
  rules reusing Caliper's total-correctness/resource proofs.
- [Realizer](../Signatures/Runtime/Caliper/Realizer.lean): an actual PolyFun
  `QuantitativeStepClass` for bounded encodings. Identity/composition contain
  `skip`/`seq` programs, with proved exact time. Its `Realizer` requires literal
  Caliper code implementing the mathematical function on every represented input.
  `descriptionSizes` supplies the existing reduction framework's code-accounting
  interface from those actual Caliper descriptions.
- [Description](../Signatures/Runtime/Caliper/Description.lean) and
  [Resources](../Signatures/Runtime/Caliper/Resources.lean): word-sized stored-code
  operands, expanded library bodies, conservative dense register slots, three-word
  buffer descriptors, and initial plus peak buffer storage. These are explicit
  machine-level accounts, not a completed flat-memory allocator refinement.
- [Words](../Signatures/Runtime/Caliper/Words.lean): concrete bit-complement code
  with exact execution and cost proofs, instantiated through the quantitative API.
- [Memory](../Signatures/Runtime/Caliper/Memory.lean): verified Caliper memcpy,
  with unit-cost time at most `7*n + 4` and extra buffer storage at most `n` words.
  This supplies a charged copy primitive, not a complete interactive snapshot.
- [Layouts](../Signatures/Runtime/Caliper/Layouts.lean): bounded counters,
  products, tagged unions and lists, with decoding round trips and exact stored
  word counts. A list reserves its entire capacity, including padding. Combined
  layouts must fit the address width; component bounds alone do not suffice.
- [Slice](../Signatures/Runtime/Caliper/Slice.lean) and
  [Wiring](../Signatures/Runtime/Caliper/Wiring.lean): executable slice copying,
  pair projections and bounded list-length access. Projections build the output
  in scratch, copy it back and release scratch. Selecting `n` words takes exactly
  `8*n` unit-cost steps and stores `26*n + 14` code words. The unrolled code is
  charged explicitly. These are local realizers, not universal product/list
  closure instances for the old unbounded source types.
- [Replay](../Signatures/Runtime/Caliper/Replay.lean): actual random-word recording,
  replay and cursor reset. A fresh read costs 7 unit-cost steps, a cached read 6,
  and resetting the virtual cursor 1. The cache must be allocated separately.
  `read_refines` proves that each returned word equals the original tape at the
  virtual cursor, preserving the recorded-prefix invariant. The physical tape
  never rewinds. Private buffers/registers are framed; linking must reserve the
  controller's buffer and registers and route random reads through it.
- [Mailbox](../Signatures/Runtime/Caliper/Mailbox.lean): actual request/reply
  buffer transfer, restoring the local-call zero-offset convention. Transferring
  `n` words costs at most `7*n + 5` unit-cost steps and at most `n` extra buffer
  words; its code occupies 41 words. Other buffers/capacities and registers beyond
  the five scratch registers are preserved. An incoming reply must already reside
  in an accounted input mailbox. External I/O and full suspension/resumption are
  still separate obligations.
- [Assembly](../Signatures/Runtime/Caliper/Assembly.lean) and
  [Construct](../Signatures/Runtime/Caliper/Construct.lean): construction from
  literal words and indexed reads, with actual scratch allocation, copying and
  release. Building `n` output words takes at most `8*n` unit-cost steps and
  stores at most `26*n + 14` code words. Concrete realizers duplicate values and
  build either tagged-union alternative, including its tag and padding. Read
  bounds rule out index wraparound and reads from the replaced scratch buffer.
- [Retain](../Signatures/Runtime/Caliper/Retain.lean): saved-state composition
  `(a, s) ↦ (f(a), s)` for any certified local callee. The saved buffer is chosen
  beyond the callee's mutation footprint, subject to an explicit name-width
  bound. Saving, projection, rebuilding and releasing it are actual instructions.
  With input/output/saved widths `a`, `b`, `s`, the wrapper adds at most
  `8*a + 8*b + 12*s` unit-cost steps to the callee and at most
  `26*a + 26*b + 39*s + 39` code words. The saved payload stays resident during
  the call. Buffer 1 and the chosen saved buffer are wrapper scratch locations;
  a surrounding interactive linker must reserve them.
- [Branch](../Signatures/Runtime/Caliper/Branch.lean): actual stored-tag dispatch,
  payload normalization and selected-callee execution. At unit costs, selecting
  a payload of `n` words adds `8*n + 2` steps to that callee. This proof is for
  canonical represented inputs; it does not implement a decoder for arbitrary
  attacker-supplied malformed bytes.
- [Loop](../Signatures/Runtime/Caliper/Loop.lean): a bounded local-loop compiler
  with early return and an executed stop routine at exhaustion. Its mathematical
  behavior equals the shared source loop specialized to local deterministic
  computation. The compiler unrolls the bound, with proved linear time and code
  bounds; it does not claim the source's one-copy loop footprint. This is not yet
  a compiler for loops that suspend on external oracle calls.
- [BoundedSource](../Signatures/Runtime/Caliper/BoundedSource.lean): layouts for
  the original `Nat`, list, product and sum source types, restricted by explicit
  capacity predicates. A local implementation proves preservation and contains
  actual Caliper code on the represented subtype. Composition and bounded loops
  preserve the original source result. Reinterpreting bytes requires a proved
  equality of encodings and leaves code and resource profiles unchanged.
- [WordIO](../Signatures/Runtime/Caliper/WordIO.lean) and
  [WordPort](../Signatures/Runtime/Caliper/WordPort.lean): a synchronous external
  I/O boundary with three explicitly priced effects: send one register word,
  receive one word into a register, and invoke the oracle. All local work remains
  ordinary Caliper code. Request words are loaded before sending; replies are
  allocated and pushed word by word. An exchange of `r` request words and `s`
  reply words takes exactly `3*r + 3*s + 1` unit-cost steps and stores
  `13*r + 8*s + 12` code words. Net buffer growth is `s - oldCapacity`, and peak
  growth is its maximum with zero. Other buffers, register zero and the private
  tape cursor are preserved. A zero-width packet still invokes the oracle once.
  This is an explicit I/O extension, not a claim that upstream Caliper has a
  built-in oracle instruction. External oracle processing is outside local time.
- [WordRun](../Signatures/Runtime/Caliper/WordRun.lean) and
  [WordFuel](../Signatures/Runtime/Caliper/WordFuel.lean): executable interpretation
  of the I/O syntax using the actual Caliper evaluator for every local block.
  Soundness and completeness connect returned states, traces and profiles to
  operational execution. The packet adapter needs local evaluator depth two,
  uniformly over valid request/reply packets. Evaluator fuel is separate from
  the exact instruction/I/O time charged above.
- [OracleCall](../Signatures/Runtime/Caliper/OracleCall.lean): the ideal oracle
  decodes only words actually sent by the machine, then supplies encoded reply
  words as external input. The local continuation executes allocation and stores.
  `oracleCall_value` proves equality with the original dependent oracle query,
  as an oracle computation that can be composed with adaptive continuations.
  Decoding here specifies the external oracle interface, not a free decoder
  available to local programs. This is a query primitive refinement; complete
  signature controller compilation and replay linking still remain.
- [Synchronizes](../Signatures/Runtime/Caliper/Synchronizes.lean) and
  [Interactive](../Signatures/Runtime/Caliper/Interactive.lean): structural
  source/target correspondence through identical adaptive queries. Local blocks
  execute literal Caliper statements; queries execute the word adapter. Refinement
  retains actual execution, time, memory and trace evidence at every returned
  leaf. Ports can represent bounded subsets of unbounded source query domains.
- [InteractiveControl](../Signatures/Runtime/Caliper/InteractiveControl.lean) and
  [InteractiveRetain](../Signatures/Runtime/Caliper/InteractiveRetain.lean):
  sequences, stored-tag branches, loops that suspend on queries, and caller state
  saved in an actual buffer beyond the callee's mutation footprint. Prefix and
  restoration instructions execute and their profiles compose. Checked emission
  below validates the generated buffer name against the word width.
- [SourceCompilation](../Signatures/Runtime/Caliper/SourceCompilation.lean) and
  [SourceErasure](../Signatures/Runtime/Caliper/SourceErasure.lean): compilation
  certificates indexed by the existing `BackendProgram.Code`, with implementation
  and capacity obligations at primitive leaves. Correctness and erasure recover
  that original program's oracle computation. Covered constructors are local
  operations, queries, sequencing, branching, saved state, bounded loops and
  input-counted iteration: every constructor of the existing language is covered.
  A completed reduction's execution
  equation is not assumed as a primitive contract.
- [InteractiveDescription](../Signatures/Runtime/Caliper/InteractiveDescription.lean):
  generated code counts include the I/O envelope and every unrolled body copy.
  Dispatch adds `26*a + 26*b + 40` words to its two bodies. Retaining state adds
  at most `26*a + 26*b + 39*s + 41` words. A loop stores the stop code plus
  `fuel * (bodyWords + 26*resultWidth + 26*stateWidth + 43)` words. These are
  description bounds, separate from the dynamic bounds below.
- [InteractiveBounds](../Signatures/Runtime/Caliper/InteractiveBounds.lean),
  [InteractiveControlBounds](../Signatures/Runtime/Caliper/InteractiveControlBounds.lean)
  and [SourceBounds](../Signatures/Runtime/Caliper/SourceBounds.lean): uniform
  runtime bounds for every represented input, tape and oracle reply path of the
  compiled program. Only primitive leaves supply budgets, checked against their
  actual Caliper implementations. Query exchange costs, sequence addition,
  branch maxima, executed copies and every loop iteration are derived. At unit
  costs, dispatch adds `2 + 8*payloadWidth` steps along the selected path;
  retaining state adds at most `8*a + 8*b + 12*s`. Loops take at most
  `stopBudget + fuel*(bodyBudget + 2 + 8*max(resultWidth, stateWidth))` steps.
  Additional buffer capacity is bounded by that time when allocation costs at
  least one per word. These dynamic bounds feed the complete machine-memory
  account below; parameter-indexed polynomial-family theorems remain separate.
- [WordResources](../Signatures/Runtime/Caliper/WordResources.lean) and
  [WordFrames](../Signatures/Runtime/Caliper/WordFrames.lean): the I/O execution's
  net profile equals its change in allocated buffer capacity. The peak bounds
  every intermediate state, including inside embedded Caliper blocks. Visited
  states are indexed by the same actual execution, so unrelated external reply
  paths cannot be mixed. All visited states preserve well-formedness and finite
  register/buffer support. Static storage includes the complete program, dense
  register slots and three words per buffer descriptor, including gaps in names.
- [SourceMemory](../Signatures/Runtime/Caliper/SourceMemory.lean): every reachable
  compiled execution has a bound on all intermediate machine states equal to
  static storage plus initial allocated capacity plus the uniform runtime budget.
  No initial data or saved caller storage disappears from the account. This is
  the stated machine-level storage convention; flat-memory/CPU refinement is separate.
- [WordAcceptance](../Signatures/Runtime/Caliper/WordAcceptance.lean),
  [InteractiveAcceptance](../Signatures/Runtime/Caliper/InteractiveAcceptance.lean)
  and [SourceAcceptance](../Signatures/Runtime/Caliper/SourceAcceptance.lean):
  checked emission validates newly reserved caller-buffer names. Primitive proofs
  and layout bounds discharge the remaining stored-word conditions, including the
  I/O adapter. `emit` returns the exact refined program with a `DescriptionFits`
  proof, or rejects it. A valid callee using the last representable buffer ID can
  therefore be rejected when a surrounding caller needs an additional saved buffer.
  The structural check conservatively checks even an unused zero-bound loop body.
- [CapacityBounds](../Signatures/Runtime/Caliper/CapacityBounds.lean): static
  allocation capacities follow from accepted descriptions; dynamic allocations
  use word-valued registers. Every visited state preserves word-sized capacities
  and lengths, including inside local loops. Bounds on total storage remain
  separately charged; fitting each operand alone is not a memory budget.
- [Counter](../Signatures/Runtime/Caliper/Counter.lean),
  [Counted](../Signatures/Runtime/Caliper/Counted.lean) and
  [CountedBounds](../Signatures/Runtime/Caliper/CountedBounds.lean): actual stored
  counter loading, testing and decrementing, with saved-state composition across
  adaptive body queries. The original `(Nat, state)` input has an explicit layout
  storing payload then counter; producers must implement that encoding. The
  maximum count bounds generated code; the stored input count controls execution.
  Correctness recovers the original source `iterate`. For payload width `s`,
  body time `B` and maximum count `n`, unit time is at most
  `8*s + n*(B + 16*s + 19)` and stored code at most
  `26*s + 15 + n*(bodyWords + 78*s + 126)`. Every saved counter and copy is charged.
- [CellArithmetic](../Signatures/Runtime/Caliper/CellArithmetic.lean): indexed
  load/arithmetic/store with exact execution time, preserved capacities, and a
  proof that all other encoded words are unchanged. List headers use these
  instructions for increment/decrement.
- [ListConstruct](../Signatures/Runtime/Caliper/ListConstruct.lean): empty lists
  initialize all reserved words; prepend copies the entry and old list and
  increments the stored count. For entry width `s` and old capacity `c`, prepend
  returns capacity `c+1`, takes at most `8*(1+(c+1)*s)+5` unit steps and stores at
  most `26*(1+(c+1)*s)+38` code words. These bounds include padding and scratch.
- [ListDestruct](../Signatures/Runtime/Caliper/ListDestruct.lean) and
  [ListCases](../Signatures/Runtime/Caliper/ListCases.lean): list case analysis
  tests the stored count, constructs the empty tag or copies the head/tail, and
  decrements the tail count. Input capacity `c+1` yields tail capacity `c`.
  For output width `N=2+(c+1)*s`, time is at most `8*N+7` and code at most `52*N+59`.
  These bounds also cover zero-word element encodings and empty lists.
- [ListCapacity](../Signatures/Runtime/Caliper/ListCapacity.lean): increasing a
  list's capacity executes copying and adds canonical zero padding. For target
  capacity `c`, time is at most `8*(1+c*s)` and code at most `26*(1+c*s)+14`.
  Capacity changes are not free relabelings of stored bytes.
- [SourceLists](../Signatures/Runtime/Caliper/SourceLists.lean): the new routines
  implement operations on the original mathematical list types, with proved
  preservation of their bounded domains. The constructor can grow a capacity;
  case analysis shrinks the tail's capacity. Looping source programs still need
  explicit layout reconciliation and invariant proofs.
- [ListFoldSetup](../Signatures/Runtime/Caliper/ListFoldSetup.lean) and
  [Reorder](../Signatures/Runtime/Caliper/Reorder.lean): executed copying prepares
  body arguments and a retained tail/environment, decrements the copied tail
  count, and rebuilds the next list/accumulator/environment frame after the call.
- [ListFold](../Signatures/Runtime/Caliper/ListFold.lean) and
  [ListFoldBounds](../Signatures/Runtime/Caliper/ListFoldBounds.lean): complete
  Caliper execution of a fold with a compiled body. The stored length controls
  calls; a maximum capacity bounds the generated code. For entry, accumulator
  and environment widths `s,b,e`, capacity `n`, and `W=1+(n+1)*s+b+2*e`, time is
  at most `8*b+n*(bodyTime+44*W+7)` and code at most
  `26*b+14+n*(bodyWords+169*W+115)`. The possible quadratic capacity cost comes
  from charged tail copying. Empty lists skip the body, and capacity zero runs
  the final accumulator projection.
- [ListLayout](../Signatures/Runtime/Caliper/ListLayout.lean) represents lists
  whose elements have bounded domains, including nested structured values.
  [SourceFold](../Signatures/Runtime/Caliper/SourceFold.lean) compiles the original
  mathematical `List.foldl` from its body implementation. It derives accumulator
  validity and source-result equality; no implementation or bound for the
  finished fold is a premise. Domain witnesses remain mathematical specifications.
- [Regression checks](../SignaturesTest/CaliperBackend.lean): actual execution,
  cost composition, invalid addresses, overflowing static operands, code size,
  charged copying, and theorem axiom guards.
- [Integration checks](../SignaturesTest/CaliperIntegration.lean): bounded-layout
  decoding/rejection, multiword projection with actual scratch peaks, bounded
  length access, fresh/cached replay including full-capacity behavior, mailbox
  framing, and axiom guards for the new proofs.
- [Control checks](../SignaturesTest/CaliperControl.lean): actual construction and
  padding costs, both branches with unequal payload widths, nested saved-state
  calls, preserved unrelated memory, actual temporary-memory peaks, bounded-loop
  early return/exhaustion, generated code size, rejected read/name bounds, and
  axiom guards.
- [Word I/O checks](../SignaturesTest/CaliperWordIO.lean): executed exchanges,
  exact time/code/net/peak charges, preserved caller buffers and private tape,
  unread input, zero-width invocation, missing/truncated packet rejection, full
  buffer rejection, source-`Nat` loop refinement, a linked typed oracle, and
  theorem axiom guards.
- [Interactive checks](../SignaturesTest/CaliperInteractive.lean): a compiled
  adaptive source loop over `Nat` query positions, where the first reply changes
  the second request; a caller retaining a payload across an exchange; actual
  time, memory, trace and code counts; original-source observation equality,
  uniform runtime/additional-buffer theorems, and proof axiom guards. The retained
  caller's complete uniform memory account is 275 words: 215 code, 3 registers,
  9 descriptor words, 2 initial data words and up to 46 additional capacity words.
  The bound covers every visited state and asserts finite support and well-formedness.
  Counted iteration checks zero, partial and maximum counts, adaptive oracle
  results, uniform resources, code size, and rejection of an oversized count.
  Address tests reject an exhausted caller-buffer namespace and oversized static
  allocation/register operands, while accepting boundary-valid code.
- [List checks](../SignaturesTest/CaliperLists.lean): actual empty, partial and
  full list execution; multiword and zero-word entries; increment/decrement;
  charged capacity growth; scratch release and exact time/net/peak profiles;
  rejection of oversized decoded counts; uniform symbolic resource bounds,
  original-source capacity preservation, and theorem axiom guards.
- [Fold checks](../SignaturesTest/CaliperFold.lean): empty, partial and maximum
  traversal; dependence on the entry, accumulator and environment; capacity-zero
  termination; retained-state cleanup, unrelated memory preservation, exact
  runtime/net/peak profiles, symbolic time/code bounds, bounded-entry decoder
  rejection and theorem axiom guards.

- [Scalar operations](../Signatures/Runtime/Caliper/ScalarBounds.lean):
  [WordBinary](../Signatures/Runtime/Caliper/WordBinary.lean) loads two actual
  words, executes the selected instruction, stores the result and truncates the
  filled length. Its reserved capacity remains charged. [Natural](../Signatures/Runtime/Caliper/Natural.lean)
  retains source `Nat` semantics on bounded inputs: addition proves no overflow,
  [subtraction](../Signatures/Runtime/Caliper/Saturating.lean) compares and branches
  to produce zero on underflow, and equality/order compare the stored words.
  [Boolean](../Signatures/Runtime/Caliper/Boolean.lean) uses only the canonical
  words 0 and 1; its decoder rejects other values. Selection executes a zero
  test to convert the Boolean to the tagged-union convention while preserving
  its payload. [Finite](../Signatures/Runtime/Caliper/Finite.lean) implements
  constants, `Fin.val` and `Nat` modulo conversion. A modulus equal to the entire
  word domain uses the already-correct bounded input bytes, avoiding a wrapped
  zero divisor. [SourceData](../Signatures/Runtime/Caliper/SourceData.lean) supplies
  unit and Boolean operations with the original source types and validity predicates.
  General-cost execution proofs and uniform unit-cost resource theorems are checked.

  | Operation | Unit-cost steps | Stored code words |
  | --- | ---: | ---: |
  | Bounded addition, equality, unsigned order | 6 | 27 |
  | Saturating natural subtraction | 8 | 38 |
  | Boolean selection | 5 | 23 |
  | One-word literal construction | 7 | 35 |
  | Finite conversion, modulus smaller than word domain | 21 | 89 |
  | `Fin.val`, or conversion with full-domain modulus | 0 | 1 |

  The zero-cost cases execute `skip`: their input and output have proved identical
  stored words. These costs use Caliper's unit model; they do not assert constant
  bit complexity for division on arbitrarily wide words.
- [Pairing](../Signatures/Runtime/Caliper/Pairing.lean) composes two implementations
  sharing one input. It duplicates that input, saves it across the first call,
  executes the second call and assembles the pair through actual permutations.
  With input/first-output/second-output widths `a`, `b`, `d`, overhead is at most
  `52*a + 36*b + 16*d` unit-cost steps and `169*a + 117*b + 52*d + 124` code words,
  in addition to the callees. Combined capacities and saved-buffer names must
  fit the word width. [SourceStructure](../Signatures/Runtime/Caliper/SourceStructure.lean)
  supplies source product formation, projections and sum elimination with domain
  preservation. These are compositional building blocks for expression compilation.
- [Scalar and composition checks](../SignaturesTest/CaliperScalars.lean): boundary
  addition, subtraction underflow/equality, both comparisons, invalid Boolean
  and finite encodings, non-power-of-two/singleton/full-domain modulo, retained
  capacity after truncation, actual scalar/copy/branch composition, uniform
  time/code bounds and axiom guards.

- [SourceListData](../Signatures/Runtime/Caliper/SourceListData.lean) implements
  empty lists, cons and charged capacity growth when entries have their own
  restricted source layouts. The correspondence to the underlying bounded list
  is proved by erasing subtype witnesses; the target executes the existing
  construction/copying routines with unchanged resource profiles.
- [ExpressionCertificate](../Signatures/Runtime/Caliper/ExpressionCertificate.lean)
  and [ExpressionCompilation](../Signatures/Runtime/Caliper/ExpressionCompilation.lean)
  compile the original `Expr`, covering every constructor: variables, unit,
  Boolean/natural literals, pairs, projections, empty/cons lists, branches,
  local bindings, fixed instructions and folds. A certificate selects bounded
  layouts and proves their capacity conditions. Only instruction leaves accept
  primitive implementations; there is no finished-expression implementation
  premise. Successful compilation returns actual Caliper code with source-result
  correctness, domain preservation and exact execution profiles.
  [ExpressionVariables](../Signatures/Runtime/Caliper/ExpressionVariables.lean)
  walks represented environments through charged projections.
  [CheckedComposition](../Signatures/Runtime/Caliper/CheckedComposition.lean)
  tests generated saved-buffer names; an exhausted namespace returns `none`.
  A byte-preserving domain view executes `skip`; list capacity growth instead
  executes the proved copying routine. The compiler does not supply an encoding
  for all unbounded source values.
  The current fold constructor requires each body call to preserve a fixed
  accumulator domain. Growing accumulators need iteration-dependent bounds and
  a corresponding fold refinement; this is still integration work. Uniform
  resource bounds for complete expressions also remain to be assembled from the
  existing primitive, copy, branch and fold bounds.
- [Expression checks](../SignaturesTest/CaliperExpressions.lean): original source
  expressions compile and execute with variable access, primitive arithmetic,
  both branches, pair projections, local bindings, domain views, lists, capacity
  growth and empty/partial/full folds. Nested computation has an actual peak of
  eight temporary words. The subtraction branch retains its two-word capacity;
  the literal branch releases one word. A valid primitive using the last buffer
  name compiles alone and is rejected when a parent pair needs another name.
  All new proofs and implementation fixtures have axiom guards.

Remaining integration sequence:

1. Derive uniform bounds for the checked expression compiler and support growing
   fold accumulators with iteration-dependent domains. Compile derived
   lookup/update expressions using these refinements. Implement encoded key/message
   equality and refine the source's unbounded `Nat` and lists along reachable
   executions. List construction, case analysis, capacity growth and folds are
   implemented, as are tag dispatch, projection/length and saved-state composition.
   Folds preserve domains for entries and accumulators. Scalar operations now
   include bounded naturals, Booleans and finite counters; structural composition
   includes paired computations and source projections/branches. The checked
   compiler now covers all original expression constructors, subject to the
   admitted domains and the current fixed-domain fold condition.
   The bounded-source layout and loop refinement are implemented; the particular
   signature programs still need their reachable-state invariants and primitive
   refinements. A fixed-width representation cannot honestly supply all the old
   closure instances unchanged.
2. Instantiate compilation certificates for the signature programs through these layouts.
   The local category above does not yet instantiate `BackendAssembly.Backend`:
   that interface requires unrestricted product/sum closure, unbounded counters,
   external queries and exact cost equations. The new bounded local constructors
   do not imply those contracts unchanged. The interactive compiler now proves
   source refinement for every control constructor, including counted iteration.
   Uniform runtime/additional-buffer bounds now follow from actual primitive
   budgets. Checked emission proves generated-word acceptance and intermediate
   descriptor bounds. Complete machine-memory bounds include
   static storage and every intermediate buffer state. These finite-program
   bounds still need parameter-indexed polynomial bounds for each scheme.
3. Link the proved word oracle adapter and replay primitives into complete signature
   callers and rewinding. Ordinary saved-state query composition is proved.
   Prove private finite-domain sampling agrees with the chosen randomness
   interface; oracle packet transport alone does not supply this distribution proof.
   Prove separation of caller/controller storage and preservation of
   their invariants across external queries. Either copy all saved registers,
   buffer contents and capacities, or prove restart-from-initial-state replay with
   charged reinitialization. Caliper has no capacity-read instruction, so arbitrary
   dynamic capacities require explicit saved allocator metadata; copying filled
   contents alone does not restore them. Equality of runs from the same mathematical
   state is not a charged snapshot/restore implementation.
4. Supply the curve-specific routine library, or retain its named implementation
   contracts as explicit assumptions. Pairing/verification routines, if executed
   by the target program, also need implementations; they are not free consequences
   of the field/G₁/G₂ interface.
5. Instantiate signature security models and their parameter-indexed resource
   bounds using admissible instruction costs, polynomial word widths and polynomial
   routine bounds. Prove coverage for the intended Caliper adversary class. A claim about
   every conventional efficient attacker needs a further machine-adequacy result.

The existing backend's exact execution equations and unbounded mathematical data
types require a proved refinement. A fixed-word implementation must justify its
representable ranges along executions; attaching a cost table alone is insufficient.
Pure Caliper instruction counts require the cryptographic routine contracts to be
discharged. Machine-to-CPU adequacy remains a separate refinement.

Use one Lean compiler process at a time. Check operational examples, invalid
encoding/bounds cases, resource composition and theorem axiom footprints.
