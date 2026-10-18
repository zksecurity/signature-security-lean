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
  Folds support fixed domains or iteration-dependent accumulator layouts.
  Uniform time and stored-code budgets now cover complete expressions, including
  construction of their fold argument frames; the certificate's primitive and
  final-conversion budgets are the only supplied local efficiency premises.
- [Expression checks](../SignaturesTest/CaliperExpressions.lean): original source
  expressions compile and execute with variable access, primitive arithmetic,
  both branches, pair projections, local bindings, domain views, lists, capacity
  growth and empty/partial/full folds. Nested computation has an actual peak of
  eight temporary words. The subtraction branch retains its two-word capacity;
  the literal branch releases one word. A valid primitive using the last buffer
  name compiles alone and is rejected when a parent pair needs another name.
  All new proofs and implementation fixtures have axiom guards.
- [StagedFold](../Signatures/Runtime/Caliper/StagedFold.lean) compiles a finite
  sequence of accumulator layouts for the same original source `List.foldl`.
  Each body implements the original source function from the current layout to
  the next. Empty input executes a value-preserving conversion to the final
  layout; nonempty input retains the tail/environment, executes the body, and
  rebuilds the frame using the next accumulator width. The source-expression
  certificate's `foldStages` constructor compiles the same body expression at
  each stage; it does not take an implementation of a completed fold.
  [FoldStepBounds](../Signatures/Runtime/Caliper/FoldStepBounds.lean) proves
  single-stage bounds, using
  `W = 1 + (remainingCapacity + 1) * entryWords + stateWords + nextWords + 2 * envWords`:
  time is at most `bodyTime + followingTime + stopTime + 44 * W + 7`, and stored
  code at most `bodyCode + followingCode + stopCode + 169 * W + 116` words.
  These include actual copies, stored branches and final conversions.
  [StagedFoldBounds](../Signatures/Runtime/Caliper/StagedFoldBounds.lean) composes
  the bounds for the entire accepted stage family. For capacity `n`, with entry,
  environment and accumulator widths at most `L`, put `U = 1 + (n + 5) * L`.
  Its time bound is `8 * L + stopTime + n * (bodyTime + stopTime + 44 * U + 7)`;
  its stored-code bound is
  `26 * L + 15 + stopWords + n * (bodyWords + stopWords + 169 * U + 116)`.
  Only the individual bodies and final conversions need supplied budgets;
  the completed fold's budget is proved by induction on successful compilation.
  [ImplementationBounds](../Signatures/Runtime/Caliper/ImplementationBounds.lean)
  provides uniform time/code bounds, composition, and the resulting actual
  execution-time and additional-buffer bounds. These do not replace the separate
  initial-storage/register/descriptor account. The expression name bounds below
  now supply that metadata account from primitive name limits and generated code
  size; code-word count alone cannot bound arbitrary primitive operand magnitudes.
  [StructuralBudgets](../Signatures/Runtime/Caliper/StructuralBudgets.lean) derives
  source-level bounds for projections, accepted shared-input pairing and cons,
  supporting structural proofs of the body budgets themselves.
  [Growing-list checks](../SignaturesTest/CaliperStagedFold.lean) compile an
  original source reversal fold whose accumulator grows from one to four words.
  Empty, both partial, and full inputs return correctly padded reversed lists.
  The full example takes 3447 unit-cost steps with 33 additional words at peak;
  unrelated storage survives and generated temporary buffers are released.
  Its compiled fold, after construction of the initial argument frame, now has
  all-input bounds of 6412 steps and 24333 stored code words. These follow from
  proved body budgets of 625 steps/2221 words and final-conversion budgets of
  32 steps/118 words; no finished-fold efficiency assumption is supplied.
- [ExpressionBudget](../Signatures/Runtime/Caliper/ExpressionBudget.lean) derives
  a uniform time/stored-code budget recursively from every original-expression
  compilation constructor. Local budget certificates occur only at primitive
  instruction leaves and the executed final conversions of staged folds.
  Variables traverse their represented environments; literals, lists, projections,
  pairing, branches, bindings, views, fixed folds and staged folds all have
  derived budgets. The staged case takes maxima over the explicit finite set of
  traversal stages, not over a message domain. [DataBudgets](../Signatures/Runtime/Caliper/DataBudgets.lean),
  [BranchBudgets](../Signatures/Runtime/Caliper/BranchBudgets.lean) and
  [FixedFoldBudgets](../Signatures/Runtime/Caliper/FixedFoldBudgets.lean) supply
  the corresponding source-level composition lemmas.
- [ExpressionBounds](../Signatures/Runtime/Caliper/ExpressionBounds.lean) proves
  that every successful compilation meets its computed budget on all represented
  inputs. `compileBudget` attaches this proof; `compileBudget_forget` proves that
  forgetting it recovers the original compiler result, including rejection.
  `exec_bounded` supplies actual execution, the original source result, and the
  uniform time/additional-buffer bounds. The complete growing-list expression
  now has bounds of 7192 steps and 27146 stored words, including argument-frame
  construction. Expression regressions check every constructor, primitive
  budgets, fixed and growing folds, unchanged namespace rejection, and exact
  budget calculations (subtraction 188 steps/791 words; conditional 576/2456).
  These time/code theorems combine with the following metadata bounds.
- [NameBounds](../Signatures/Runtime/Caliper/NameBounds.lean),
  [StructuralNames](../Signatures/Runtime/Caliper/StructuralNames.lean),
  [FoldNames](../Signatures/Runtime/Caliper/FoldNames.lean) and
  [ExpressionNames](../Signatures/Runtime/Caliper/ExpressionNames.lean) prove that
  every accepted original expression has at most `N + C` dense register slots
  and buffer descriptors, where `N` bounds the names in supplied primitive/final
  conversion code and `C` is the derived stored-code budget. No bound on the
  finished expression is assumed. Saved-state calls choose a fresh buffer above
  the callee's names; its extra descriptor fits within the wrapper's code count.
  Pairing, branches, fixed folds and staged folds preserve this account.
  The regression with a two-word `memFree 255` primitive demonstrates why `N`
  cannot be inferred just from the primitive's description length.
- [ExpressionMemory](../Signatures/Runtime/Caliper/ExpressionMemory.lean) combines
  these results with actual execution. With initial register/buffer support bounds
  `r`/`b`, initial buffer capacity `I`, and derived time bound `T`, total memory is
  at most `C + max(r, N+C) + 3*max(b, N+C) + I + T`, at every intermediate and
  final state. All initial caller-owned capacity is included. The static part is
  at most `5*C + 4*N + r + 3*b`; thus metadata introduces no exponential term.
  The growing-fold regression derives 27149 name slots and 135742 static words
  from its supplied conversion-name limit of three and code budget of 27146.
  These deliberately conservative bounds do not assert that arbitrary primitive
  families are polynomial: scheme families must bound `N`, primitive time/code,
  layout widths, traversal capacities and initial storage in the security parameter.
- [WordEquality](../Signatures/Runtime/Caliper/WordEquality.lean) and
  [EncodedEquality](../Signatures/Runtime/Caliper/EncodedEquality.lean) implement
  equality by scanning two stored encodings. Each word pair executes two loads,
  equality, and accumulation with bitwise AND. Source equality follows from the
  encoding's proved injectivity; decoding is never called by the program.
  An `n`-word comparison takes exactly `6*n + 3` unit-cost steps, stores
  `30*n + 13` code words, and uses five register slots. It writes one Boolean
  into buffer zero, with at most one additional buffer word and no input copies.
  Zero-word encodings are handled and still pay for their Boolean output.
  Bounded-layout implementations preserve the original source types and prove
  the same budgets on every admitted value.
- [LookupLayout](../Signatures/Runtime/Caliper/LookupLayout.lean) and
  [LookupCompilation](../Signatures/Runtime/Caliper/LookupCompilation.lean)
  construct the certificate for the original `lookup eq` expression, including
  all projections, found/value state, branches, frame construction and fold.
  Capacity counts stored entries, never keys in the entire domain. The key and
  value layouts remain arbitrary bounded source layouts. Encoded equality can
  discharge the sole comparison leaf, and its actual budget/name proofs supply
  all the compiler's primitive premises.
- [LookupBounds](../Signatures/Runtime/Caliper/LookupBounds.lean) proves exact
  formulas for the computed lookup budgets and transfers them to every accepted
  compiler result. Let `k`/`v` be key/value word counts, `n` entry capacity,
  `L = 1 + n*(k+v)`, and `t`/`c` comparison time/code budgets. Then:
  `T = 188*k + 288*v + 256*L + 103 + n*(t + 768*k + 1080*v + 428*L + 500)` and
  `C = 611*k + 936*v + 832*L + 808 + n*(c + 2678*k + 3770*v + 1521*L + 2589)`.
  These are quadratic in entry capacity because every traversal step copies its
  retained environment. There is no assumed efficiency of the completed lookup.
  The existing expression memory theorem combines these budgets with primitive
  names and all initial storage. The compiler checks generated scratch names;
  successful emission for encoded lookup is now proved below. The remaining
  scheme code still requires its corresponding acceptance proofs.
- [LookupExpression](../Signatures/Runtime/Caliper/LookupExpression.lean)
  compiles the original `lookupExpr` with a structured-key equality expression
  by proved normalization to encoded equality. Its only source premise is that
  the comparator tests equality, as already proved for the scheme comparators.
  No implementation or efficiency assumption is supplied for the completed
  lookup or source comparison expression. The generated program scans the
  complete stored key encodings. Its result agrees with the original source
  expression on every admitted input; the optimization does not claim to
  preserve the source interpreter's step count.
  The existing constructed certificate supplies the same time/code budgets,
  name extent `5+C`, and static memory bound `5*C+20+r+3*b`. Complete execution
  memory adds all initial buffer capacity and `T`, including intermediate states.
  Normalization preserves compiler acceptance/rejection. Product-key regressions
  distinguish either component, preserve cached zero and unrelated caller storage,
  and check universal budgets `14813` steps and `53660` code words for capacity
  two, two-word keys and one-word values. Scheme-wide compilation and successful
  family emission remain separate obligations.
- [BufferBounds](../Signatures/Runtime/Caliper/BufferBounds.lean) derives scratch
  bounds for actual copied slices, assembly, retained calls, pairing, dispatch
  and fixed-layout folds, independently of copied widths and traversal capacities.
  [CompositionAcceptance](../Signatures/Runtime/Caliper/CompositionAcceptance.lean),
  [ExpressionEmission](../Signatures/Runtime/Caliper/ExpressionEmission.lean) and
  [FoldEmission](../Signatures/Runtime/Caliper/FoldEmission.lean) use these bounds
  to construct successful results of the existing checked compiler. Rules cover
  variables, Booleans, projections, primitive application, pairing, branching
  and complete fixed-layout folds, including their retained argument frames.
  The proof pays for all existing copying through the unchanged resource budgets.
- [LookupAcceptance](../Signatures/Runtime/Caliper/LookupAcceptance.lean) proves
  that the original lookup certificate compiles for every `LookupLayout` when
  the comparator uses at most five buffer slots. Encoded equality supplies that
  bound. The whole lookup needs at most seven buffer slots, independent of key
  width, entry capacity and key-domain size. The existing layout conditions
  suffice; no generated-code-length bound or separate acceptance premise is added.
  `EncodedLookup.implementation` is therefore total on every admitted layout,
  including capacity zero, and inherits the original source-result proof and
  time/code/memory bounds. Both lookup regression files now obtain acceptance
  from the general theorem; actual code still runs for all their operational tests.
- [RestrictedLayout](../Signatures/Runtime/Caliper/RestrictedLayout.lean) records
  additional proved domain invariants without changing bytes or code. Its decoder
  predicate is mathematical; it supplies no free executable test.
  [GuardedBranch](../Signatures/Runtime/Caliper/GuardedBranch.lean) executes the
  Boolean test and tag selection, then gives each branch the invariant of its
  observed result. Its copying, dispatch, time/code and name bounds are proved.
- [ListNarrow](../Signatures/Runtime/Caliper/ListNarrow.lean) and
  [ListFixedCons](../Signatures/Runtime/Caliper/ListFixedCons.lean) use paid prefix
  copying to remove only proved-unused padding before prepending within the old
  capacity. For stored table width `L`, fixed-capacity prepend costs at most
  `16*L+5` steps and `52*L+53` code words. A miss must have a free slot.
- [CacheCompilation](../Signatures/Runtime/Caliper/CacheCompilation.lean) constructs
  a total implementation of the original `cacheProgram` expression. The
  [layout](../Signatures/Runtime/Caliper/CacheLayout.lean) admits full-table hits
  and requires room only on misses; `capacityPred+1` is its fixed entry capacity.
  The same stored comparison result drives the guarded branch. Hits preserve
  the old table, including zero values and duplicate-key order; misses prepend
  without changing capacity. Only the source comparator's equality theorem is
  supplied; no implementation or efficiency premise for the finished cache is used.
  [CacheBounds](../Signatures/Runtime/Caliper/CacheBounds.lean) derives
  `Tcache = Tlookup + 160*I + 128*v + 40*L + 176` and
  `Ccache = Clookup + 546*I + 442*v + 130*L + 1030`, where `I=k+v+L`.
  The code needs at most eight buffer slots. Complete memory includes stored
  code, dense metadata, all initial capacity and every intermediate state:
  `5*Ccache+20+r+3*b+initialCapacity+Tcache`.
  Operational regressions cover full-table hits, cached zero, duplicate keys,
  insertion into empty/partly filled tables, unchanged caller storage and
  zero-word entries. Full-table misses and out-of-range component values are
  excluded by the input invariant. Scheme-level reachability must still prove
  that invariant.
- [CacheReadCompilation](../Signatures/Runtime/Caliper/CacheReadCompilation.lean)
  constructs the original effectful `cacheGetExpr`. The source comparator's
  equality theorem and a primitive draw's actual code/refinement are supplied;
  every other cache operation is generated. Hits return the cached value without
  invoking the draw. Misses save their frame beyond the lowered draw's buffer
  footprint, call it, restore the frame and insert the returned value. All these
  copies execute. The output observation equals the original source computation,
  including its oracle-call tree. The primitive draw's sampling distribution is
  not established by this generic composition theorem.
  [CacheReadBounds](../Signatures/Runtime/Caliper/CacheReadBounds.lean) proves
  `Tread = Tlookup+t+404*I+80*k+692*v+112*L+420` and
  `Cread = Clookup+c+1339*I+260*k+2275*v+364*L+2526`, with `t,c` the primitive's
  time and lowered-code budgets. The additional overhead is linear in widths.
  [CacheReadMemory](../Signatures/Runtime/Caliper/CacheReadMemory.lean) includes
  static code, dense metadata, all initial caller capacity and every visited
  state: `5*Cread+4*max(5,s)+r+3*b+initialCapacity+Tread`, where `s` bounds the
  primitive's register/buffer names. Stored-word acceptance is derived from the
  primitive's accepted description and `s<2^w`, including the fresh saved buffer.
  A one-query primitive regression checks no query/input consumption on full
  hits, one query on misses, fresh zero, fixed capacity, and preservation of an
  unrelated caller buffer/register and tape position. With one-word keys/values,
  capacity two and a four-step/20-word draw, the universal budgets are 15437 steps
  and 56159 code words. The source equality and axiom footprint are also checked.
- [InteractiveNames](../Signatures/Runtime/Caliper/InteractiveNames.lean) derives
  dense name bounds for lowered compute/sequence/tag-dispatch/saved-call wrappers.
  It supplies the cache memory proof; the remaining scheme controllers still
  need their own assembly and family bounds.
- [CacheReadOracle](../Signatures/Runtime/Caliper/CacheReadOracle.lean) connects
  the same executed cache code to the shared `QueryImpl.ListCache.handler`,
  preserving the value and updated table jointly.
  [BLSCache](../Signatures/Runtime/Caliper/BLSCache.lean) specializes this to the
  existing BLS AGM `privateListOracle`, with scalar or scalar-pair values. It
  requires the primitive draw's exact uniform-sampling law; it does not replace
  that law with word-packet transport. The existing time/code/memory proofs
  apply to this identical code.
- [SourcePrefix](../Signatures/Runtime/Caliper/SourcePrefix.lean) tracks adaptive
  source prefixes using supported replies and states from the same stateful
  oracle. Every supported completed simulation has such a path. Query allowances
  decrease along these paths, and list growth is bounded by requests used.
  [BLSCacheReachability](../Signatures/Runtime/Caliper/BLSCacheReachability.lean)
  proves the cache's input invariant immediately before every reachable request.
  `good_ready` and `bad_ready` use the original reductions' query theorems to
  reserve `2*q+1` entries from an empty table, including extraction and the final
  target. Scalar values must fit, and actual queried messages must satisfy the
  key layout; no finite-message-domain instance is required. A regression uses
  unbounded natural-number keys with only encountered keys represented, proving
  both adaptive hit/miss branches and executing their Caliper continuations.
  These results discharge the private-cache capacity obligation, not the complete
  scheme controller, caller-storage or replay certificates.
- [PairSampling](../Signatures/Runtime/Caliper/PairSampling.lean) constructs an
  independent pair sampler from two certified component samplers. The first
  result is saved beyond the second sampler's lowered buffer footprint, restored
  after that draw, then permuted into output order by executed instructions.
  The product uniform-sampling law follows from the two component laws.
  [PairSamplingBounds](../Signatures/Runtime/Caliper/PairSamplingBounds.lean)
  proves `T=t1+t2+20*a+16*b`, `C=c1+c2+65*a+52*b+58`, and dense name bound
  `S=max(3,max(s1,s2+1))`, for component word widths `a,b`, time budgets `t1,t2`,
  code budgets `c1,c2`, and name reservations `s1,s2`.
  [PairSamplingMemory](../Signatures/Runtime/Caliper/PairSamplingMemory.lean)
  bounds complete memory at every visited state by
  `C+4*S+initialRegisterSlots+3*initialBufferSlots+initialCapacity+T`.
  Generated-word acceptance is derived from the component descriptions and the
  second component's name reservation fitting the word width.
  [BLSCachePairs](../Signatures/Runtime/Caliper/BLSCachePairs.lean) uses two copies
  of the scalar sampler in the existing pair-valued private cache. It derives
  the cache's source equality, time/code bounds and description acceptance; no
  separate pair sampler or pair-sampling law is assumed. The wider table and
  its additional saved buffer have explicit width obligations. Scalar sampling
  from a fair-bit tape remains separate from this composition theorem.
  Regression executions check different first/second replies, output order,
  two input consumptions, unrelated caller storage, a callee using buffer 2,
  and full-cache hits that
  skip both draws. One-word components with four-step/20-word scalar draws have
  pair budgets of 44 steps, 215 code words and four name slots.

- [BLSResponse](../Signatures/Runtime/Caliper/BLSResponse.lean) constructs both
  AGM branches' response arithmetic from named scalar-multiplication and group-
  addition implementations. Argument selection, shared-input retention and all
  copies execute Caliper code. The good branch returns `rho*g` for hashing or
  `rho*X` for signing. The bad branch forms `alpha*X+beta*g` and multiplies by
  `kappa` for signing. [BLSResponseBounds](../Signatures/Runtime/Caliper/BLSResponseBounds.lean)
  derives affine budgets in the scalar/point widths and the two primitive budgets:
  with widths `a,g`, primitive times `ts,ta` and code budgets `cs,ca`, good replies
  use `T=ts+96*a+144*g`, `C=cs+312*a+468*g+168`. Bad hash replies use
  `T=2*ts+ta+604*a+476*g`, `C=2*cs+ca+1963*a+1547*g+521`; bad signing replies use
  `T=3*ts+ta+812*a+612*g`, `C=3*cs+ca+2639*a+1989*g+675`.
  [BLSResponseMemory](../Signatures/Runtime/Caliper/BLSResponseMemory.lean)
  connects the actual output to the existing `LazyAGM.goodResponse`/`badResponse`
  source definitions and bounds every state in that same run by
  `5*C+4*primitiveSlots+initialRegisterSlots+3*initialBufferSlots+initialCapacity+T`.
  Generated descriptions fit the word width; the layout and scratch-name
  reservations are explicit. Regression executions cover all four response
  variants, distinct and zero masks, and preservation of unrelated caller storage.
  [ImplementationMemory](../Signatures/Runtime/Caliper/ImplementationMemory.lean)
  exposes the reusable local memory theorem independently of signature games.
  These response implementations are used by the complete reply handlers below.
- [BLSRecord](../Signatures/Runtime/Caliper/BLSRecord.lean) constructs the update
  of the selected reverse-order reply log and returns the delivered point. Its
  specification is the original `LazyAGM.record`. Both logs retain fixed capacity;
  inserting a reply, preserving the unselected log, and returning the point all
  execute charged copies. Full unselected logs are supported. Repeated delivered
  replies each receive an entry, even when the private lookup was a cache hit.
  [BLSRecordBounds](../Signatures/Runtime/Caliper/BLSRecordBounds.lean) derives
  `T=208*e+44*g+476*l+5` and `C=676*e+143*g+1547*l+527`, where `e` is the encoded
  message/point entry width, `g` the point width and `l=1+capacity*e` the padded
  width of one log. The complete returned-point/log operation uses at most five
  buffer slots. Every intermediate state's total memory is bounded by
  `5*C+initialRegisterSlots+3*initialBufferSlots+initialCapacity+T`, with no supplied
  primitive budgets. [BLSRecordReachability](../Signatures/Runtime/Caliper/BLSRecordReachability.lean)
  establishes the input domain before each hash/sign query in a supported prefix
  of the original `LazyAGM.listOracle`: initially stored replies plus the query
  allowance must fit the log capacity, queried messages must be representable,
  and the response functions must preserve the point domain. Private randomness
  leaves the logs unchanged. The theorem applies to arbitrary adaptive source
  programs and does not enumerate the message space. Regressions execute both
  updates with a full unselected log, repeated and first replies, domain checks
  excluding a full selected log or an unrepresentable message, and both branches of an actual
  adaptive source prefix. Caller contents, spare capacity and tape position survive.

- [BLSReplySchemes](../Signatures/Runtime/Caliper/BLSReplySchemes.lean) assembles
  both complete AGM reply handlers from scalar sampling, scalar multiplication
  and addition. The good handler uses the scalar cache; the bad handler uses
  the actual pair sampler and pair-valued cache. Challenge points `g,X` and the
  bad signing scalar `kappa` are stored input data. The generated preparation
  saves the original message/configuration/state across the cache call, computes
  the response once, records that point and returns the updated store. Every
  projection, constant encoding, retained frame and output copy executes code.
  [BLSReply](../Signatures/Runtime/Caliper/BLSReply.lean) proves equality with
  the original `LazyAGM.listReply`, jointly preserving reply, configuration,
  cache and both logs. The source and target synchronize their sampling calls;
  an outer cache hit draws nothing but still records the delivered reply.
  [BLSReplyBounds](../Signatures/Runtime/Caliper/BLSReplyBounds.lean) derives
  `T=cacheTime+responseTime+2272*W+5` and
  `C=cacheWords+responseWords+7384*W+2196`, where
  `W=cacheInputWords+configWords+pointWords+2*logWords` and
  `logWords=1+logCapacity*(messageWords+pointWords)`. Cache and response terms
  are themselves derived from named primitive budgets. No finished-reply
  implementation or efficiency assumption is supplied.
  [BLSReplyMemory](../Signatures/Runtime/Caliper/BLSReplyMemory.lean) bounds
  every visited state of the same actual execution that returns a represented,
  supported source answer. Its bound is
  `5*C+4*max(5,drawSlots,responseSlots)+initialRegisterSlots+3*initialBufferSlots+initialCapacity+T`.
  Stored descriptions fit with one additional scratch-name reservation above
  the sampler; [CacheReadBuffers](../Signatures/Runtime/Caliper/CacheReadBuffers.lean)
  derives the cache extent `max(8,drawBuffers+1)` independently of code size.
  Word-execution regressions cover both branches' hash/sign replies, distinct
  scalar masks, one/two miss draws, hits skipping draws, duplicate delivered
  replies, a full unselected log, invalid message/log domains, and preservation
  of unrelated caller contents, spare capacity, registers and tape position.
  The tests use word arithmetic to check wiring; curve implementations retain
  their named primitive obligations. Scalar uniformity is still an explicit
  primitive law. The complete handler requires its cache hit-or-room and
  selected-log-room invariants; connecting the existing prefix capacity proofs
  through whole-reduction controllers remains integration work.

Remaining integration sequence:

1. Compile the remaining scheme code and establish reachable-state invariants.
   Fixed-capacity `cacheProgram` and `cacheGetExpr`, encoded
   key/message equality, the original
   atomic-comparison `Lookup`, and structured `LookupExpr` now have actual
   implementations and derived budgets, with total encoded lookup compilation
   proved for all admitted layouts and total cache programming/reads on their
   hit-or-room domain (reads require a certified primitive draw). Prove successful emission for the remaining
   scheme code, and refine the source's unbounded
   `Nat` and lists along reachable executions. List construction, case analysis,
   capacity growth and folds are
   implemented, as are tag dispatch, projection/length and saved-state composition.
   Folds preserve domains for entries and accumulators. Scalar operations now
   include bounded naturals, Booleans and finite counters; structural composition
   includes paired computations and source projections/branches. The checked
   compiler now covers all original expression constructors, subject to the
   admitted domains, including iteration-dependent domains for growing folds.
   The bounded-source layout and loop refinement are implemented; the particular
   signature programs still need their reachable-state invariants and primitive
   refinements beyond the BLS private-cache invariant above. A fixed-width
   representation cannot honestly supply all the old
   closure instances unchanged.
2. Instantiate compilation certificates for the signature programs through these layouts.
   The local category above does not yet instantiate `BackendAssembly.Backend`:
   that interface requires unrestricted product/sum closure, unbounded counters,
   external queries and exact cost equations. The new bounded local constructors
   do not imply those contracts unchanged. The interactive compiler now proves
   source refinement for every control constructor, including counted iteration.
   Uniform runtime/additional-buffer bounds now follow from actual primitive
   budgets. Carry the expression name bounds through interactive wrappers and
   oracle-call implementations when assembling scheme-family memory bounds.
   Checked emission proves generated-word acceptance and intermediate
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
