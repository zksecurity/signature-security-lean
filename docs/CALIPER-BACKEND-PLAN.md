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
  primitive law. Whole-reduction controller integration remains below.
- [BLSReplyReachability](../Signatures/Runtime/Caliper/BLSReplyReachability.lean)
  combines represented configuration, cache entries, transcript entries and
  remaining capacity in one `Reserved` invariant. It holds along every supported
  adaptive prefix of the original random/hash/sign oracle, from the initial
  reservation and total query allowance. `prefix_ready` derives the complete
  reply input guard. Reply-domain preservation follows from the constructed
  handler's source law, without another global response-domain assumption.
- [BLSDispatch](../Signatures/Runtime/Caliper/BLSDispatch.lean) executes the stored
  hash/sign tag, branch and payload normalization. Time is bounded by the larger
  reply budget plus `8*W+2`; stored code includes both reply bodies plus
  `52*W+40`. The [memory proof](../Signatures/Runtime/Caliper/BLSDispatchMemory.lean)
  charges static code, registers, descriptors, all initial buffer capacities and
  intermediate allocation in the same supported execution.
  [Source linkage](../Signatures/Runtime/Caliper/BLSDispatchSource.lean) identifies
  the original joint reply/configuration/cache/transcript distribution and proves
  that supported machine returns preserve the remaining reservation.
  [Both scheme dispatchers](../Signatures/Runtime/Caliper/BLSDispatchSchemes.lean)
  use the constructed good/bad responses and scalar/pair samplers, with primitive
  implementation and sampling assumptions only. Adaptive operational regressions
  inspect the first returned point's bits, then execute another hash/sign request
  using copies of the stored configuration, cache and logs. Both repeated hits
  and fresh signing misses are checked for both reductions. These small clients
  are regressions; the prefix invariant quantifies over arbitrary source clients.
  This hash/sign dispatcher is included in the full query service below.
- [UniformQuery](../Signatures/Runtime/Caliper/UniformQuery.lean) forwards a range
  chosen at runtime to the original uniform oracle. A request occupies one word;
  the dependent reply occupies two (range and sampled index), with `index <= range`
  checked by the representation decoder. No table of all ranges is constructed.
  The raw exchange costs 10 steps and 41 code words. Forwarding with a saved
  `S`-word store executes copying, costs at most `34+12*S` steps and `160+39*S`
  code words, and uses at most three named registers/buffers. This establishes
  the ideal uniform-port law, not a fair-bit implementation of arbitrary sampling.
- [BLSOracle](../Signatures/Runtime/Caliper/BLSOracle.lean) joins random forwarding
  and hash/sign dispatch on this common port. Request and reply tags, payload
  normalization and padding are executed instructions. Random queries return the
  unchanged stored configuration/cache/logs. [Source equality](../Signatures/Runtime/Caliper/BLSOracleSource.lean)
  identifies the original `LazyAGM.listOracle` answer and private state jointly
  for all three query kinds. [Readiness](../Signatures/Runtime/Caliper/BLSOracleReady.lean)
  derives a represented request with the exact original query/state at every
  adaptive source prefix from its initial reservation, total query allowance,
  represented messages and random-range bound. This is a representation theorem;
  it does not claim that a caller constructs packets for free.
  [Resource bounds](../Signatures/Runtime/Caliper/BLSOracleBounds.lean) use
  `W = BLSReply.width + 3`: time is at most `max(34+12*W,dispatchTime)+16*W+2`,
  and code at most `dispatchCode+143*W+232`. All stored branches are counted.
  [Complete memory](../Signatures/Runtime/Caliper/BLSOracleMemory.lean) includes
  code, names, initial capacity and every intermediate state of the same execution
  that returns the represented source result, using the reusable
  [interactive resource theorem](../Signatures/Runtime/Caliper/InteractiveMemory.lean).
  [Both services](../Signatures/Runtime/Caliper/BLSOracleSchemes.lean) construct
  their responses from scalar sampling and scale/add routines. Regressions use
  an actual constant-range query/projection sampler on the shared port, then run
  hash -> adversary randomness -> sign/hash with machine copies of the private
  store between all calls. Out-of-range requests and dependent replies are rejected.
  Whole-caller storage separation, setup, final-forgery handling and extraction
  remain to be linked. Capacity accounting must also include the extraction's
  additional private-cache calls and charged chronological transcript reversal.
- [InteractiveInvariant](../Signatures/Runtime/Caliper/InteractiveInvariant.lean)
  composes refinement on reachable domains. Structural synchronization retains
  source support at each returned leaf; sequencing and loops use it to carry a
  decreasing capacity reservation. Dispatch and saved-state composition execute
  their existing code. [Bounds](../Signatures/Runtime/Caliper/InteractiveInvariantBounds.lean)
  derive `stopTime + fuel*(bodyTime + loopOverhead)` and complete memory accounting
  for the same supported run, including stored instructions, metadata and all
  initial capacity. Restricting a proof domain neither tests it at runtime nor
  provides free state changes.
- [SumContext](../Signatures/Runtime/Caliper/SumContext.lean) constructs the
  distribution `(A+B)*S -> (A*S)+(B*S)` with actual instructions. With unequal
  payload widths, padding moves from before the saved context to after it;
  mathematical reassociation alone would give the wrong bytes.
  [Bounds](../Signatures/Runtime/Caliper/SumContextBounds.lean) charge at most
  `24*W+2` steps and `156*W+95` code words, where
  `W = 1 + max(A.words,B.words) + S.words`. Both stored branches are counted.
- [CallerStep](../Signatures/Runtime/Caliper/CallerStep.lean) constructs request
  routing, preservation of pending caller state across the handler, reply
  routing, and preservation of the new private store across the caller's local
  continuation. The continuation returns either a result or a next request and
  caller state. Its actual code is supplied by the caller; the handler's actual
  code is supplied by its independent construction proof. The complete step is
  generated here, with structural source refinement on the handler's readiness
  domain. [Bounds](../Signatures/Runtime/Caliper/CallerStepBounds.lean) add at most
  `80*W` time and `260*W+128` code words to those two implementations, with
  `W = 1 + state.words + request.words + reply.words + result.words + store.words`.
  Description acceptance and dense name bounds are derived compositionally.
  [Regressions](../SignaturesTest/CaliperCaller.lean) instantiate the step with
  the shared uniform port and a real caller continuation that selects its next
  request from the previous reply. Two-call executions preserve both caller and
  private states, unrelated buffer contents and spare capacity, a register and
  the tape cursor. They exercise zero-range follow-ups, zero-fuel stopping and
  both unequal-width routing branches. A decreasing-domain loop refinement and
  time bound are checked for every represented input and supported reply.
  The complete generated controller and original-machine bridge are described
  below. Dependent BLS packet routing, finalization and extraction still need
  their scheme-specific composition proofs.
- [CallerControl](../Signatures/Runtime/Caliper/CallerControl.lean) constructs
  initialization with a retained private store, initial-result dispatch, a
  bounded handler/continuation loop, early return and cutoff. Final packets retain
  either a result or the pending request and caller state. Cutoff stays distinct
  from return in the actual stored tag. [Refinement](../Signatures/Runtime/Caliper/CallerControlRefinement.lean)
  carries readiness and decreasing reservations through supported handler replies;
  no finished-controller implementation or efficiency contract is assumed.
  [Routing](../Signatures/Runtime/Caliper/CallerControlRouting.lean) charges all
  padding, tag and saved-state transfers. For `W = CallerStep.width`, input width
  `A`, allowance `q`, and primitive times `I,L,H`, the
  [complete time bound](../Signatures/Runtime/Caliper/CallerControlTime.lean) is
  `I + 8*A + 88*W + 4 + q*(H + L + 172*W + 6)`.
  [Stored instructions](../Signatures/Runtime/Caliper/CallerControlStorage.lean)
  occupy at most `CI + 26*A + 507*W + 286 + q*(CH + CL + 742*W + 389)` words.
  This includes every inlined copy of the bounded loop body. Description
  acceptance and dense register/buffer name bounds follow from the primitive
  implementations and their reserved names.
- [CallerMachine](../Signatures/Runtime/Caliper/CallerMachine.lean) connects the
  controller to an arbitrary original `OracleMachine`. Explicit views relate
  bounded caller/private states to the original mathematical types. The local
  caller transition matches the original next head; handler synchronization
  matches typed replies and private state jointly. The whole-run correspondence
  is proved by induction, preserving the original adaptive query tree.
  `ImplementsWithin` identifies the source program and rules out fuel exhaustion.
  [CallerExecution](../Signatures/Runtime/Caliper/CallerExecution.lean) applies this
  bridge to the actual generated word program and proves its complete memory
  account for every visited state of the same supported execution. Initial
  buffer capacity, code, register slots and descriptors are all included.
  [Regressions](../SignaturesTest/CaliperCallerControl.lean) check immediate return
  at zero allowance, pending cutoff, return after a query, early return with spare
  allowance, and repeated adaptive calls ending in cutoff. They check traces,
  unconsumed replies and unrelated machine storage. An original machine with a
  Nat query interface and an implementation certificate is instantiated; kernel
  proofs connect its source program to the actual controller and instantiate
  time and every-intermediate-state memory bounds. These fixtures test the generic
  theorem and do not establish coverage of all efficient Caliper attackers or
  instantiate BLS's dependent packets and source correspondences.
- [SumContextMerge](../Signatures/Runtime/Caliper/SumContextMerge.lean) executes
  the inverse union/context conversion, with time at most `44*W + 2`, stored
  code at most `286*W + 143` and accounted names, where `W` is the full packet
  width. The private store is retained while the chosen union tag and padding
  are written, then copied into its final position.
  [BLSCallerPackets](../Signatures/Runtime/Caliper/BLSCallerPackets.lean) uses
  executed nested distribution and this merge to convert the generic caller's
  separate request/reply and private-store pairs to the existing BLS service.
  Mathematical proof packaging changes no bytes: `request_bytes` proves that
  the constructed request has exactly the service's encoding on its ready domain.
  [Bounds](../Signatures/Runtime/Caliper/BLSCallerPacketBounds.lean) charge at most
  `64*W + 6` time and `420*W + 270` stored code for request preparation, and
  `44*W + 2` time and `286*W + 143` stored code for reply conversion, with
  `W = 3 + messageWords + pointWords + storeWords`.
  [Regressions](../SignaturesTest/CaliperBLSPackets.lean) execute random/hash/sign
  preparation and random/group replies with a nonempty cache and transcript.
  They check padding movement in both directions, unrelated machine storage,
  untouched replies/tape position, and non-readiness of a full signing log even
  on a cache hit. The source message type is infinite; only represented messages
  are used. The composed BLS handler below supplies its source and reservation
  laws; the whole-controller bridge is instantiated below.
- [BLSCallerHandler](../Signatures/Runtime/Caliper/BLSCallerHandler.lean) composes
  actual request preparation, the complete random/hash/sign service, and actual
  reply reconstruction. It proves `RefinesOn ready`, time at most the existing
  service budget plus `108*W + 8`, and stored code at most the existing service
  budget plus `710*W + 420`. Name bounds and accepted instruction descriptions
  follow from the constructed converters and primitive implementations.
  Its total mathematical source has an inert extension outside the ready domain;
  no correctness or resource claim applies there, and reservations exclude it.
  [BLSCallerSource](../Signatures/Runtime/Caliper/BLSCallerSource.lean) proves exact
  original-oracle query-tree equality jointly with the reply and entire private
  store. Random packets preserve both the requested range and the sampled index.
  [Synchronization](../Signatures/Runtime/Caliper/SynchronizesObservations.lean)
  derives joint leaf correspondence from literal equality of observed free
  computations, rather than equality only after probabilistic interpretation.
  [BLSCallerInvariant](../Signatures/Runtime/Caliper/BLSCallerInvariant.lean) derives
  query admission from represented messages, readiness from `Reserved (n+1)`, and
  `Reserved n` for every supported handler output using the original oracle's
  proved growth bound. No finished-handler equivalence or efficiency contract is
  an input. The packet regressions additionally instantiate these theorems with
  an actual uniform-draw routine and a small word response routine, execute all
  three handler branches (including a cache hit and a signing miss), and audit
  the endpoint axioms. This fixture is not a curve implementation or a theorem
  covering all attackers. The caller assembly below connects these components;
  reduction finalization remains open.

- [BLSCaller](../Signatures/Runtime/Caliper/BLSCaller.lean) constructs the complete
  caller from actual local initialization/continuation code and the generated BLS
  handler. Its invariant combines a local pending-state domain with the private
  store's decreasing reservation. Local preservation is required only on replies
  matching the pending source query; readiness, typed reply compatibility and
  reservation preservation follow from the existing handler proofs.
  [BLSCallerExecution](../Signatures/Runtime/Caliper/BLSCallerExecution.lean) proves
  equality with the original source computation, retaining the whole final store.
  The original machine's `ImplementsWithin` certificate excludes cutoff. These
  are local caller implementation obligations, not assumptions of completed
  controller or reduction correctness.
  [BLSCallerResources](../Signatures/Runtime/Caliper/BLSCallerResources.lean)
  substitutes actual sampler/response and local caller budgets into time, code,
  generated-name and whole-execution memory bounds. With caller frame width `W`,
  input width `A`, allowance `q`, initialization time `I`, continuation time `L`
  and constructed-handler time `H`, elapsed time is at most
  `I + 8*A + 88*W + 4 + q*(H + L + 172*W + 6)`.
  Stored code counts every unrolled body. The memory theorem uses this same
  supported execution and includes all initial capacity and every visited state.
  Primitive implementations and finite layout/name bounds remain explicit.
  The packet regression now supplies an actual adaptive caller: a random reply
  selects a hash message, a cache miss draws a scalar, and the caller returns the
  resulting point. It instantiates the original-machine/source and resource
  endpoints and checks zero-fuel cutoff, cutoff after the first reply, final
  cache/transcript contents, and unrelated storage/replies/tape preservation.
  Its response routine is a small word operation, not curve code; this does not
  establish coverage of every Caliper attacker or finalize the full reduction.

- [BLSInitialization](../Signatures/Runtime/Caliper/BLSInitialization.lean) copies
  a runtime caller input and configuration, then writes the complete bounded
  empty cache and transcript encodings. Every word is charged: time is at most
  `8*outputWords`, stored code at most `26*outputWords + 14`. The resulting store
  has a proved reservation up to the configured cache and log capacities.
  [BLSSetup](../Signatures/Runtime/Caliper/BLSSetup.lean) builds both AGM setup
  branches from runtime challenge data. The good branch selects the supplied
  public key and stores the challenge points. The bad branch retains the
  challenge while sampling a scalar, calls an individual scale routine to obtain
  its public key, and stores the sampled scalar with the challenge points.
  [BLSSetupSampling](../Signatures/Runtime/Caliper/BLSSetupSampling.lean) proves
  exact source-tree correspondence, using only the primitive sampler's uniform
  law. No completed setup implementation or efficiency premise is supplied.
  [BLSSetupResources](../Signatures/Runtime/Caliper/BLSSetupResources.lean) derives
  time, complete code, generated names, accepted descriptions and memory bounds
  for every state visited by the same sampled execution. The linear overhead
  depends on the admitted setup width; sampler and scale costs remain explicit.
  [Regressions](../SignaturesTest/CaliperBLSSetup.lean) vary runtime challenge
  values and scalar replies (including zero), check cache/transcript padding and
  untouched storage/replies/tape, instantiate source/resource endpoints and
  audit their axioms. The executable scale fixture uses word arithmetic, not a
  curve implementation. `BLSFull` below now composes these setup and caller
  phases with final-forgery handling and extraction. Public model/family
  certificates remain outstanding.

- [ListReverse](../Signatures/Runtime/Caliper/ListReverse.lean) constructs actual
  reversal of an admitted source list. Its staged fold grows the accumulator
  and executes padding on early return. [StagedFoldAcceptance](../Signatures/Runtime/Caliper/StagedFoldAcceptance.lean)
  proves successful emission from the local body implementations and bounds the
  reused scratch namespace independently of traversal capacity.
  [ListReverseBounds](../Signatures/Runtime/Caliper/ListReverseBounds.lean) derives
  polynomial time and stored-code budgets from entry width and list capacity;
  it includes all copied/padded words and stored unrolled bodies. The reversal
  uses at most three buffer names. Its memory theorem includes stored code,
  registers/descriptors, all initial capacity and every intermediate state.
  [BLSChronological](../Signatures/Runtime/Caliper/BLSChronological.lean) executes
  this reversal for both explicit-reply logs, implementing the original source
  `chronological` view with at most four buffer names. If one reversal has
  budgets `T`/`C` and each stored log has `L` words, the complete preparation
  costs at most `2*T + 172*L` steps and `2*C + 559*L + 154` code words.
  [Regressions](../SignaturesTest/CaliperBLSChronological.lean) check empty,
  partial and full lists, zero-capacity and zero-word-entry layouts, invalid
  length/entry bounds, duplicate-message transcript occurrences, separate log
  padding, released scratch and untouched caller storage. Source/resource
  endpoints and axiom guards are instantiated. Coefficient association is
  implemented below, as is private row evaluation; both now participate in the
  complete BLS extractors described below.

- [ListIndex](../Signatures/Runtime/Caliper/ListIndex.lean) implements positional
  lookup from a runtime index, default and bounded stored list. Its constructed
  body executes counter comparison, saturating subtraction and found-value
  retention; preparation and result projection also execute charged copies.
  The source result is exactly `list[index]?.getD default`, matching the original
  arithmetic-language indexing theorem. The index bound and list capacity are
  independent, and no enumeration of the value domain occurs. Missing
  coefficients can therefore use zero without discarding extra stored entries
  for free: the complete suffix is still traversed after a hit.
  [ListIndexBounds](../Signatures/Runtime/Caliper/ListIndexBounds.lean) derives
  uniform time, complete stored-code, name and all-visited-memory bounds, with
  at most six buffer names. For capacity `n`, entry width `s`, and
  `W = 3 + (n + 1)*s`, the budgets are
  `T = 384*W + 88 + n*(1088*W + 407)` and
  `C = 1248*W + 927 + n*(3638*W + 2615)`.
  Layouts require `8*W < 2^w`, a fitting list count and a positive fitting index
  bound. Zero-capacity lists and zero-word entries are supported.
  [Regressions](../SignaturesTest/CaliperListIndex.lean) execute first/middle/last
  and missing lookups, maximum-word indices, runtime defaults, independent
  capacities, multiword and zero-word entries, and check invalid encodings,
  charged suffix traversal, released scratch, preserved caller storage and
  theorem axioms. This supplies lookup for the coefficient association below.

- [AttachRows](../Signatures/Runtime/Caliper/AttachRows.lean) constructs positional
  coefficient rows with an accepted staged fold. Each body executes the complete
  bounded lookup, creates one row, and increments a runtime counter with a proved
  no-wrap bound. The growing row buffer and counter have stage-specific domains;
  early exits execute padding, and an executed final reversal restores key order.
  [AttachRowsBounds](../Signatures/Runtime/Caliper/AttachRowsBounds.lean) derives
  time, complete stored-code and all-visited-memory bounds from key/coefficient
  capacities and word widths. The complete routine uses at most ten buffer names.
  Key and coefficient capacities are independent; empty and zero-word-entry
  layouts are supported. Only the supplied key list is traversed.
  [TokenRows](../Signatures/Runtime/Caliper/TokenRows.lean) first reverses the
  stored transcript, retains the complete coefficient list, writes an encoded
  default, and executes row attachment. The default's encoding is charged in
  code and runtime. [TokenRowsSource](../Signatures/Runtime/Caliper/TokenRowsSource.lean)
  specializes it to zero and proves that the actual Caliper program implements
  the original AGM `tokenRows` expression, including both message and returned
  group-point components of every chronological token. Missing coefficients are
  zero and extra coefficients create no rows; their stored suffix is still
  copied and scanned. The whole-program bounds are derived, not assumed.
  [Regressions](../SignaturesTest/CaliperTokenRows.lean) execute empty, partial,
  full and unequal-capacity inputs, zero-word layouts, the last counter step,
  duplicate messages with different returned points, missing/surplus coefficients,
  early padding and all scratch release. They reject invalid counters and input
  bounds, check that surplus coefficients increase charged work, and audit the
  complete source bridge and resource proofs. The row evaluator below consumes
  these rows; the complete BLS extractors below join row preparation, evaluation,
  final lookup and arithmetic.

- [BLSAccumulate](../Signatures/Runtime/Caliper/BLSAccumulate.lean) constructs
  scalar `acc + coeff * answer` and both coordinates of pair accumulation from
  individual scalar multiplication/addition implementations. Copies, projections
  and each stored routine occurrence are charged. With scalar width `s`, scalar
  time budgets `Tm, Ta` and code budgets `Cm, Ca`, the scalar update costs at most
  `Tm + Ta + 472*s` steps and `Cm + Ca + 1534*s + 322` code words. The pair update
  costs at most `2*Tm + 2*Ta + 2776*s` steps and `2*Cm + 2*Ca + 9022*s + 1470`
  code words. [BLSAccumulateSource](../Signatures/Runtime/Caliper/BLSAccumulateSource.lean)
  proves agreement with the original `goodCombine` and `badCombine` expressions.
  No complete accumulator implementation is assumed.
  [CacheAccumulate](../Signatures/Runtime/Caliper/CacheAccumulate.lean) retains
  the represented coefficient and accumulator across the actual encoded cache
  read, then constructs update arguments and returns the new accumulator jointly
  with the updated cache. On the explicit hit-or-room domain, this agrees with
  the original association-list handler and adds at most one cache entry.
  Its overhead beyond the cache read and local update is at most `404*W` steps
  and `1313*W + 532` code words, where `W` includes the cache request, coefficient
  and accumulator widths. [CacheAccumulateMemory](../Signatures/Runtime/Caliper/CacheAccumulateMemory.lean)
  bounds generated names, stored descriptions and every intermediate state of
  the same execution, including initial caller capacity.
  [BLSPrivateAccumulate](../Signatures/Runtime/Caliper/BLSPrivateAccumulate.lean)
  instantiates both updates and derives the pair sampler from two scalar draws.
  [Source agreement](../Signatures/Runtime/Caliper/BLSPrivateAccumulateOracle.lean)
  uses the existing BLS private oracle, with its uniform scalar law explicit;
  these reads create no public transcript tokens. [Regressions](../SignaturesTest/CaliperBLSPrivateAccumulate.lean)
  exercise full-cache hits without sampling, scalar/pair misses, zero and distinct
  coordinates, duplicate-key priority, invalid full-cache misses and message
  bounds, caller storage preservation and scratch release. This is the compiled
  per-read update used by the row loop below. Final-target arithmetic is
  implemented below; complete solver composition remains.

- [InteractiveFold](../Signatures/Runtime/Caliper/InteractiveFold.lean) constructs
  an effectful list fold from an executed body, a runtime length branch and
  charged head/tail copies. Capacity bounds the stored unrolling; an empty or
  partially occupied list stops early. Its decreasing invariant reserves actual
  tail length. With entry width `e`, state width `s`, capacity `n`, and
  `W = 1 + (n+1)*e + s`, the derived budgets are `8*s + n*(Tbody + 44*W + 7)`
  steps and `26*s + 15 + n*(Cbody + 169*W + 130)` stored code words.
  [InteractiveFoldMemory](../Signatures/Runtime/Caliper/InteractiveFoldMemory.lean)
  proves instruction acceptance and memory throughout the same execution,
  including initial caller capacity and the complete stored program.
  [RowRequest](../Signatures/Runtime/Caliper/RowRequest.lean) constructs each
  private lookup request and its saved coefficient/accumulator by actual copies
  and literal default construction. Point bytes remain in the row encoding.
  Its bounds are `584*Wrow` steps and `1898*Wrow + 779` code words, where
  `Wrow` includes the accumulation frame and point width.
  [RowEvaluation](../Signatures/Runtime/Caliper/RowEvaluation.lean) composes this
  preparation with the existing private cache/read update and proves that
  `cache.length + remainingRows <= cacheCapacity` is preserved after consuming
  one row. [RowFold](../Signatures/Runtime/Caliper/RowFold.lean) instantiates the
  actual fold with this constructed body, deriving time, code, names and
  [whole-memory bounds](../Signatures/Runtime/Caliper/RowFoldMemory.lean).
  Its [postcondition](../Signatures/Runtime/Caliper/RowFoldPostcondition.lean)
  bounds total cache growth by the occupied row count and preserves any extra
  reservation for subsequent row folds or the final target lookup.
  [BLSRows](../Signatures/Runtime/Caliper/BLSRows.lean) instantiates scalar and
  pair accumulation from named scalar routines, including two scalar draws for
  a pair miss. Its [source agreement](../Signatures/Runtime/Caliper/BLSRowsOracle.lean)
  is an equality to the ordered fold using the original BLS private oracle,
  preserving both accumulator and final cache. No whole row evaluator is assumed.
  [Execution regressions](../SignaturesTest/CaliperBLSRows.lean) cover empty and
  zero-capacity loops, two successive misses, repeated messages with different
  points, cache hits, zero coefficients, missing replies, partially occupied
  row capacity, preserved caller storage and released scratch space.

- [BLSExtractArithmetic](../Signatures/Runtime/Caliper/BLSExtractArithmetic.lean)
  constructs the terminal scalar arithmetic from named subtraction, negation
  and division routines. The good branch computes `numerator/(target-signatures)`;
  the bad branch computes `-(target.2-signatures.2)/(target.1-signatures.1)`.
  Division remains total. For scalar width `s`, good arithmetic takes at most
  `232*s + Tsub + Tdiv` steps and `754*s + 154 + Csub + Cdiv` stored code words.
  Bad arithmetic takes at most `1160*s + 2*Tsub + Tneg + Tdiv` steps and
  `3770*s + 552 + 2*Csub + Cneg + Cdiv` code words. Argument copies and both
  coordinate projections are executed and charged.
  [CacheScalarResult](../Signatures/Runtime/Caliper/CacheScalarResult.lean)
  retains the extraction inputs across the existing private read, executes
  the scalar arithmetic and returns the entire updated cache. It accommodates
  scalar and pair cache values with a scalar result. Its bounds are
  `Tread + Tupdate + 404*W` steps and `Cread + Cupdate + 1313*W + 532` code words,
  with the existing cache/frame width `W`. [Memory bounds](../Signatures/Runtime/Caliper/CacheScalarMemory.lean)
  include stored instructions, dense names, descriptors, initial caller capacity
  and all visited states of the same execution.
  [BLSFinalTarget](../Signatures/Runtime/Caliper/BLSFinalTarget.lean) instantiates
  both branches with the constructed arithmetic and scalar or paired sampling.
  [Source equality](../Signatures/Runtime/Caliper/BLSFinalTargetOracle.lean)
  uses the original private list oracle and preserves the entire cache.
  [Regressions](../SignaturesTest/CaliperBLSFinalTarget.lean) exercise full-cache
  hits without sampling, misses, first-hit duplicate semantics, empty caches,
  zero denominators, missing replies, both pair coordinates, preserved caller
  storage and released scratch space. The word-arithmetic fixtures test wiring;
  the general theorems require the selected field routines' actual contracts.
  The incoming good frame already contains `beta + hashes`; the executed
  constructor below now supplies that addition. The complete BLS extractors
  below join the transcript evaluations through physically retained frames.

- [TokenEvaluation](../Signatures/Runtime/Caliper/TokenEvaluation.lean) composes
  chronological token/coefficients preparation, literal initial-accumulator
  construction and the interactive private-cache fold into one executed phase.
  Its input contains the original reversed token list, coefficient list and cache.
  [Preparation](../Signatures/Runtime/Caliper/TokenEvaluationPrepare.lean)
  explicitly copies the cache and constructs the row/accumulator frame; changing
  subtype views is justified by equality of the encoded bytes.
  For the combined layout width `W`, preparation adds `448*W` steps and
  `1456*W + 291` code words to the existing token-row budgets. The complete phase
  then adds the row-fold budgets and two stored composition words.
  [Memory](../Signatures/Runtime/Caliper/TokenEvaluationMemory.lean) is bounded
  throughout that same execution. [Source and postconditions](../Signatures/Runtime/Caliper/TokenEvaluationSource.lean)
  preserve the original ordered cache fold and any reservation beyond the actual
  token count. Allocated list padding creates no private lookups.
  [BLSTokens](../Signatures/Runtime/Caliper/BLSTokens.lean) instantiates both scalar
  and pair branches with actual encoded zeros, scalar multiplication/addition and
  one or two scalar draws per miss. Its [source theorem](../Signatures/Runtime/Caliper/BLSTokensSource.lean)
  identifies the entire computation, including final cache, with the original
  `evalTerms (traceTerms coefficients chronologicalTokens)` under BLS's private
  oracle. No whole transcript evaluator is supplied as an assumption.
  [Execution checks](../SignaturesTest/CaliperBLSTokens.lean) cover chronological
  assignment, missing/surplus coefficients, repeated-message occurrences,
  zero-weight lookups, empty/full-cache and zero-token-capacity cases, incomplete
  sampling replies, cache reservation, instruction acceptance and caller storage.
  The signature phase retains its final forgery context in the composed tail
  below; the complete extractor also retains the signature transcript across
  the hash pass and executes the initial forgery routing.

- [CacheTargetFrame](../Signatures/Runtime/Caliper/CacheTargetFrame.lean) packs
  the returned transcript sum/cache and saved target/scalar into the final
  private-lookup request. Projections, literal defaults, retained input copies
  and output construction execute instructions. The hit-or-room invariant
  admits full-cache hits; a remaining-slot reservation supplies it on misses.
  Time is at most `616*W`, code at most `2002*W + 794`, and scratch buffer names
  are at most six. The entire cache capacity, including padding, is charged.
  [BLSFinalFrame](../Signatures/Runtime/Caliper/BLSFinalFrame.lean) constructs
  the good branch's numerator from separately stored `beta` and `hashes` using
  the named scalar addition routine. Its complete frame takes at most
  `864*W + addTime` steps and `2808*W + 1116 + addWords` code words. The bad
  branch uses the pair-valued constructor and preserves the original coordinate
  ordering. Bounds and names are derived from addition and the executed code;
  no whole-frame implementation contract is assumed.
  [Execution regressions](../SignaturesTest/CaliperBLSFinalFrame.lean) run these
  frames followed by the existing final lookup/extraction arithmetic. They cover
  hits, misses, duplicates, empty caches, zero division, incomplete pair replies,
  preserved caller storage and released scratch. The word fixture also checks
  that addition executes; it is not a field implementation.
  These constructors are used by the composed signature tail and the complete
  BLS extractors below, including the good branch's hash pass.

- [BLSSignatureTail](../Signatures/Runtime/Caliper/BLSSignatureTail.lean) joins
  signature-transcript evaluation, actual save/restore of the target and
  intermediate scalars, final request construction and private extraction.
  Both branches preserve the context in an allocated buffer beyond the
  evaluator's footprint. Their input reserves actual token count plus one
  target entry; the proved evaluator postcondition establishes final readiness.
  The good context stores `mstar`, `beta` and the already computed hash sum;
  the bad context stores `mstar` and `beta`.
  [Source equality](../Signatures/Runtime/Caliper/BLSSignatureTailSource.lean)
  recovers the original `evalTerms` followed by the original BLS private oracle,
  including the complete final cache, missing-coefficient queries and total
  division. Its source definitions specify the ideal random law; executed code
  is constructed separately from actual routines and the refined sampler.
  [Runtime](../Signatures/Runtime/Caliper/BLSSignatureTailBounds.lean) and
  [stored code](../Signatures/Runtime/Caliper/BLSSignatureTailWords.lean) add all
  phase budgets and the actual retain overhead. With input/output/context widths
  `a`, `b`, `s`, retention adds at most `8*a + 8*b + 12*s` steps and
  `26*a + 26*b + 39*s + 41` code words. [Memory bounds](../Signatures/Runtime/Caliper/BLSSignatureTailMemory.lean)
  cover every visited state of that same source-supported execution, including
  caller storage, context, dense names and buffer descriptors.
  [Acceptance](../Signatures/Runtime/Caliper/BLSSignatureTailAcceptance.lean)
  derives the saved-buffer fit from actual evaluator footprints.
  [TokenEvaluationBuffers](../Signatures/Runtime/Caliper/TokenEvaluationBuffers.lean)
  bounds those footprints independently of the number of unrolled rows.
  [Execution regressions](../SignaturesTest/CaliperBLSSignatureTail.lean) check
  chronological coefficients, missing and surplus coefficients, repeated-message
  reuse, zero-weight queries, target reuse, empty logs, partial replies, zero
  division, caller preservation and released scratch in the composed program.
  The complete BLS extractor below now supplies the initial routing and good
  hash pass. Complete BLS solver assembly and public model instantiation remain
  separate unfinished steps.

- [BLSExtractorLayout](../Signatures/Runtime/Caliper/BLSExtractorLayout.lean)
  represents the original `(mstar, beta, gamma, xi)` output alongside the cache
  and both reverse-stored transcripts. It derives combined address fits from
  the existing evaluator layouts and keeps coefficient and token capacities
  independent. [Initial routing](../Signatures/Runtime/Caliper/BLSExtractorRouting.lean)
  executes slice copies into the hash-evaluator input plus retained signature
  context; the bad route selects the signature input and original target/beta.
  Its input still stores the discarded hash explanation/log, and the memory
  theorem charges that initial capacity. These programs preserve log order;
  the existing evaluator remains responsible for chronological reversal.
  [The handoff](../Signatures/Runtime/Caliper/BLSExtractorTransition.lean) after
  hash evaluation executes another permutation, selecting the signature log
  and coefficients while retaining the updated cache, target, beta and hash sum.
  Its output is exactly the existing signature tail's input representation.
  [Resource proofs](../Signatures/Runtime/Caliper/BLSExtractorFrameBounds.lean)
  bound each router by `8*n` steps and `26*n + 14` stored code words, where `n`
  is its padded output width; three register slots and two buffer slots suffice.
  The same execution has a whole-memory bound at every visited state of
  `34*n + 14 + max(registers,3) + 3*max(buffers,2) + initialCapacity`.
  [Operational regressions](../SignaturesTest/CaliperBLSExtractorFrame.lean)
  check distinct gamma/xi and log lengths, surplus coefficients, empty logs,
  discarded hash data, scalar/pair caches, updated cache retention, exact output
  bytes, actual runtime, caller storage preservation and released scratch.
  These routers are used by the complete extractor composition below.

- [BLSExtractor](../Signatures/Runtime/Caliper/BLSExtractor.lean) constructs both
  complete BLS AGM private extractors from the original bounded forgery,
  reverse-stored hash/signature logs, and private cache. The good branch executes
  initial routing, a [retained hash pass](../Signatures/Runtime/Caliper/BLSExtractorHash.lean),
  the handoff, and the signature tail. The bad branch routes directly to its
  signature tail. Every supported hash result preserves enough capacity for the
  actual remaining signature tokens plus the final target; no extra ready-state
  or implementation contract is supplied for the composed phases.
  [Source equality](../Signatures/Runtime/Caliper/BLSExtractorSource.lean)
  identifies their erased results with the original `LazyAGM.goodFinish` and
  `badFinish` under the private list oracle, retaining the full final cache and
  exact query order. The scalar sampler's ideal-uniform law remains an explicit
  primitive contract. [Time](../Signatures/Runtime/Caliper/BLSExtractorBounds.lean)
  and [stored-code](../Signatures/Runtime/Caliper/BLSExtractorWords.lean) bounds
  include both transcript passes, all routing, saved-state copies and composition
  words. [Memory](../Signatures/Runtime/Caliper/BLSExtractorMemory.lean) covers
  every visited state of the same source-supported execution. [Acceptance](../Signatures/Runtime/Caliper/BLSExtractorAcceptance.lean)
  derives the hash context's saved-buffer fit from the actual evaluator footprint.
  [Whole-extractor regressions](../SignaturesTest/CaliperBLSExtractor.lean)
  cover disjoint and shared hash/signature messages, chronological coefficients,
  missing/surplus coefficients, repeated tokens, zero-weight lookups, target
  reuse, initial cache hits, empty logs, division by zero, partial responses,
  exact final cache/trace, measured runtime, caller preservation and scratch release.
  The word fixture tests composition; the general field theorems establish
  source equality. [Invariant views](../Signatures/Runtime/Caliper/InteractiveInvariantViews.lean)
  only change mathematical product views after proving identical encoded bytes.
  Caller termination and complete BLS AGM setup/caller composition are
  implemented below; public security-model instantiation remains unfinished.

- [BLSExtractionExit](../Signatures/Runtime/Caliper/BLSExtractionExit.lean)
  instantiates executed caller-return/cutoff handling with both complete AGM
  extractors. Its input contains the tagged forgery or pending caller state,
  union padding, configuration, cache, and reverse-stored transcripts.
  [Routing](../Signatures/Runtime/Caliper/BLSCallerFinishLayout.lean) copies the
  forgery and private store past padding and configuration. Successful returns
  run extraction and copy out the scalar; cutoffs execute a stored zero without
  querying or requiring extraction headroom. [Composition](../Signatures/Runtime/Caliper/BLSCallerFinish.lean)
  refines this control flow on the branch-specific reachable domain.
  [Resource bounds](../Signatures/Runtime/Caliper/BLSCallerFinishBounds.lean)
  include both stored branches, all copies, scalar projection, initial
  configuration/pending data and every visited memory state. Actual BLS
  instantiations derive time/code/name and operand-acceptance bounds from the
  already constructed extractors and their primitive contracts.
  [Source theorems](../Signatures/Runtime/Caliper/BLSExtractionExitSource.lean)
  identify successful exits with the original scalar `goodFinish`/`badFinish`
  computation and cutoff with zero. Operational regressions extend the complete
  extractor fixture with nonzero configuration, both padding directions,
  preserved caller storage, no-query cutoffs without extraction room, exact
  scalar outputs, charged runtime and incomplete sampling replies.
  [The service bridge](../Signatures/Runtime/Caliper/BLSCallerFinishService.lean)
  constructs the caller service with the extractor's cache, token encoding and
  log capacity, and proves that its stored configuration/cache/log bytes match
  the terminal frame. The caller's existing growth postcondition supplies both
  branches' extraction reservation; this is derived rather than assumed of the
  completed caller. The service uses positive log capacity, so a zero-query
  family can choose one slot. Its configuration/address fit is explicit.
  Generated caller execution now composes with this terminal handler below;
  setup is now joined into the full BLS AGM programs below.

- [BLSCallerExtraction](../Signatures/Runtime/Caliper/BLSCallerExtraction.lean)
  constructs the generated caller followed by terminal handling and extraction.
  [Layouts](../Signatures/Runtime/Caliper/BLSCallerExtractionLayout.lean) derive
  terminal width and exact input bytes from the shared caller service. The caller's
  growth theorem proves extraction readiness at every supported exit, using
  initial cache/log occupancy plus `2*q+1` headroom. Caller initialization,
  continuation and response routines supply local implementation proofs; no
  completed-caller correctness or growth assumption is introduced.
  [Source equality](../Signatures/Runtime/Caliper/BLSCallerExtractionSource.lean)
  connects the decoded execution to the original attacker machine under the
  original BLS service, followed by the source extractor. It uses local machine
  correspondence, the scalar sampling law and local extractor equality;
  `ImplementsWithin` excludes cutoff for the source comparison. The charged
  cutoff branch remains in the actual code.
  [Bounds](../Signatures/Runtime/Caliper/BLSCallerExtractionBounds.lean) add
  caller and terminal time/code costs. [Resources](../Signatures/Runtime/Caliper/BLSCallerExtractionResources.lean)
  bound every visited memory state, including stored instructions and initial
  data. Handler saved-buffer acceptance follows from the constructed code budget
  and primitive name bounds, rather than a supplied whole-handler acceptance
  assumption. [Regressions](../SignaturesTest/CaliperBLSCallerExtraction.lean)
  instantiate both actual `BLSExtractor` programs, with derived refinement,
  time/code/memory/name/operand bounds and a uniform sampler. Their executions
  cover hash/sign returns, adaptive random-to-hash calls, cache reuse, cutoffs,
  missing scalar/partial pair responses, exact traces and preserved caller data.
  This word-arithmetic fixture tests execution composition; it does not supply a
  curve implementation or field instance. The existing general field source
  theorems remain separate. Setup composition and complete solver source
  specialization are now implemented below; public security-model instantiation
  is still outstanding.

- [BLSFullProgram](../Signatures/Runtime/Caliper/BLSFullProgram.lean) constructs
  both complete BLS AGM programs: setup, generated adaptive caller, lazy query
  service, terminal handling and extraction. [Shared layouts](../Signatures/Runtime/Caliper/BLSFullLayout.lean)
  make the setup/service/extractor stores agree by construction. The parameters
  are named scalar/group routines and local caller initialization/continuation
  code; there is no supplied complete-solver implementation or budget contract.
  [Correctness](../Signatures/Runtime/Caliper/BLSFullCorrectness.lean) derives the
  initial extraction headroom from executed empty-store setup and composes all
  phases. [Source equivalence](../Signatures/Runtime/Caliper/BLSFullEquivalence.lean)
  identifies the erased executions with `goodReductionList` and `badReductionList`.
  It preserves the caller output, chronological transcript and private cache, and
  derives the bad-case setup law from the scalar sampler's uniform law.
  The caller still supplies local oracle-machine correspondence, bounded query
  termination, and erasure of its represented forgery to the algebraic output.
  These obligations do not yet prove coverage of every intended efficient attacker.
  [Budgets](../Signatures/Runtime/Caliper/BLSFullBudget.lean),
  [bounds](../Signatures/Runtime/Caliper/BLSFullBounds.lean),
  [operand acceptance](../Signatures/Runtime/Caliper/BLSFullAcceptance.lean), and
  [resources](../Signatures/Runtime/Caliper/BLSFullResources.lean) charge all phases,
  stored code, scratch descriptors, initial challenge data and every visited
  memory state. Width conditions are explicit arithmetic inequalities derived
  from component budgets. The ideal uniform sampling port remains explicit;
  it is not a fair-bit sampler implementation.
  [Full-program regressions](../SignaturesTest/CaliperBLSCallerExtraction.lean)
  instantiate actual scalar and group arithmetic routines, make the first caller
  query depend on the public key produced by setup, and check exact traces,
  output, cutoffs, missing randomness, preserved memory and proved time budgets.
  The bad program still samples setup at zero caller fuel. The fixture is word
  arithmetic, not a field or curve implementation. Other schemes, replay,
  parameter families and public security-model integration remain outstanding.

- [Within](../Signatures/Runtime/Caliper/Within.lean) defines a solver class over
  actual interactive Caliper code with a fixed oracle port and bounded input/output
  layouts. One program must implement the source at every represented input;
  correctness and resources hold for every local tape. Private sampling is through
  the port, so an arbitrary tape cannot supply uncharged advice. The class requires
  accepted operands, a stored-code limit, a time limit, and a total-memory limit at
  every visited state, including dense register/buffer descriptors and initial data.
  The resource witness is constructed from proved refinements and component bounds.
  Exact source semantics prevents a failing implementation from satisfying the
  resource premise vacuously. [Regressions](../SignaturesTest/CaliperWithin.lean)
  certify a zero-time identity with six charged words and prove that zero memory
  is impossible for its one-word input.
  [DLog](../Signatures/Runtime/Caliper/DLog.lean) fixes this class before taking the
  supremum over solvers, and requires every sampled challenge to be represented.
  [Challenge coverage](../Signatures/Runtime/Caliper/BLSFullChallenges.lean) derives
  that condition for BLS: the scalar sampler's full support covers every scalar,
  and implemented group/key scaling preserves the generator representations.
  [BLS certificates](../Signatures/Runtime/Caliper/BLSFullDLog.lean) construct both
  original reductions' witnesses from the assembled programs and exact source
  equality. [Concrete security](../Signatures/Runtime/Caliper/BLSFullSecurity.lean)
  then proves the two-reduction bound with a common derived code/memory/time budget,
  for both the lazy coefficient-view game and the shared direct AGM game.
  No finished-reduction efficiency or challenge-coverage contract is supplied.
  The old backend's unbounded encoding/category contracts are not used by this
  resource class. The ideal uniform port and separate flat-memory/CPU adequacy
  boundary are unchanged.
- [Public BLS AGM parameters](../Signatures/BLS/CaliperAGMParameters.lean) and
  [reduction certificates](../Signatures/BLS/Proofs/CaliperAGM.lean) now connect
  this execution model to `BLS.agm_security`. Layouts, actual primitive routines,
  sampler code/law and numeric caller allowances are fixed before the attacker.
  Each attacker supplies its own initialization/continuation code, local bounds,
  reachable-state invariants and source correspondence. Both original reductions'
  complete code/time/total-memory certificates are derived, without a supplied
  whole-reduction efficiency assumption. The public hardness supremum uses this
  Caliper class, and widening time preserves its fixed code and memory limits.
  The source game remains backend-independent and directly uses the shared AGM.
  The public theorem retains its curve, security parameter, query allowances and
  adversary arguments. Tests guard these dependencies and the theorem's axioms.
  The earlier `GeneralAGM` abstract-backend family results remain separate.
  Broader caller coverage, other schemes and replay remain unfinished.
- [Caliper families](../Signatures/Runtime/Caliper/Family.lean) fix the word-width,
  port and layout families before the solver. One polynomial per resource bounds
  word width, stored code, total memory and time across all security parameters;
  every pointwise witness is an actual `Interactive.Within` program. The
  [DLog family class](../Signatures/Runtime/Caliper/DLogFamily.lean) also requires
  every sampled challenge to be represented, and quantifies hardness over all
  such nonuniform solver families.
  [BLS component resources](../Signatures/BLS/CaliperAGMFamilyResources.lean) assume
  polynomial primitive/caller budgets, base encoding widths, storage capacities
  and name reservations. Complete good/bad time, code and memory bounds are
  derived from the existing numerical formulas, including setup and extraction.
  The actual original reductions then belong to the Caliper family class.
  Field/message cardinalities and the numerical random-query range are not
  required to be polynomial: their encodings and the actual code are charged.
  [Public asymptotic security](../Signatures/BLS/CaliperAGMFamilyStatement.lean),
  with a separate [proof](../Signatures/BLS/Proofs/CaliperAGMFamily.lean), concludes
  negligible forgery from nonuniform Caliper DLog hardness and negligible inverse
  group order. Tests audit the component premises, public proof dependencies and
  axioms; a real Word8 identity program instantiates the general family class.
  No uniform program generator, conventional-machine coverage, fair-bit sampler
  or CPU/flat-memory refinement follows from this theorem.

- [Caller presentation](../Signatures/Runtime/Caliper/CallerPresentation.lean)
  constructs an oracle machine directly from the caller's initialization and
  continuation functions. Its state is the existing returned/pending packet;
  the correspondence observes both the pending request and private state, so
  different requests may share the same private state. Local reply conversion
  proves the head correspondence. Branchwise query termination derives a finite
  source tree and its bounded implementation theorem, without a separately
  supplied machine or machine implementation certificate. The source tree is
  mathematical semantics; it is not enumerated by the emitted program.
  [BLS caller presentation](../Signatures/Runtime/Caliper/BLSCallerPresentation.lean)
  derives both reduction correspondences through this construction. Key layouts
  may represent a restricted subset of an infinite mathematical type: a
  represented fallback extends only the source initialization outside that
  domain, and termination is required only on represented keys. No executed
  validity test or fallback is added. `Parameters.callerCorrespondence` uses the
  already represented key generator and derives signature-point coverage from
  sampler full support, implemented scaling and generator surjectivity. No
  key-group surjectivity or new representation-completeness premise is assumed.
  Actual local Caliper code, resource bounds,
  reachable-state invariants and equality with the algebraic source remain
  explicit. This removes a presentation restriction; it does not prove general
  Caliper program coverage or conventional-machine adequacy.
- [Uniform sampling](../Signatures/Runtime/Caliper/UniformSampling.lean) writes
  a fixed range request, invokes the existing uniform word port and copies the
  returned index into a finite counter. A supported-output view proves the
  reply range matches the request, with unchanged encoded bytes and execution.
  [Resource bounds](../Signatures/Runtime/Caliper/UniformSamplingBounds.lean)
  certify at most 26 local steps, 125 stored-code words, three register/buffer
  slots and 166 total memory words. The numeric range may fill the whole word
  domain. This remains the ideal uniform oracle, not a fair-bit sampler.
  [Coron sampling](../Signatures/Runtime/Caliper/CoronSampling.lean) constructs
  the independent scalar/coin draw needed on a fresh co-CDH cache entry. For
  scalar encoding width `s`, it takes at most `scalarTime + 20*s + 42` steps and
  stores at most `scalarWords + 65*s + 235` code words; names are bounded by
  `max 4 scalarSlots`. Its complete memory certificate and product-uniform law
  are derived from the scalar component. Tests execute zero, intermediate and
  full-word ranges, plus the composed pair with both query traces and preserved
  private state.
- [Coron's paired cache](../Signatures/Runtime/Caliper/CoronCache.lean) combines
  the scalar/coin sampler with the existing executed cache. It derives exact
  private-oracle semantics and time, code, name, description and total-memory
  bounds from the scalar sampler. The initial encoded table, retained miss
  frames and insertion copies are charged; full tables remain valid for hits.
  Its storage bound includes one extra coin word per entry. Execution tests
  cover empty and partial misses, full-table hits without sampling, shadowed
  entries, missing coin input, query order and preserved private state.
  [The paired source bridge](../Signatures/Runtime/CoronPairedCache.lean) proves
  exact oracle-computation equality with the existing two-cache Coron oracle
  and reduction. It preserves both projected caches and the signing set for
  every adaptive caller, including the final verification hash and extraction.
  Cache and reply-log lengths grow by at most the query count. The source view
  does not enumerate the message domain or execute its function-valued caches.
  The constructed service below retains both explicit reply logs and charges
  them in its complete resource bounds.
  Executed final handling, the complete controller,
  public Caliper security theorem and its polynomial family remain unfinished.
- [Coron response code](../Signatures/Runtime/Caliper/CoronResponse.lean) now
  constructs the hash and signing arithmetic from implemented group scaling and
  addition. Its input contains the scalar/coin entry and all three challenge
  points. The finite coin zero test executes five instructions; branch selection,
  argument copies, retained frames and the encoded zero constant are also actual
  code. Zero-point representability follows from the scalar sampler's full
  support, implemented scaling and an already represented point, so no separate
  zero-coverage contract is needed at integration.
  For encoded input width `W`, [derived bounds](../Signatures/Runtime/Caliper/CoronResponseBounds.lean)
  are `scaleTime + addTime + 388*W + 48` hash steps and
  `scaleTime + 260*W + 48` signing steps. Stored code is at most
  `scaleWords + addWords + 1287*W + 768` for hashing and
  `scaleWords + 871*W + 599` for signing. [Name and buffer bounds](../Signatures/Runtime/Caliper/CoronResponseNames.lean)
  and [complete memory bounds](../Signatures/Runtime/Caliper/CoronResponseMemory.lean)
  retain the primitive reservations and charge initial capacities, code and every
  intermediate copy. Source output agrees with the paired Coron oracle. Tests
  execute both branches with distinct challenge points, zero scalars and maximal
  full-word coins, checking real elapsed time and preserved private state.
- [Coron's complete caller service](../Signatures/Runtime/Caliper/CoronService.lean)
  joins the constructed scalar/coin sampler, persistent paired cache, hash/sign
  responses and both reply logs. Random, hash and signing requests use the
  existing caller packet interface; request preparation, reply conversion,
  stored tags, retained frames and all copies execute actual instructions.
  Its [layouts](../Signatures/Runtime/Caliper/CoronServiceLayout.lean) share the
  scalar/coin representation and store all three challenge points. Supplied
  implementations are scalar sampling and group scaling/addition; the complete
  handler and its costs are constructed from them.
  [Resource proofs](../Signatures/Runtime/Caliper/CoronServiceBounds.lean) derive
  time, code, name and description bounds, plus a `Within` witness that charges
  code, initial data, descriptors and buffers at every instruction boundary.
  [Source correspondence](../Signatures/Runtime/Caliper/CoronServiceSource.lean)
  preserves the dependent random reply, challenge points, both native caches
  and signing set. This native projection is only a proof view; the executed
  service keeps and pays for its paired cache and both logs. A reserved query
  slot makes every represented request ready, and each reply preserves the
  remaining reservation. Whole-service tests execute fresh hashing/signing,
  hash-then-sign cache hits for both coin branches, random forwarding with full
  logs, incomplete randomness and private-frame preservation. They instantiate
  the complete resource certificate and audit its axioms. These tests use small
  word arithmetic, not a curve implementation.
  Complete co-CDH setup, caller/controller, final hashing and extraction, followed
  by its public concrete and polynomial-family statements, remain to be joined.

Remaining integration sequence:

The caller completion bound is now proved in
[BLSCallerPostcondition](../Signatures/Runtime/Caliper/BLSCallerPostcondition.lean).
Every supported exit preserves the configuration and adds at most `q` cache
entries and `q` transcript tokens after at most `q` calls, including early return
and fuel cutoff. [BLSCallerExecution](../Signatures/Runtime/Caliper/BLSCallerExecution.lean)
transfers this postcondition to the actual returned bytes and execution.
From an empty store, cache capacity `2*q + 1` leaves room for one private read
per transcript token plus the final message. Transcript capacity stays at `q`;
no extraction reservation is imposed on the logs. The asymmetric-capacity
regression uses five cache entries and two transcript slots and rejects a
five-slot joint reservation. This is the capacity precondition for the
complete extractor implementation above. The service bridge transfers it to
the terminal branch. `BLSCallerExtraction` now composes the generated caller
execution and terminal handler. `BLSFull` now joins setup and specializes
the source/output conversion for both complete BLS AGM reductions.

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
   bounds have polynomial-family proofs for BLS AGM; the other schemes still
   need their corresponding proofs.
3. Link the proved word oracle adapter and replay primitives into complete signature
   callers and rewinding. Ordinary saved-state query composition, generated
   caller steps and decreasing-domain loop composition are proved.
   Prove private finite-domain sampling agrees with the chosen randomness
   interface; oracle packet transport alone does not supply this distribution proof.
   The original-machine bridge is now instantiated with the constructed BLS handler,
   carrying reservations through the generated controller. The caller and terminal
   execution now compose with derived extraction room and complete resource bounds.
   Both BLS AGM setups and source/output conversions are now joined in `BLSFull`.
   Repeat the full construction for the other signature reductions. The complete
   extractors and terminal branches above execute chronological coefficient-row
   preparation/evaluation, the retained outer frames, numerator addition and
   final lookup/arithmetic. The service bridge connects the caller's proved
   `2*q + 1` cache headroom to the terminal success branch's extraction reservation. Caller state and
   private store are already framed across their respective callees.
   For rewinding, either copy all saved registers,
   buffer contents and capacities, or prove restart-from-initial-state replay with
   charged reinitialization. Caliper has no capacity-read instruction, so arbitrary
   dynamic capacities require explicit saved allocator metadata; copying filled
   contents alone does not restore them. Equality of runs from the same mathematical
   state is not a charged snapshot/restore implementation.
4. Supply the curve-specific routine library, or retain its named implementation
   contracts as explicit assumptions. Pairing/verification routines, if executed
   by the target program, also need implementations; they are not free consequences
   of the field/G₁/G₂ interface.
5. Migrate the remaining signature security models after the concrete BLS AGM
   wrapper and its polynomial-family theorem. Establish the other schemes'
   parameter-indexed bounds using polynomial word widths and routine bounds.
   Prove coverage for the intended Caliper adversary class. A claim about every
   conventional efficient attacker needs a further machine-adequacy result.

The existing backend's exact execution equations and unbounded mathematical data
types require a proved refinement. A fixed-word implementation must justify its
representable ranges along executions; attaching a cost table alone is insufficient.
Pure Caliper instruction counts require the cryptographic routine contracts to be
discharged. Machine-to-CPU adequacy remains a separate refinement.

Use one Lean compiler process at a time. Check operational examples, invalid
encoding/bounds cases, resource composition and theorem axiom footprints.
