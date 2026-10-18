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
  restoration instructions execute and their profiles compose. The generated
  buffer name still needs a width check when accepting the complete program.
- [SourceCompilation](../Signatures/Runtime/Caliper/SourceCompilation.lean) and
  [SourceErasure](../Signatures/Runtime/Caliper/SourceErasure.lean): compilation
  certificates indexed by the existing `BackendProgram.Code`, with implementation
  and capacity obligations at primitive leaves. Correctness and erasure recover
  that original program's oracle computation. Covered constructors are local
  operations, queries, sequencing, branching, saved state and bounded loops.
  Input-counted iteration is not yet covered. A completed reduction's execution
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
  compiled subset. Only primitive leaves supply budgets, checked against their
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
  the stated machine-level storage convention; generated address acceptance and
  flat-memory/CPU refinement are separate obligations.
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

Remaining integration sequence:

1. Complete list access/update and refine the source's unbounded `Nat` and lists
   to bounded representations along reachable executions. Construction, tag
   dispatch, projection/length and saved-state composition are implemented.
   The bounded-source layout and loop refinement are implemented; the particular
   signature programs still need their reachable-state invariants and primitive
   refinements. A fixed-width representation cannot honestly supply all the old
   closure instances unchanged.
2. Finish compiling the existing quantitative reduction/control code through these layouts.
   The local category above does not yet instantiate `BackendAssembly.Backend`:
   that interface requires unrestricted product/sum closure, unbounded counters,
   external queries and exact cost equations. The new bounded local constructors
   do not imply those contracts unchanged. The interactive compiler now proves
   source refinement for local/query/sequence/branch/first/bounded-loop code.
   Uniform runtime/additional-buffer bounds now follow from actual primitive
   budgets. Remaining work includes input-counted iteration and complete
   generated-code/address acceptance. Complete machine-memory bounds include
   static storage and every intermediate buffer state. These finite-program
   bounds still need parameter-indexed polynomial bounds for each scheme.
3. Link the proved word oracle adapter and replay primitives into complete signature
   callers and rewinding. Ordinary saved-state query composition is proved.
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
