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

Remaining integration sequence:

1. Complete list access/update and refine the source's unbounded `Nat` and lists
   to bounded representations along reachable executions. Construction, tag
   dispatch, projection/length and saved-state composition are implemented.
   A fixed-width representation cannot honestly supply all the old closure
   instances unchanged.
2. Compile the existing quantitative reduction/control code through these layouts.
   The local category above does not yet instantiate `BackendAssembly.Backend`:
   that interface requires unrestricted product/sum closure, unbounded counters,
   external queries and exact cost equations. The new bounded local constructors
   do not imply those contracts unchanged. Prove the representation and cost
   refinement, including the different footprint of the unrolled loop compiler,
   rather than assuming an execution/cost equation for each finished reduction.
3. Link the mailbox and replay primitives into oracle suspension/resumption and
   rewinding. Prove separation of caller/controller storage and preservation of
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
