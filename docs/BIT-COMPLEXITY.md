# Bit-Level Implementation Status

The scalar primitives and deterministic Schnorr scalar extractor have verified
Boolean-circuit implementations for `ZMod p`, where `p` is prime and `p > 2`.
Natural-number operations have range-checked word implementations. A separate
bounded rejection sampler has a fair-bit distribution proof. The complete
Schnorr extractor now has a compiled bit-cell implementation and pathwise cost
bound, including input/data loading and both replay passes. The public
[bit-machine security theorem](../Signatures/Schnorr/BitStatement.lean) includes
the accumulated rejection error, with no ideal-sampling assumption for the solver.

## What Is Proved

[PrimeFieldCircuit](../Proofs/Runtime/PrimeFieldCircuit.lean) builds a circuit
for `(z - z') / (c - c')`, using the standard library's verified bit-vector
circuits. It uses modular subtraction, schoolbook multiplication, remainder,
and square-and-multiply inversion with public exponent `p - 2`.

`extract_correct` proves that the output bits encode exactly that field value.
`extract_size` bounds the additional AIG declarations by

```text
102*w^3 + 137*w^2 + 93*w
```

Both theorems refer to the same generated circuit. The width requirement is
`p*p <= 2^w`, preventing overflow before modular reduction. `standard_width`
proves that `w = 2 * p.size` suffices; `p.size` is the binary bit length, not `p`.
The resulting circuit size is therefore cubic in the modulus bit length.

Zero denominators produce zero, matching Lean's total field division. As before,
extracting the secret requires two accepting transcripts with the same commitment
and distinct challenges; those checks are not part of this scalar circuit.

[BitCircuit](../Proofs/Runtime/BitCircuit.lean) proves bounds on the actual
standard-library circuit builders, not assumed prices for abstract operations:

| Word Operation | Additional Declarations |
| --- | ---: |
| Addition | `12*w` |
| Subtraction | `24*w` |
| Multiplication | `15*w*w` |
| Remainder | `36*w*w + 7*w` |
| Unsigned comparison | `6*w` |
| Equality | `4*w` |

AIGs use Boolean AND gates and complemented wires. These are circuit-size
bounds, not timings of Lean's circuit generator or its recursive evaluator.
The existing input circuit is excluded from the additional-gate count. Building
or reading input encodings, allocation, addressing, and host execution time are
not covered by these theorems.

## Operation Coverage

[PrimeFieldOps](../Proofs/Runtime/PrimeFieldOps.lean) adds constants, addition,
negation, and equality to the subtraction, multiplication, and division above.
[WordCircuit](../Proofs/Runtime/WordCircuit.lean) handles natural and bounded
integers. All size bounds count additional AIG declarations.

| Primitive | Bound | Semantic Restriction |
| --- | ---: | --- |
| Field zero/one | `0` | Canonical prime-field encoding |
| Field addition | `36*w*w + 19*w` | `p*p <= 2^w` |
| Field negation | `36*w*w + 43*w` | `p*p <= 2^w` |
| Field equality | `4*w` | `p <= 2^w` |
| Natural addition | `12*w` | The sum must fit; overflow is not ignored |
| Natural subtraction | `33*w` | Inputs fit; underflow saturates at zero |
| Natural equality/comparison | `4*w` / `6*w` | Inputs fit |
| `Fin (n+1)` conversion | `36*w*w + 7*w` | Input fits; no restriction on the modulus |
| `Fin` zero/value | `0` | Value fits; identity wiring |
| Encoded key/message equality | `4*w` | A supplied injective fixed-width encoding |

When `n+1 >= 2^w`, `Fin` conversion is identity wiring, including the zero-width
singleton case. Key/message equality does not invent a codec for arbitrary
types or charge the work of constructing their encodings.

The instruction dispatcher described below connects these implementations
to every `CryptoOp` constructor. The heap, expression, and program compiler
proofs below compose them through closed-machine execution and Schnorr security.

## Instruction Compiler

[CryptoCircuit](../Proofs/Runtime/CryptoCircuit.lean) lowers all 27 existing
`CryptoOp` constructors to actual circuits, including both group types, and
proves their gate bounds. It uses one conservative common word width `w`.
The scalar prime `r` and the two curve-coordinate primes `p1`, `p2` may differ.
Correctness requires each prime to exceed two and each squared modulus to fit
in the word. Group values belong to chosen curve subgroups with `ZMod r` actions.

[CryptoCircuitCorrectness](../Proofs/Runtime/CryptoCircuitCorrectness.lean)
proves agreement with `arithmetic.execute`, not a separate arithmetic semantics.
Keys/messages require explicit injective codecs. Natural and `Fin` input ports
include range evidence, so equality and conversion cannot silently compare
truncated values. Natural addition additionally requires its sum to fit.
`safe_of_expr_budget` derives that obligation from the local range theorem below.

[CryptoCircuitExecution](../Proofs/Runtime/CryptoCircuitExecution.lean)
connects the same compiled instruction to the costed circuit evaluator.
`execute_correct` identifies its output bits with the arithmetic result;
`execute_steps` bounds that very execution. In the evaluator bound below, use
`N = input graph declarations + gates(w, op)` and the instruction's output width
(`w`, `3*w`, or one bit).

[PrimitiveCode](../Proofs/Runtime/PrimitiveCode.lean) removes the need to
supply a pre-existing input graph. `precompile` takes only public word width,
moduli, curves, and opcode, never secret input values. It produces a finite
`CircuitExecution.Code`; its runner consumes only that code and runtime bits.
`precompile_correct`, `precompile_steps`, and `precompile_cells` concern this
same code. Output length is fixed even for malformed input bits; semantic
correctness additionally requires the stated operand representation and ranges.

[InputCircuit](../Proofs/Runtime/InputCircuit.lean) creates one fresh atom
per input bit. [FixedPorts](../Proofs/Runtime/FixedPorts.lean) wires these
atoms into typed operands and proves their representation. There are `m <= 6*w`
input bits and exactly `1+m` initial declarations. Thus the online bound uses
`N = 1+m+gates(w, op)`. The static executable-code size, including unary
addresses and list spines, is at most

```text
N*(2*N + m + 4) + outputWidth(w, op)*(N + 2) + 2
```

These layouts exclude lists. The semantic `Layout.encode` specifies already
supplied operand bits; it is not an uncharged online conversion of abstract
group values. Uniform compiler time is not included. Heap-to-operand loading
is covered separately by the shared-heap backend below.

[CircuitWires](../Proofs/Runtime/CircuitWires.lean) describes typed compiler
ports and proves prefix preservation through the representation theorem. Its
products/lists are compiler metadata, not a runtime allocation scheme. Port-bit
concatenation is not a serialization of arbitrary variable-length values.

## Shared Heap

[HeapBits](../Proofs/Runtime/HeapBits.lean) gives heap nodes a self-delimiting
bit encoding with distinct word, pair, empty-list, and list-cons tags. Words
carry a unary length followed by payload bits; pair/cons nodes carry two
unary node indices. The executable encoder and decoder have round-trip and
cell-cost proofs. Decoding a valid node preserves the following tape exactly.

[SharedHeap](../Proofs/Runtime/SharedHeap.lean) stores these nodes on one
bit tape. Reads decode the tape instead of assuming random access. Allocation
encodes the new node, copies the old tape, and copies the returned address;
all three traversals are charged. Old references remain valid. Pointers count
nodes, not byte positions: variable-size nodes with unary byte offsets could
otherwise cause exponential growth.

`WellFormed` requires backwards references and a leaf-payload bit cap `W`.
For `h` nodes, `tape_length` proves

```text
tape bits <= h*(2*W + 2*h + 4)
read steps <= 3*tapeBits + 7*(h+1)
allocation steps <= 2*tapeBits + 4*newNodeBits + 2*h + 8
```

[TypedHeap](../Proofs/Runtime/TypedHeap.lean) relates typed roots to source
values. Pairs/lists use links, so copying a reference does not duplicate its
mathematical value. Natural leaves include a no-truncation proof. Atom meanings
come from the primitive codecs. Allocation preserves existing representations,
and pair/cons construction preserves well-formedness. Tests allocate 100
repeated shared pairs in 101 nodes without expanding their `2^100` leaves.

[HeapPorts](../Proofs/Runtime/HeapPorts.lean) loads fixed primitive operands
by following these links, decoding leaf bits, and charging concatenation. Every
primitive needs at most three node reads. Its atom relation uses the existing
field/curve/key/message codecs and checks natural/Fin ranges.
[HeapPrimitive](../Proofs/Runtime/HeapPrimitive.lean) then executes the same
precompiled code and allocates its result. `runPrimitive_value` proves the exact
returned allocation; `primitive_result_represents` gives its source meaning.
`runPrimitive_steps` includes loading, execution, and allocation:

```text
3*(3*T + 7*(h+1) + 2*m + 5)
  + N*(4*N+m+10) + k*(N+4) + 3
  + 2*T + 4*(3+2*k) + 2*h + 10
```

Here `T` is the current tape length, `h` its node count, `m` the input width,
`N = 1+m+gates(w,op)`, and `k = outputWidth(w,op)`. Results are word nodes;
their lengths are at most `3*w+1`, preserving a common heap payload cap.

The tape-size theorem is about this explicit representation, not Lean VM
allocation or garbage collection. Source expressions are now compiled to it as
described below, including closed-machine effects, initialization, input/data
loading, and both replay passes. Sampling-error composition is proved below.

## Compiled Expressions

[HeapControl](../Proofs/Runtime/HeapControl.lean) stores register frames as
bit lists of unary node indices. Lookup parses them; extending a frame charges
copying both the new address and the existing frame. Projections and branch
selectors decode the heap, rejecting malformed nodes.

[HeapExpression](../Proofs/Runtime/HeapExpression.lean) compiles every
`Expr` constructor to first-order code: literals, variables, pairs, lists,
projections, binding, branches, primitives, and folds. It runs on frames and
heap tapes, not semantic field/group values or arbitrary host callbacks. Fold
fuel is a copied unary node counter. Backward references in well-formed heaps
prove this fuel suffices; malformed cyclic inputs terminate with failure.

[HeapExpressionCorrectness](../Proofs/Runtime/HeapExpressionCorrectness.lean)
proves matching source values, preservation of existing roots, and at most `B`
new nodes for a source expression taking `B` arithmetic steps. Variable reuse
preserves sharing, including for exponentially large unfolded values.

[HeapExpressionCost](../Proofs/Runtime/HeapExpressionCost.lean) proves the
actual compiled interpreter's step bound:

```text
bit steps <= B * budget(w, h+B, expression)
```

Here `h` is the initial node count. `budget` is computed from syntax using the
maximum of child budgets and explicit heap-scan, allocation, frame-copy, and
precompiled-primitive bounds. It covers either branch, but `B` counts only
executed branches and fold iterations. In particular, this is not a recursive
expansion of all possible values or a bound exponential in nested fold depth.
`compile_costed_of_budget` combines correctness and this cost bound, deriving
all intermediate Nat/Fin width conditions from the initial ranges and `B`.
Already-encoded inputs and their codecs are premises for this expression theorem.
The package theorem below also charges loading those representations into the
heap. Abstract-to-bit encoding is a representation boundary, not an online call.

## Program Controller

[HeapArguments](../Proofs/Runtime/HeapArguments.lean) compiles procedure
arguments, preserving their order and evaluating each in the original caller
frame. Its combined theorem proves the callee frame's meaning, heap growth,
and bit-step bound, including frame copies. Argument values share heap roots.

[HeapLoop](../Proofs/Runtime/HeapLoop.lean) implements counted loops using
a same-width binary predecessor and zero test. A tick costs exactly `2*w+1`
cell steps. It does not decode a natural number for online control: the binary
value is only a proof/termination measure. `run_erase` proves exact monadic
effect preservation, and `run_costed` bounds every supported stateful path,
including early failure. For at most `C` steps per body and returned-address
length at most `H`, the bound for `n` iterations is
`n*(C+2*w+3)+2*w+2*H+3`.

[HeapLoopRefinement](../Proofs/Runtime/HeapLoopRefinement.lean) strengthens
this to a relation with the actual source `repeatRun`: implemented steps are
bounded by source steps times a multiplier, while matching queries and replies
exactly. Its invariant is indexed by remaining iterations, so heap growth need
only be safe for the iterations that are actually executed. The body refinement
and its cost bound are explicit premises to discharge for compiled programs.
[QueryTreeRel](../Proofs/Runtime/QueryTreeRel.lean) supplies this structural
relation, composition, support transport, and equality of agreeing observations;
it requires no probability distribution or semantic decoder.

[HeapProgram](../Proofs/Runtime/HeapProgram.lean) now supplies executable
code and compilation for all program constructors, including adaptive queries,
binding, branches, counted loops, and calls. Query handlers receive heap roots.
[HeapProgramCorrectness](../Proofs/Runtime/HeapProgramCorrectness.lean)
proves structural refinement for every constructor: matching queries/replies,
typed successful results, preserved state relation and old roots, and no more
new heap nodes than matched source steps. `compile_refines_of_budget` derives
all intermediate and reply width checks from the source budget and actual
handler growth. The handler-refinement premise only applies when replies fit,
so unused, oversized requests need not have fixed-width implementations.
Tests include concrete theorem applications for a counted loop and a real
oracle-reply-dependent branch, as well as execution comparisons.

[HeapProgramCost](../Proofs/Runtime/HeapProgramCost.lean) proves the aggregate
bit-step bound for that executable compiler, alongside the same semantic and
allocation refinement. Its syntax-computed multiplier takes the maximum of
expression and argument costs, child-program costs, handler fees, and explicit
frame/read/loop overheads. For source budget `B`, initial heap node count `h`,
and word width `w`, `compile_costed_of_budget` proves on every path:

```text
compiled steps <= source steps * budget(w, h+B, handler fees, code)
               <= B * budget(w, h+B, handler fees, code)
```

The proof derives the heap bound after each adaptive prefix from its allocation
bound and residual source budget. It does not assume a uniform loop-body cost
or require an extra iteration after termination. Handler costs are still explicit
premises about their actual executions, not assumed equal to source prices.
Tests instantiate the theorem on a counted loop and a Boolean oracle that
allocates its reply, including both reply-dependent branches.

The concrete machine-effect and package instantiations are described next.
This generic program theorem starts from encoded inputs and precompiled code;
the package theorem adds loading. Neither theorem charges compiler execution.

## Closed Machine Effects

[HeapMachine](../Proofs/Runtime/HeapMachine.lean) implements all four
`Machine.Effect` constructors: scalar sampling, bounded-natural sampling, store
read, and store write. Its executable state is a heap root and a sticky failure
Boolean. Reads and writes copy addresses, not unfolded semantic values; samples
run fixed bit code and allocate typed word nodes. `compileBody` precompiles the
effect instructions, including samplers inside loops, using the proved
`HeapProgram.Code.mapQueries` translation. No sampler compiler runs online.

For heap limit `H`, let `A = allocBudget(3*w+1,H)` and
`P(n) = PaddedSampling.budget(n,w,k)`. The proved complete effect fees are:

| Effect | Bit-step fee |
| --- | ---: |
| Scalar sample | `P(r) + A + 3` |
| Uniform `Fin (n+1)` | `P(n+1) + A + 3` |
| Store read | `2*H + 2` |
| Store write | `2*H + A + 4` |

`handler_costed` proves typed results, heap extension, state/flag refinement,
and these bounds for every bit path, including exhausted samplers.
`compileBody_costed` discharges the generic compiler's handler obligations and
uses a total budget from the **original ideal-randomness machine**. The
[support-refinement proof](../Proofs/Runtime/SupportRefinement.lean) shows
that each marked fair-bit execution has the same source result and source step
count as an allowed ideal execution after dropping the flag. This transports
runtime bounds through arbitrary adaptive control flow; it is not probability
equivalence or a security proof.

The body theorem starts with represented input registers and initialized
storage. The following composition removes those heap/storage premises.

## Complete Packages

[HeapMachineCode](../Proofs/Runtime/HeapMachineCode.lean) compiles and charges
the initialization expression before the body, using the original ideal-machine
budget to bound both. [HeapData](../Proofs/Runtime/HeapData.lean) loads encoded
data through the existing expression and argument-frame controllers. It handles
all value types, including nested lists and pairs, preserving old heap roots.
Natural and `Fin` leaves must fit the initial width; fixed field/group/key/message
encodings are the same as the primitive backend's. Encoding specifies the input
representation and prepares fixed constants offline. The online runner never
encodes or decodes abstract field/group values.

[HeapPackage](../Proofs/Runtime/HeapPackage.lean) starts from an empty heap,
loads the input and fixed data, copies the combined register frame, initializes
storage, and runs the body. `compilePackage_costed` proves typed result/heap
refinement, equality of the sticky failure flag, and the bound

```text
(inputLoad + B + 1) * packageFactor(w, r, retries, inputLoad+B, registers, code)
```

Here `B` is a bound on the original ideal `Machine.Package.run`, `inputLoad` is
the structural source load cost of the input, and `registers` counts input plus
fixed-data registers. The additional input term is necessary because the original
package budget assumes supplied input registers. `packageFactor` is the maximum
of the explicit loader/frame and code budgets, using one common heap envelope.
[HeapBudget](../Proofs/Runtime/HeapBudget.lean) proves their monotonicity.
Initial Nat/Fin leaves fitting `bits` and `bits+B <= w` discharge all executed
intermediate width checks. Code generation itself remains outside online cost.

[SchnorrBits](../Proofs/Runtime/SchnorrBits.lean) applies this to the actual
`forkPackage` built from a `SourceCertificate`. `bitCode_costed` gives
`(targetBudget + 4) * bitFactor`, including both source executions, caches,
replay, extraction, fallback, and loading. The challenge is one point register,
whose structural input load costs three units. `bitCode_error` connects the
actual returned scalar encoding to the named ideal DLog reduction: unmarked
mass is dominated by the ideal law, and marked probability is at most
`targetBudget * 2^(-retries)`. This is a distribution theorem, not support inclusion.

[HeapDLog](../Proofs/Runtime/HeapDLog.lean) defines the corresponding hardness
class over actual precompiled packages. `dlogWithin` bounds both static code/data
cells and online work on every fair-bit reply path, including input loading.
[HeapCodeSize](../Proofs/Runtime/HeapCodeSize.lean) counts all branches,
literal bits, circuit addresses, type/layout metadata, and sampler parameters.
An unexecuted lookup table therefore still consumes the static budget.
`dlogAdvantage` samples the external DLog challenge uniformly and observes the
returned heap root as a scalar encoding. The challenge interface needs only
the first curve subgroup and word width, not the second group or key/message
codecs. It uses exactly the circuit port's existing point encoding. This decoder
is the mathematical success test, not an uncharged operation inside the solver.
The [public bit endpoint](../Signatures/Schnorr/BitStatement.lean) proves

```text
delta * (delta/(qH+1) - 1/r) <= epsilon + B * 2^(-retries)
B = targetBudget
online hardness budget = (B+4) * bitFactor
static hardness budget = (cert.bitCode ...).cells
delta = Adv_EUF-CMA - qS*(qS+qH)/r
```

Subtractions truncate at zero. The theorem derives the concrete solver budget
and sampling error from the source certificate; neither is an extra assumed
bound on the finished reduction. The static budget is the exact footprint of the
compiled artifact, not an assumed size certificate or a polynomial bound in
source-program size. Cells count a fixed finite alphabet of tags and bits,
not physical bytes; natural metadata uses length-delimited binary encoding.

## Word Bounds

[NaturalRange](../Proofs/Runtime/NaturalRange.lean) follows Nat and Fin leaves
through the actual `Expr.run`, including nested pairs/lists, local bindings,
branches, and folds. Among primitives, only natural addition can increase their bit bound, by at
most one per operation. Fin reduction cannot enlarge its input even when its
modulus is large.

If initial natural leaves fit in `b` bits and an expression takes at most `B`
charged local steps, `b+B` bits suffice for every intermediate on that execution.
`expr_trace_bound` covers discarded results and every executed fold iteration,
not merely the final output. Unary literal-loading costs are accounted for.

[ProgramRange](../Proofs/Runtime/ProgramRange.lean) extends output and state
range growth through stateful `Program.run`: adaptive queries, binding,
branches, loops, and calls. `args_trace_bound` also checks all intermediates in
procedure arguments. `program_bound` requires a range-growth proof for each
actual supported handler reply and state transition, not an assumption that
arbitrary oracles return small values.

`effects_bound` discharges that obligation for the closed machine's store and
sampling effects provided `n < 2^(sampling.uniform n)`. An unconstrained abstract
sampling price does not imply this condition. `machine_bound` then bounds the
closed code's output, including initialization.
[ProgramTrace](../Proofs/Runtime/ProgramTrace.lean) now derives bounds on
every reached expression and oracle reply, including adaptive loops and calls.
It requires nonempty oracle reply types: otherwise an empty continuation could
make a terminal cost bound vacuous. Untaken branches need no range certificate.
This trace theorem feeds the full program compiler and complete replay package.
Field/group/key/message sizes remain explicit
codec obligations. In particular, `Ty.load` charges one arithmetic step for
an atomic `Fin` value regardless of its modulus: initial `Fin` widths cannot
be inferred from that loading cost alone.

## Circuit Execution

[CircuitExecution](../Proofs/Runtime/CircuitExecution.lean) lowers AIG
declarations to a small instruction list. Input and gate addresses become unary
lists. Its costed interpreter scans Boolean lists to read a bit, stores each
gate result once, and explicitly copies the result list when appending a new
bit. All output wires share that one execution. This avoids silently assuming
constant-cost random access or efficient recursive DAG evaluation.

For `N` declarations, `m` input bits, and `k` output bits, `evaluate_steps` proves

```text
cell-interpreter steps <= N*(4*N + m + 10) + k*(N + 4) + 3
final stored gate values = N bits
```

`evaluate_correct` proves equality with the AIG denotation used by all the
primitive-circuit correctness theorems. `lower` materializes the code and output
addresses once, and `lower_run` proves that `Code.run` agrees exactly with
`evaluate`. `lower_cells` separately bounds the complete static representation,
including unary addresses and list spines. The evaluator
is deliberately conservative and quadratic in `N`, not an optimized RAM engine.

This is an explicit bit-list cell-cost model, not a Lean VM timing theorem or
a Turing-machine translation. Circuit construction happens outside the counted
interpreter: its running time is not proved here. This evaluator is now the
primitive backend of the full typed source/replay machine, with shared-heap
operand loading, result allocation, and input/data loading charged separately.

## Elliptic-Curve Operations

[FieldProgram](../Proofs/Runtime/FieldProgram.lean) compiles straight-line
field expressions, explicit intermediate bindings, and equality selections to
the verified field circuits. Its correctness and gate-bound proofs cover the
same generated circuit. Both selection arms are built, so the gate bound does
not depend on secret branch outcomes.
[FieldCircuitVector](../Proofs/Runtime/FieldCircuitVector.lean) compiles
multiple outputs onto one graph and proves that earlier wires retain their values.

[EllipticCurveCode](../Proofs/Runtime/EllipticCurveCode.lean) expresses
mathlib's general affine Weierstrass formulas as that field code. Points are
encoded as `(finite flag, x, y)`, with `(0,0,0)` for infinity. The encoding is
proved injective. Correctness is relative to actual mathlib nonsingular points,
not arbitrary triples of field elements.

[EllipticCurveCircuit](../Proofs/Runtime/EllipticCurveCircuit.lean) builds
shared-output circuits and proves their agreement with the point group:

| Point Operation | Additional Declarations |
| --- | ---: |
| Zero | `0` |
| Negation | `159*w^2 + 143*w` |
| Addition | `4080*w^3 + 20897*w^2 + 12774*w` |
| Subtraction | `4080*w^3 + 21056*w^2 + 12917*w` |
| Equality | `25*w` |
| Scalar multiplication (a `v`-bit scalar) | `v*(8160*w^3 + 41794*w^2 + 25557*w)` |

The coordinate field is `ZMod p`, with `p > 2` prime and `p*p <= 2^w`.
Addition includes infinity, vertical lines, ordinary addition, and doubling.
The constants are conservative bounds for complete affine formulas, not an
optimized curve implementation.

[EllipticCurveScale](../Proofs/Runtime/EllipticCurveScale.lean) builds binary
double-and-add with an input-wire selector. Each scalar bit builds both the
doubling and addition, then selects the result; there is no host branch on a
secret scalar. The decoder includes leading zeros and the zero-width case.
`scale_correct` connects the same circuit to the `ZMod r` action on a chosen
curve subgroup. The scalar prime `r` and coordinate prime `p` may differ, as may
their word widths. The scalar encoding requires `r <= 2^v`.

The subgroup's module structure can be constructed from a proof that `r` kills
every subgroup element. No curve, prime-order generator, subgroup cardinality,
or discrete-log hardness assumption is silently selected by this implementation.

## Model Boundaries

- The bit endpoint restricts stored code/data as well as online execution.
  The separate arithmetic-machine endpoints bound online work only; their
  hardness assumptions do not restrict precompiled code size. They should not
  be read as conventional bounded-size circuit hardness without that restriction.
- A uniform compilation-time bound or a Lean VM/Turing-machine implementation
  theorem would be needed to claim either rather than the explicit bit-cell model.
- Concrete curve/generator facts, codecs, source certificates, and DLog hardness
  remain parameters. This is not an unconditional security or hardware-timing claim.

The bit theorem compiles the certified first-order adversary code inside the
reduction. It does not assign a bit budget to an arbitrary `OracleComp` adversary
or prove that every bit-machine adversary has such a source certificate.
The proof uses complete compilation/refinement, not substitution of scalar gate
counts for `PrimitiveCosts` in the arithmetic-machine theorem.

## Sampling Choice

[BitSampling.not_balanced_prime](../Proofs/Runtime/BitSampling.lean) proves
the counting obstruction: no total function of a fixed number of fair bits is
exactly uniform over an odd prime number of outputs. Equal-sized output fibers
would require that prime to divide a power of two. The theorem is about fixed
tapes; a formal padding translation from adaptive bounded samplers is not included.

[RejectionSampling](../Proofs/Runtime/RejectionSampling.lean) now implements
bounded rejection. `fairWord` draws independent fair bits and is proved uniform
on `Fin (2^w)`. `runTape` is an executable early-stopping interpreter, and
`runTape_distribution` connects it to that sampler. For `n <= 2^w` and `k` attempts:

```text
failure probability = (1 - n/2^w)^k
probability of each accepted value = (1 - failure probability)/n
bits consumed <= w*k
```

For `n > 0`, choosing `w = n.size` gives failure at most `2^(-k)`. Zero retries,
singleton outputs, zero-width words, and power-of-two ranges are covered.
That tape bound counts randomness consumption. The separate
[BitRejection](../Proofs/Runtime/BitRejection.lean) implementation now draws
individual Boolean oracle replies, constructs little-endian bit lists, compares
them against a precompiled limit, and retries with static unary fuel. Its online
code does not decode words to unbounded naturals. It charges word construction,
comparison, returned-word copying, and retry control. For `w`-bit words and at
most `k` attempts, on every possible reply path:

```text
fair-bit queries <= k*w
CPU cell steps <= k*(10*w+6)+1
```

[BitRejectionDistribution](../Proofs/Runtime/BitRejectionDistribution.lean)
proves that interpreting this actual oracle program with independent uniform
bits gives exactly the encoded rejection distribution above. This includes
aborts, early stopping, zero retries, and full-width moduli, which must not be
truncated to zero. Choosing `w = n.size` for positive `n` gives abort probability
at most `2^(-k)`. The CPU bound prices each primitive bit draw at one step;
precompilation, code loading, heap-result allocation, and width padding are not
included in this sampler-local bound.

For integration with a total typed machine, `executeDefault` returns an all-zero
word on exhaustion and a separate failure flag. Its value always fits the range
when `n > 0`, its flag has exactly the proved abort probability, and its cost is
at most `k*(10*w+6)+2*w+3`, with the same query bound. The fallback is not uniform:
the machine must preserve that flag and charge the bad event in the security
proof. Tests exhaust small tapes and compare values, consumed prefixes, costs,
and flags against `runTape`; the `n=5,w=3,k=3` case has 27 failures and 97 copies
of each accepted value among 512 tapes.

[PaddedSampling](../Proofs/Runtime/PaddedSampling.lean) now connects the
sampler to machine-width words. For range size `n` and machine width `w`, it
samples at `v = min(n.size,w)` and constructs/appends `w-v` high zero bits with
charged operations. Its complete cost is `k*(10*v+6)+2*v+2*w+8`; it preserves
the sampled value and failure flag and uses at most `k*v` bit queries. For
`0 < n <= 2^w`, its exact distribution is the rejection distribution at width
`v`, and the bad probability is at most `2^(-k)`. Full-width power-of-two ranges
work without either truncation or an unnecessary extra bit. The machine-effect
fees above additionally include allocation.

[MarkedProbability](../Proofs/Runtime/MarkedProbability.lean) proves an
adaptive, weighted-query composition bound: unmarked output mass is dominated
by the ideal law, and accumulated marked probability is at most `B * 2^(-k)`.
[MachineSampling](../Proofs/Runtime/MachineSampling.lean) derives the needed
query bound from the original machine/package execution budget `B`, without a
separate sampling-count assumption. Each request costs its primitive sampling
price plus the query instruction's one unit. The same budget, together with the
sampling-price width contract, bounds every reached uniform domain.
[HeapProbability](../Proofs/Runtime/HeapProbability.lean) proves the exact
per-effect distribution bridge to the existing padded fair-bit implementation.
`Program.run_mmap` lifts these equalities through complete programs and packages.
[MachineProbability](../Proofs/Runtime/MachineProbability.lean) proves that
the ideal tree law equals the original machine's probability law, using the
native measure theorem for `uniformSample`. `HeapProbability.package_error`
therefore compares the complete marked reference with the original ideal package.
Exact query-tree refinement then transfers the result to the compiled Schnorr
runner in `bitCode_error` and the public bit security theorem.

This is a new sampler with an explicit bad event, not an exact replacement for
the existing ideal sampler. Complete machine and two-pass implementation
integration and error propagation into the bit security inequality are proved.
The separate arithmetic-machine security theorem is unchanged.
Exact non-aborting sampling would instead require unbounded rejection retries
and expected-time or tail bounds.

## Checks

[BitComplexity](../SignaturesTest/BitComplexity.lean) executes generated circuits
on wraparound, zero-secret, zero-denominator, and two-modulus examples. It also
builds a nonconstant circuit, checks the bound, connects circuit correctness to
the existing arithmetic extractor, and checks the theorem axiom footprints.
[PrimitiveBits](../SignaturesTest/PrimitiveBits.lean) exhaustively checks all
4-bit input pairs on nonconstant arithmetic/comparison circuits and tests modular
field operations and `Fin` boundaries.
[RejectionSampling tests](../SignaturesTest/RejectionSampling.lean) enumerate all
512 three-word tapes for sampling five values: 27 failures and 97 copies of each
accepted value, with stopping counts checked separately. The new correctness,
size, and sampling theorems have checked axiom footprints.
[EllipticCurveBits](../SignaturesTest/EllipticCurveBits.lean) executes point
circuits against mathlib operations on infinity, equal, distinct, and inverse
points. It includes a point whose double is infinity and a general Weierstrass
curve with nonzero first and third coefficients. It also checks nonconstant
addition-circuit allocation against the bound, exercises field-code bindings and
both selection branches, and checks the new theorem axiom footprints.
[EllipticCurveScale tests](../SignaturesTest/EllipticCurveScale.lean) cover zero,
leading zeros, multiple scalar values, and a nonconstant secret-bit selector.
They instantiate the scalar-action theorem with scalar field `ZMod 3` and a
subgroup of a curve over `ZMod 5`, and check correctness/size axiom footprints.
[CircuitExecution tests](../SignaturesTest/CircuitExecution.lean) check shared
gates, both complement polarities, zero-input/output cases, memory size, static
code size, and execution bounds. A symbolic test transfers the existing wire
representation predicate to executable output bits. Its correctness and cost
theorems also pass axiom-footprint checks.
[CryptoCircuit tests](../SignaturesTest/CryptoCircuit.lean) execute every
instruction constructor, using scalar modulus three and coordinate moduli five
and seven. They cover both scalar multiplications, zero division, nonconstant
input ports, saturating subtraction, Fin range boundaries, and cell-step bounds.
[NaturalRange tests](../SignaturesTest/NaturalRange.lean) detect overflow in a
discarded sum and a later fold iteration, accept a sufficiently wide word, and
check that untaken branches do not enter the execution trace. Both suites guard
the new theorem axiom footprints.

[HeapMachine tests](../SignaturesTest/HeapMachine.lean) check all 1024 ten-bit
tapes for the sampling/store body and the initialized closed code, including
failure flags and consumed prefixes. They instantiate the complete package
theorem, check input/fixed-data frame order, and load nested list/pair/Nat/Fin
data into a nonempty heap without changing old roots. The package and Schnorr
bit endpoints have standard-axiom guards.
[HeapCodeSize tests](../SignaturesTest/HeapCodeSize.lean) check stored literals,
unary circuit addresses, sampler fuel, fixed data, and both program branches.
Growing a dead literal by 2000 bits leaves execution cost unchanged but adds
4000 syntax cells; the resource predicate rejects oversized packages regardless
of their time allowance. [StatementAssumptions](../SignaturesTest/StatementAssumptions.lean)
checks that the public hardness hypothesis uses the actual compiled package's
size, its derived online budget, and the accumulated error term.
