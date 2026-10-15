# Schnorr: Game, Rewinding, and Cost

The [public statement](../Signatures/Schnorr/Statement.lean) proves ordinary
programmable-ROM EUF-CMA security from fixed-generator DLog hardness within a
derived arithmetic-machine budget. It does not assume algebraicity.
The [bit-machine statement](../Signatures/Schnorr/BitStatement.lean) additionally
implements all online operations and includes bounded-rejection sampling loss.

## Game and Probability Bound

The [game](../Signatures/Schnorr/Spec/ROM.lean) uses VCVio's Schnorr definition.
The adversary receives `pk = x*g`, makes adaptive randomness, hash, and signing
queries, and returns `(m, R, z)`. Verification requires `z*g = R + H(m,R)*pk`;
the forged message must never have been signed. All source hash/signing queries
and final verification use the same lazy cache.

Write `delta = Adv_EUF-CMA - qS*(qS+qH)/|F|`, with subtraction truncated at zero.
The theorem concludes

```text
delta * (delta / (qH + 1) - 1/|F|) <= epsilon.
```

Here `epsilon` bounds every DLog solver in the general closed machine class at
the certified target budget. `qS` and `qH` bound signing and hash calls on every
reply path, for every public key. Repeated calls count again. The source-code
certificate separately bounds private-random calls, hash calls, signing calls,
and local work. Both sets of query bounds are premises; neither is inferred
from a bound on distinct messages. The extra hash slot covers the final forgery.

## What Rewinding Executes

1. Run the compiled adversary with simulated signatures: sample `c,z`, form
   `R = z*g - c*pk`, and program the managed cache if that point is absent.
2. Record private-random and live-hash replies. Append the final live hash query.
3. Verify the forgery and locate its challenge in the chronological live log.
4. Reset and re-execute the source from the beginning, replaying answers strictly
   before the selected challenge. Resample that challenge and the remaining suffix.
5. Require matching selections and commitments and different challenges. Extract
   `(z-z')/(c-c')`; on failed checks, return a fresh random scalar.

The simulator's managed programming cache and the live random-oracle cache are
distinct, matching the upstream reduction, not two source-game oracles.
Private scalar samplers may contain multiple primitive uniform queries. Their
expansion preserves the joint distribution of the two executions.

No continuation is copied for free. Both full executions, tape recording/replay,
linear cache and prefix scans, reset, verification, extraction, random fallback,
and fixed-data loading are charged. The bound is pathwise, not expected time.
Primitive arithmetic/sampling prices are explicit contracts, not bit costs.

[FixedTapeROM.security](../Signatures/Schnorr/Proofs/FixedTapeROM.lean) separately
proves the same Schnorr EUF-CMA probability inequality for a named reduction that
preserves the entire private tape, including draws after the changed challenge.
It requires an explicit finite list of private sampling families and an
all-reply-path bound on the simulated adversary's primitive randomness. It does
not enumerate all ranges below the largest sampler. The complete seed includes
the final verification query, while the
forking denominator remains `qH + 1`: seed capacity and candidate fork positions
are counted separately. [SeededReplay](../Signatures/Runtime/SeededReplay.lean)
proves that each successful seeded fork has the common-prefix structure needed
by special-soundness extraction; this is support inclusion, not equality of the
two replay distributions. [FixedTapeExtraction](../Signatures/Schnorr/Proofs/FixedTapeExtraction.lean)
composes extraction, averaging over keys, and the signing-simulation bound.
Its [regressions](../SignaturesTest/SchnorrFixedTape.lean) check private draws
after the fork, the final-query slot, and the axiom footprint.

[SchnorrSeededSecurity.security](../Signatures/Runtime/SchnorrSeededSecurity.lean)
now proves the same native EUF-CMA inequality for a source-derived fixed-tape
reduction. Its original `SourceCertificate` supplies both semantics and resources;
there is no separate seed-bound premise. The seed families come from the source
syntax, and the capacity is derived from its local-time and query budgets.
Private scalar sampling has a separate typed family, so a scalar sampler may
use multiple raw uniform queries. Expansion occurs after forming the typed
fork, and its output probabilities and extraction support are preserved.
The [coverage theorem](../Signatures/Runtime/SchnorrSeededFork.lean)
proves that neither run uses live private randomness. Sparse-family regressions
check that a large sampler arity does not allocate every smaller family.

[SchnorrSeededPass](../Signatures/Runtime/SchnorrSeededPass.lean) now compiles one
complete seeded pass, including the source adversary, signing simulation, cache
access and final verification query. Its erasure is exact equality with the
typed seeded computation used in the probability proof.
[SeedTapeDraw](../Signatures/Runtime/SeedTapeDraw.lean) charges the family scan,
decoding, literal tags and storage operations for each draw, including misses.
[SeedTapeReset](../Signatures/Runtime/SeedTapeReset.lean) implements and charges
the selected-family prefix truncation and replacement, preserving every other
family's entire tape. [Regressions](../SignaturesTest/SeedTape.lean) exercise
interleaved families, missing-family fallback, and private draws after a changed
hash in two compiled executions.

[SeedTapeGenerate](../Signatures/Runtime/SeedTapeGenerate.lean) implements seed
setup with primitive sampling loops, codecs and list concatenation. Its exact
erasure is VCVio's `generateSeed`, including repeated family entries and draw
order. Its budget includes capacity literals and every generated cell.
[SchnorrSeededPassBudget](../Signatures/Runtime/SchnorrSeededPassBudget.lean)
derives a complete pass budget from the original source budget, accounting for
shrinking tapes, growing caches, simulated signatures and final verification.

[SchnorrSeededMachine](../Signatures/Runtime/SchnorrSeededMachine.lean) now composes
setup, both passes, selection, reset, extraction and fallback into a complete
first-order controller. It preserves the original seed in a register, resets
only the selected hash family, and starts each pass with empty caches. An absent
seed entry proceeds to the second pass; only an existing equal answer triggers
the collision guard.
[SchnorrSeededMachineBudget](../Signatures/Runtime/SchnorrSeededMachineBudget.lean)
derives the entire package budget from the original source certificate,
including literal loading and fixed data. The second pass uses the proved bound
that a reset seed has at most one more cell than the original.
[SchnorrSeededMachineCorrectness](../Signatures/Runtime/SchnorrSeededMachineCorrectness.lean)
proves exact equality to `Seeded.reduction`, places the named source solver in
`Machine.Within`, and gives the arithmetic hardness endpoint `SeedTape.security`.

[SchnorrSeededBits](../Signatures/Runtime/SchnorrSeededBits.lean) compiles this
package to the existing bit backend, with online cost `(B+4)*seededBitFactor`
and sampling error at most `B*2^(-k)`, where `B` is the complete seeded package
budget. [SeededBitStatement](../Signatures/Schnorr/SeededBitStatement.lean) combines
those results with fixed-tape security and hardness against bit packages bounded
in runtime and stored code/data. Its width and codec premises are the same kind
as the contextual endpoint below. The query limit is now a charged code literal,
so it does not need a separate input-data width premise.

## Nonzero Signing Nonces

[NonzeroSecurity.security](../Signatures/Schnorr/Proofs/NonzeroSecurity.lean)
proves a separate native ROM theorem for uniformly nonzero signing nonces.
Secret keys and challenges still range over all of `F`, and verification is
unchanged, including for identity commitments in attempted forgeries.
With `delta = Adv_EUF-CMA - qS*(qS+qH)/(|F|-1)`, it proves

```text
delta * (delta / (qH + 1) - 1/|F|) <= Pr[nonzero-nonce dlogReduction succeeds].
```

Its simulator samples `c,z` uniformly from `F` and a fresh `a` uniformly from
`Fˣ`. If `R = z*g-c*pk` is zero, it returns `(a*g,c,z+a)`; otherwise it returns
`(R,c,z)`. This finite sampler has exactly the honest transcript distribution.
[NonzeroSampling](../Signatures/Schnorr/Proofs/NonzeroSampling.lean) proves the
repair law with an explicit finite bijection. The resulting commitment
distribution is uniform on the nonidentity group elements, giving collision
bound `1/(|F|-1)`. The named reduction uses this simulator directly.
This theorem is a probability reduction; the full-field machine and bit
certificates above are not claimed for this variant.

## Adaptive Algebraic Group Model

[AGMSecurity.security](../Signatures/Schnorr/Proofs/AGMSecurity.lean) proves
security of the original adaptive [AGM game](../Signatures/Schnorr/Spec/AGM.lean)
with a named single-pass DLog solver:

```text
Pr[AGM game succeeds] <= Pr[AGM dlogReduction succeeds]
                        + (qH + 1)/|F| + qS*(qS + qH)/|F|.
```

The adversary explains each outgoing group element using its chronological
received inputs: the generator, public key, and signing commitments. Signing
and hash caps apply on every reply path and for every public key. The scalar
action on the generator is injective. No extra request-shape assumption is
needed: malformed requests set the source game's permanent failure flag.

[AGMReduction](../Signatures/Schnorr/Proofs/AGMReduction.lean) flattens these
explanations to affine representations and records each fresh hash point's
representation **before** drawing its challenge. Repeated hashes and colliding
signatures retain the first entry. Freshness rules out extraction from entries
created by signing. [AGMRunSound](../Signatures/Schnorr/Proofs/AGMRunSound.lean)
proves these invariants throughout adaptive execution and extraction on every
accepted path outside the bad event.

[AGMReductionProbability](../Signatures/Schnorr/Proofs/AGMReductionProbability.lean)
charges at most `1/|F|` for each adversarial hash and final verification query.
[AGMSigningSimulation](../Signatures/Schnorr/Proofs/AGMSigningSimulation.lean)
charges `qS*(qS+qH)/|F|` for signing collisions, using cache cardinality and
adaptive composition. [AGMSourceGame](../Signatures/Schnorr/Proofs/AGMSourceGame.lean)
proves exact equality of the honest instrumented and original game distributions,
including shared cache reads, signing history, malformed requests, and final
verification. The public theorem uses the native probability measure.

This AGM theorem certifies probability and single-pass extraction. The arithmetic
and bit-machine certificates for the ordinary ROM reduction are separate; they
are not runtime certificates for this AGM solver.

The [finite-list implementation](../Signatures/Runtime/SchnorrAGMExecution.lean)
now has exact joint output/state query-tree correspondence to that reduction,
including malformed requests and final extraction. Its cache stores only
encountered message/commitment pairs. Repeated hashes and colliding signatures
retain the first challenge and explanation. The [capacity proof](../Signatures/Runtime/SchnorrAGMGrowth.lean)
bounds the whole run by `qS + qH + 1` cache entries, `qS + 2` affine basis
entries, and `qS` signed messages. No finite message or group type is required.
The [probability endpoint](../Signatures/Runtime/SchnorrAGMSecurity.lean)
preserves both original loss terms. Its solver uses the supplied generator;
equality to the source's fixed-generator solver is proved for the complete DLog
experiment.

The [native cache core](../Signatures/Runtime/BackendSchnorrAGMCache.lean) now
implements the tuple/list encoding, message/commitment comparisons, first-hit
lookup, scalar sampling, entry insertion, and the exceptional-challenge flag.
The affine explanation is explicit runtime data retained before sampling. A
cache hit preserves the complete costed run when the sampler changes.
[Derived bounds](../Signatures/Runtime/BackendSchnorrAGMCacheBudget.lean) charge
the scans, sampling, field operations, compiler environments and stored code.
The [complete native read](../Signatures/Runtime/BackendSchnorrAGMRead.lean) also
constructs its default entry, retains the complete metadata, and restores the
updated cache and bad flag. Its output/state distribution equals the finite
source read. The [read budget](../Signatures/Runtime/BackendSchnorrAGMReadBudget.lean)
adds the actual setup, return and control costs. Separate bounds on the two
unchanged histories are preserved across reads; the cache grows by at most one
entry. Only primitive, scalar-sampler and representation contracts are assumed.
[Native representation flattening](../Signatures/Runtime/SchnorrAGMFlatten.lean)
now matches the source's chronological coefficient convention for every list,
including missing or extra coefficients. It uses the existing positional
coefficient matcher and computes the two affine coordinates with field products
and sums. Its [complete native cost](../Signatures/Runtime/BackendSchnorrAGMFlattenBudget.lean)
charges coefficient matching, both coordinates, temporary rows and retained
context; the full coefficient length appears even for an unused suffix.
Stored code is bounded independently of the basis/coefficient lengths, and the
output holds two field elements.

The [decoded hash path](../Signatures/Runtime/BackendSchnorrAGMHash.lean) now
composes flattening and the complete read, retaining the original state during
coefficient processing. Its [budget](../Signatures/Runtime/BackendSchnorrAGMHashBudget.lean)
adds the actual preparation and control costs to the proved flattening/read
bounds. It agrees with the finite source for every coefficient vector, preserves
both histories and the malformed flag, and keeps the first cached explanation.
Cache hits still charge coefficient processing but do not sample a challenge.
The [singleton decoder](../Signatures/Runtime/BackendListSingleton.lean) checks
list shape using two flags and one candidate, with a derived cost for scanning
the entire list and a constant stored-code bound. Duplicate elements do not
turn a multiple-element list into a singleton.

The [all-shape dispatcher](../Signatures/Runtime/BackendSchnorrAGMHashDispatch.lean)
now runs both scans and selects the decoded hash or rejection path. Rejection
returns zero and sets malformed while preserving the cache, both histories and
bad flag; replacing the sampler leaves the full costed rejection run unchanged.
The source correspondence covers arbitrary group and coefficient-row lists,
including repeated group elements and empty/multiple coefficient rows. Its
[derived budget](../Signatures/Runtime/BackendSchnorrAGMHashDispatchBudget.lean)
includes defaults, both scans, packing, selection, rejection construction and
all control transitions. Every coefficient row and all group elements contribute
to the input-size bound, even if the request is rejected. Its stored code is
independent of these runtime list lengths.

The [history append](../Signatures/Runtime/BackendListSnoc.lean) preserves the
chronological order of received representations and signed messages, with costs
for both list reversals, construction and retained inputs. The
[signing-cache programmer](../Signatures/Runtime/BackendSchnorrAGMProgramming.lean)
inserts a supplied challenge only on a miss, preserving the first cached
challenge and explanation even when the challenge is zero. It exactly matches
the cache component of `signedState` and has derived time/code bounds from the
implemented message/group comparisons and storage contracts. It performs no
sampling.

The [accepted signing core](../Signatures/Runtime/BackendSchnorrAGMSigning.lean)
now composes those components with both scalar draws and response arithmetic.
It exactly realizes the source's accepted signing branch, preserving cache
entries on collisions and appending both histories in order. Its
[derived budget](../Signatures/Runtime/BackendSchnorrAGMSigningBudget.lean)
charges the full internal path, including retained state, adapters and control.
The stored-code bound is independent of cache and history lengths.

The [signing dispatcher](../Signatures/Runtime/BackendSchnorrAGMSigningDispatch.lean)
accepts raw group and coefficient lists. A compiled emptiness scan selects the
accepted signing core or malformed rejection. Rejection sets only the malformed
flag, returns scalar zero with no group elements, and makes no scalar draws.
Acceptance constructs the scalar response and singleton commitment list. The
[complete budget](../Signatures/Runtime/BackendSchnorrAGMSigningDispatchBudget.lean)
charges the scan, retained input, routing and both reply constructors, and the
input-size bound includes every coefficient row even though signing ignores
their values. The tuple/list result has an exact correspondence to the source
reply. Its conversion to the caller's indexed request/reply interface remains
part of general-caller composition.

The [randomness handler](../Signatures/Runtime/BackendSchnorrAGMRandom.lean)
uses one [dynamic uniform query](../Signatures/Runtime/BackendUniformSampling.lean)
for every request, including malformed requests. Its arity is a runtime input;
there is no sampler table or loop over the randomness domain. Request/reply
conversions have implemented realizers with explicit cost and encoding contracts.
A compiled emptiness scan marks malformed state and preserves the cache and
both history capacities. The handler returns the sampled natural number and an
empty group list. Its [complete budget](../Signatures/Runtime/BackendSchnorrAGMRandomBudget.lean)
charges conversions, the external query and its control cost, scans, retained
data, state updates and reply construction. Ignored rows are included in input
size. Its exact source correspondence relates the natural-number result to the
source's dependent `Fin (n+1)` reply; caller-index tagging remains separate.

The hash dispatcher still uses an internal scalar/state interface. Final
extraction, full solver accounting and general-caller composition,
including external request/reply packing, remain open; these component certificates
are not yet a certificate for the full solver.

## What Efficiency Is Certified

The arithmetic extractor has the proved exact cost
`2 * cost.field + cost.division + 16`: two field subtractions, one division,
and expression/register overhead. The complete reduction additionally has a
proved budget for obtaining the two transcripts. Its public budget is
`forkPrice + load(adversary data) + qH + 9`; generator and register setup are
included in the constant, and `qH` is charged at its unary literal load cost.

This is an implementation-backed bound, not an assumed runtime for an abstract
extractor. However, it does not by itself prove polynomial time in a security
parameter. The bit backend described below supplies a separate execution bound
and an end-to-end probability comparison with the ideal reduction.
The deterministic scalar extractor now has a separate, verified cubic-size
Boolean circuit for odd prime fields; see [Bit-Level Implementation Status](BIT-COMPLEXITY.md).
Separate field/word circuits and a bounded fair-bit rejection sampler are also
verified, along with elliptic-curve point operations and secret-scalar
multiplication on curve subgroups. A separate costed bit-list circuit interpreter
agrees with these circuits' semantics and charges memory scans and output reads.
All `CryptoOp` instructions now have assignment-independent precompiled code
with correctness, code-size, and cell-cost proofs. Local expression budgets
imply bounds for every executed Nat/Fin intermediate. Program output/state range
proofs cover adaptive handlers; the closed machine's sampling effects need an
explicit result-width lower bound on sampling prices. A shared bit-tape heap
now implements primitive operand loading and result allocation with refinement
and cost bounds. Every source expression also compiles to a bit-tape controller,
with matching values, preserved sharing, and a bound on actual execution steps
including frame copies, branches, and list folds. Procedure argument compilation
and the binary counted-loop controller also have correctness and cost proofs.
The whole-program controller has exact query-tree, allocation, and aggregate
bit-step refinement under handler refinement/cost premises, with executed
expression/reply widths derived from source budgets. All four concrete
closed-machine handlers now instantiate this theorem for precompiled bodies,
using the original ideal-machine budget via support inclusion. Initialization
and input/fixed-data loading now compose into a complete package theorem.
`SourceCertificate.bitCode_costed` instantiates it on the actual two-pass
extractor, with bound `(targetBudget + 4) * bitFactor` in the explicit bit-cell
model. Encoded input is the representation boundary; compiler runtime is not
included. Sampling-abort propagation into the security bound is also proved.
The fair-bit rejection sampler itself now has an executable controller, CPU and
query bounds, and an exact distributional refinement. Its optional zero fallback
retains a failure flag, with padding and heap allocation charged. Adaptive
sampling-tree composition now proves accumulated error at most
`targetBudget * 2^(-k)`, with the query bound derived from the original runtime
certificate. Exact whole-package probability bridges connect this tree law to
the existing ideal game and compiled bit runner, including its scalar output encoding.

For the bit endpoint, the conclusion becomes

```text
delta * (delta/(qH+1) - 1/r) <= epsilon + targetBudget * 2^(-k).
```

Here `epsilon` is hardness against all bit-heap packages with online budget
`(targetBudget+4)*bitFactor` and stored code/data at most `(cert.bitCode ...).cells`.
The static count includes unexecuted branches and literal data, preventing an
unbounded lookup table from qualifying solely because it has short execution paths.
It is an exact artifact-size budget, not a proved polynomial compiler bound.
`k` is the maximum rejection attempts per draw.
The width premises include squared moduli fitting `w`, initial data fitting
`bits`, and `bits+targetBudget <= w`. Injective message/key codecs and the
generator's bijective scalar action remain explicit. The result is for the
precompiled bit-cell model, not Lean VM timing or compilation time.
The support refinement used for costs does not imply probability equivalence.
In particular, a uniform `Fin (n+1)` reply is recorded with
the natural tag `n+2`, and
[`uniformEncode_steps`](../Signatures/Runtime/MixedReplay.lean) charges
`n + cost.field + cost.natOp + 9`. That is linear in `n`, not `log n`.
Very large random-request ranges can therefore make the certified bound large,
even when sampling itself is cheap. Small-range requests avoid that issue.

The audit checked the source reply contract, shared-prefix randomness, cache
reset and final challenge, extraction guards, exact named-solver equality,
and loading/cost premises. No correctness defect was found in those checked
connections. This does not constitute an independent audit of every upstream
VCVio proof or a proof that chosen primitive prices match a concrete implementation.

## Proof Review Order

- [SourceCertificate](../Signatures/Runtime/SchnorrSource.lean): first-order source
  code, fixed data, equality to the original adversary at every key, and resource bounds.
- [SchnorrForkMachine](../Signatures/Runtime/SchnorrForkMachine.lean): the actual
  two-pass controller, selection, checks, extraction, and fallback.
- [SchnorrForkBudget](../Signatures/Runtime/SchnorrForkBudget.lean): `forkPrice` and
  the complete package bound derived from the source budget.
- [SchnorrForkCorrectness](../Signatures/Runtime/SchnorrForkCorrectness.lean): exact
  erasure to the primitive-boundary contextual fork.
- [SchnorrTrace](../Signatures/Runtime/SchnorrTrace.lean): equality to the native
  game trace and proof that the final challenge is present in the live cache.
- [SchnorrReduction](../Signatures/Runtime/SchnorrReduction.lean): exact equality
  to VCVio's `Schnorr.dlogReduction` and the resulting `Machine.Within` certificate.
- [Statement](../Signatures/Schnorr/Statement.lean): combine the probability lower
  bound and universal budget-bounded hardness upper bound.

## Tests

[SchnorrReduction](../SignaturesTest/SchnorrReduction.lean) checks a complete
zero-query source certificate through named-reduction equality and the machine
budget, plus an adaptive source that hashes a commitment returned by signing.
Its resource certificate covers every possible reply. The tests also reject
unexpected axioms in the full proof chain.
[SchnorrForkMachine](../SignaturesTest/SchnorrForkMachine.lean) checks fork guards
and controller costs. The other `SignaturesTest/Schnorr*` and replay modules cover
query caps, repeated hashes, extraction guards, replay, and sampler expansion.
[SchnorrSeededMachine](../SignaturesTest/SchnorrSeededMachine.lean) checks missing
versus colliding seed entries, selected-index guards, a complete package bound
from a zero-query source, and the axiom footprints through the seeded bit theorem.
