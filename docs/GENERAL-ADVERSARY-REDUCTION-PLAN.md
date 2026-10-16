# General adversary reduction plan

Updated 2026-10-16. All seven conditional general-attacker routes now have
proved complete solver resources, short public concrete statements and nonuniform
family security: BLS co-CDH, BLS/OOPS/Proximity AGM, Schnorr AGM, and Schnorr ROM
with either full-field or nonzero nonces. The source games and probability losses
are preserved; Proximity retains its collision qualification.

The shared framework derives caller invariants, composition costs, representation
bounds and full stored-code accounting from original measured resources. It does
not assume a completed reduction is efficient. The family theorems keep one
backend fixed across security parameters and derive polynomial solver resources.
Attackers need not use the arithmetic source language; AGM adds its algebraic-output
requirement. Conventional-machine adequacy remains a separate stronger claim.

The superseded eager-table AGM security wrappers and the BLS arithmetic-attacker
alias are retired. The [migration guide](API-MIGRATION.md) identifies the replacement
interfaces and their hardness scope. Original eager probability/resource lemmas
remain supporting references, and the retained arithmetic-source co-CDH and
Schnorr endpoints keep their distinct scopes.

The conditional reduction plan is complete: the final requirement audit and
current-tree integration verification passed all 1,054 targets (924 library
modules and 130 regression modules). This includes the sharper BLS cache bound
`qH + qS + 1` for both actual list-cache reductions. The detailed implementation
checkpoints below record the evidence and historical intermediate states;
the completion evidence map links every checklist item to its proof and tests.

## Existing results and limits

| Route | Existing result | Work needed for this plan |
| --- | --- | --- |
| BLS co-CDH ROM | Public general-caller concrete and nonuniform asymptotic security endpoints over arbitrary message types, with derived native runtime/code certificates and canonical encoding recovery. | A conventional-machine instantiation if claiming conventional PPT coverage; the conditional backend route is complete. |
| BLS AGM | Complete lazy native runtime/code certificates, resource-indexed DLog security, short public concrete statements, and a nonuniform asymptotic corollary with derived polynomial solver bounds. General realized callers, arbitrary messages, and the original probability loss are preserved. | Conventional-machine instantiation only if claiming that stronger model; the conditional backend route is complete. |
| OOPS AGM | Complete native certificates, concrete security, short public statements and nonuniform family security with derived polynomial resources. General realized callers, arbitrary topics and the original admissibility rule are preserved. | Conventional-machine instantiation only if claiming that stronger model; the conditional backend route is complete. |
| Proximity AGM | Complete native certificates, concrete security, short public statements and derived polynomial family resources. The original optional-coordinate/function-vector game has forgery bounded by collision probability plus negligible error; negligible forgery additionally assumes negligible collisions. | Conventional-machine instantiation only if claiming that stronger model; the conditional backend route, including its collision qualification, is complete. |
| Schnorr ROM | Complete native replaying solver with exact source correspondence, derived runtime/code certificate, short public concrete statement and nonuniform polynomial-family security. The original quadratic forking bound is retained; the public bound exposes its square-root consequence. General unrestricted callers and arbitrary messages are preserved. | Conventional-machine instantiation only if claiming that stronger model; the conditional full-field nonce route is complete. |
| Schnorr AGM | Complete native runtime/code certificates, short concrete security statement and derived polynomial-family corollary from general-caller resources, with exact source correspondence, arbitrary messages and the original probability losses. Actual setup, conversions, optional-return/cutoff handling and extraction are charged. | Conventional-machine instantiation only if claiming that stronger model; the conditional backend route is complete. |
| Schnorr nonzero-nonce ROM | Complete native replaying solver, derived runtime/code certificate, short public concrete statement and nonuniform family security. Both original samplers and both actual nonzero passes are charged. The signing denominator remains `|F|-1`; inverse nonzero-field growth follows from the original field-growth premise. | Conventional-machine instantiation only if claiming that stronger model; the conditional backend route is complete. |

The existing bounds are not absent or silently assumed. The pairing-based AGM
machine bounds explicitly charge full-domain initialization and sums. For BLS
their domain size is `|M|`; for OOPS it is `|T| * (d + 1)`; for Proximity it is
`|S| * (ell + 1)`. Such bounds can be exponential in encoding length. They can
also be useful when the relevant domain is polynomial-sized.

The source games already use lazy random oracles and their extraction proofs
already use the actual transcripts. The original reduction implementations
surround transcript computations with full-domain tables and loops. The new BLS
lazy solvers remove that enumeration; their complete conditional native runtime
certification is now proved. Distributional equivalence alone does not imply equal runtime.

The BLS AGM probability theorem is proved in Lean. On 2026-10-13,
`lake build Signatures.BLS.Proofs.LazyAGM` passed. Axiom checks for
`BLS.LazyAGM.Proofs.security`, `functional_euf_cma_adaptive`, and `baseCoeff_sum`
reported only `propext`, `Classical.choice`, and `Quot.sound`.

See the [computational-security status](COMPUTATIONAL-SECURITY.md),
[runtime certification](RUNTIME-CERTIFICATION.md), and
[Schnorr proofs and costs](SCHNORR.md) for the existing endpoints.

## Shared theorem and model

For each constructed solver, derive a bound of the following form:

```text
time(R[A]) <= c * T_A + H(lambda, T_A, query bounds, encoding/output sizes, scheme parameters)
```

Here `c` accounts for executing or simulating the attacker. A straight-line
solver executes it once; the Schnorr fork executes it at most twice. The exact
constant or simulation overhead must follow from the chosen execution model.
`H` includes initialization, handler work, communication, sampling, storage,
extraction, and replay where applicable. It may depend on `T_A`, for example to
bound private-randomness recording.

- Use a general costed oracle-machine interface for the attacker, with an actual
  execution/realization and all-path local-time, query, and output-size bounds.
  Bounds must hold under the simulator's permitted replies and public keys,
  including paths reached only in the second fork execution. Arbitrary Lean
  functions do not receive arbitrary asserted runtime labels.
- Keep the wrapper in the current abstract machine where possible. Its primitive
  contracts must specify behavior, encoding sizes, and implementation costs in
  the computational model used for the attacker and hardness assumption.
  Group encodings remain available to the attacker for arbitrary computation.
- Use a solver hardness class that includes the composed general attacker and
  wrapper. Hardness only against the old arithmetic-language class does not
  cover a solver containing arbitrary attacker code.
- Specify uniform parameterized machines, or explicit polynomial code/advice
  bounds for a nonuniform variant. Preserve the appropriate initial-data and
  code-size conventions; online time alone is not a code-size theorem.
- Prove caller/handler composition, including state invariants, reply-size
  conformance, and transfer/representation costs. Derive the completed solver's
  budget rather than assuming it as an extra premise.

The existing [composition theorem](../Signatures/Runtime/Composition.lean) and
[`SourceBudget.implemented_bound`](../Signatures/Runtime/SourceBudget.lean)
already add handler costs for arithmetic-language callers. Generalize that
argument to the broader caller interface. The pinned VCVio complexity interfaces
are useful starting points, but their handler-certificate API alone does not
supply a completed general resource-substitution theorem.

For every primitive, prove the number of calls and the sizes of its arguments,
then multiply by its contracted cost. All loops, memory scans, copying, random
sampling, and coefficient processing must be included. Polynomial query counts
alone do not bound arbitrary local computation or large intermediate values.

For concrete security, prove that the resulting solver budget fits the stated
hardness budget. For asymptotic security, supply polynomial resource and primitive
cost bounds in a parameterized family, and preserve non-negligible success after
the reduction losses. An explicit exponential bound is concrete but insufficient.
Primitive implementation contracts may remain explicit hypotheses; a full bit
backend or hardware-timing theorem is not a prerequisite for this conditional result.

## Public theorem interface

User requirement, 2026-10-14: make the public statements read as scheme/curve
parameters and a security parameter, a qualified adversary, query allowances,
the security game, and a probability bound. Generic machine type parameters,
identity encoding conversions, and compiler certificates belong in supporting
definitions and proofs, rather than the public theorem's argument list.

The intended shape is:

```text
parameters at security parameter lambda
an efficient adversary A (algebraic only for an AGM route)
query allowances and a proof that A respects them
---------------------------------------------------------
Pr[the scheme's security game accepts A] <= security bound
```

Bundle the attacker's actual execution, semantic correspondence, and resource
bounds in the adversary interface. Bundle primitive implementations, encoding
laws, and structural group assumptions in the scheme/backend setup. Keep every
obligation inspectable: such packaging must not introduce an assumption that a
finished reduction is efficient or silently restrict general attackers to the
arithmetic source language. Ordinary ROM routes permit unrestricted internal
attacker computation too; AGM adds its separate algebraic-output requirement.

Hardness must remain explicit in meaning. Either the bound contains the
appropriate resource-indexed DLog/co-CDH advantage function, or an explicitly
documented hardness hypothesis supplies its numerical bound. Query counts alone
do not bound arbitrary local computation. The bundled attacker resources must
therefore include the local-time, output/representation, and code/advice bounds
needed by the selected model. Use `<=` for the established non-strict bounds;
a strict inequality needs a corresponding strict hypothesis or slack.

Prioritize complete concrete solver bounds. Asymptotic corollaries are subsequent
packaging for parameterized families with polynomial resource/primitive bounds
and the required asymptotic hardness. They are not a prerequisite for the soundness
of the concrete theorem.

The former BLS source-machine AGM endpoint and its specialized
`ArithmeticAttackerCertificate` alias are retired. The public replacement is
[`BLS.agm_security`](../Signatures/BLS/Statement.lean), with four explicit inputs:
curve, security parameter, query allowances, and algebraic adversary. The
[`AGMSecurityModel`](../Signatures/BLS/GeneralSecurityModel.lean) fixes the backend and
resource class separately from the curve. Its
[detailed records](../Signatures/BLS/GeneralAGMParameters.lean)
keep backend contracts and actual attacker resources inspectable. The main RHS is
`2 * dlogSuccessBound(agmReductionTime) + 1/|F|`, using the maximum of the two
derived solver times. The sharper sum of the two separately budgeted terms is
`agm_security_two_budgets`. The DLog bound is the supremum over
all solvers within the fixed backend's code/input/time limits, not an assumed
advantage of the constructed reduction. Numerical hardness bounds are separate.
The same public interface is implemented for all seven routes, with OOPS's degree
and Proximity's dimension as additional explicit inputs. Supporting proof bodies
remain in separate files.

Earlier public-interface revision, 2026-10-14: the earlier `BLS.GeneralAGM.security P A`
bundling was still too opaque for the requested English description. The new
`BLS.agm_security` names the curve, security parameter, query allowances, and
algebraic adversary directly, and displays the named EUF-CMA game and the two
DLog terms plus inverse curve order. `Model.PairingCurve` contains only the
mathematical data. `BLS.AGMSecurityModel` separately fixes execution contracts and
resource limits, with checked equalities tying its configured generators and
query allowances to the public inputs. `AlgebraicAdversary.query_allowances`
proves all three allowances bound the actual source computation. The short
theorem is proved from the existing complete solver endpoint; no new reduction
efficiency premise or hardness assumption is introduced. Other signature routes
still require their concrete overhead work before receiving this interface.
Validation: public signature, axiom, resource-premise, and allowance/game checks
pass in `SignaturesTest.GeneralAGMStatement`. The full
`lake build Signatures SignaturesTest` passes (3952 jobs), log
`/private/tmp/agm-english-full-suite.log`. The public theorem has exactly four
explicit inputs and one declared `SecurityModel`; no independent field/group,
encoding, or cost parameters appear in its signature.

Earlier public-interface transparency revision, 2026-10-14: the short statement hid too
much behind names. At that stage, `Statement.lean` contained the execution/resource model,
attacker contract, actual EUF-CMA experiment, and an explicit DLog-success
supremum beside the theorem. `eufCmaGame_eq` proves exact equality to the original
lazy game. The RHS uses that one supremum at the visible `goodTime` and `badTime`
budgets; the old named bounds remain compatibility definitions in
`SecurityModel.lean`. The proof displays the probability inequality, the two
constructed resource witnesses (`GeneralAGM.reductions_within`), and the two
supremum inclusions. It no longer forwards the whole result to
`GeneralAGM.security`. The public model documentation identifies attacker
work/state/code limits and primitive/backend contracts, and distinguishes these
from DLog hardness and additional asymptotic/conventional-machine obligations.
Validation: `lake build Signatures SignaturesTest` passes (3988 jobs), log
`/private/tmp/agm-public-transparent-full.log`. The new game-equivalence,
resource-witness and supremum-correspondence checks pass with the existing
public argument, allowance, axiom, and forbidden-premise guards.

Earlier public-route and proof-file revision, 2026-10-14: `BLS.agm_security` and
`BLS.cocdh_security` now explicitly separate the AGM/DLog and unrestricted
co-CDH claims. The shared `ExecutionModel` contains the local computation and
message-type interface; each route has its own resource contracts and native
solver. `GeneralCoCDH.Adversary` returns a plain message/signature pair, with
no coefficient representation. `GeneralCoCDH.reduction_within` constructs its
native Coron executable and derives code/time bounds, including caller work,
query simulation, final hashing and extraction. The public co-CDH theorem uses
`coronFactor queries.sign * coCDHSuccessBound solverTime`.

At the user's request, the proof bodies moved to
[`BLS/Proofs/GeneralSecurity.lean`](../Signatures/BLS/Proofs/GeneralSecurity.lean).
[`Statement.lean`](../Signatures/BLS/Statement.lean) contains the two complete
statements with one-line references to those proofs.
[`GeneralSecurityModel.lean`](../Signatures/BLS/GeneralSecurityModel.lean) keeps
the model fields, attacker classes, expanded games and hardness suprema
inspectable. Exact game-equality lemmas preserve the original source experiments.
The old `security`/`SecurityModel` names remain AGM-only compatibility aliases;
they are not the canonical entry point for co-CDH. The public interface guards
cover both route signatures, query allowances, source-game equality, standard
axioms, and absence of finished-reduction or arithmetic-attacker premises.
Validation: `lake build Signatures SignaturesTest` passes (4002 jobs), log
`/private/tmp/agm-bls-routes-weighted-full.log`. The public signatures, expanded
games and their separate proof bodies all pass the standard-axiom checks.
The compatibility import also builds separately (3502 jobs), log
`/private/tmp/agm-bls-compatibility3.log`.

Public-statement simplification, 2026-10-14: the main `agm_security` now states
`Pr[forgery] <= 2 * DLogSuccess(agmReductionTime) + 1/groupOrder`.
`agmReductionTime` is exactly the maximum of the good and bad native solver
times. Monotonicity of the DLog success supremum is proved by enlarging only the
runtime allowance of the same executable; the backend, input cap and stored-code
cap stay fixed. `agm_security_two_budgets` preserves the sharper original bound,
and the compatibility name `BLS.security` retains that original type.
Both main public statements omit the internal resource-record binding; co-CDH
uses `cocdhReductionTime`, exactly the already-proved complete Coron runtime.
The games and hardness suprema remain explicit named terms in the inequalities,
and the separate proof file contains all new proofs. The original four public
inputs and route-specific model assumptions are preserved. Validation of the
statements and compatibility imports passes (3502 jobs), log
`/private/tmp/agm-simple-statement-api.log`. The full
`lake build Signatures SignaturesTest` passes (4013 jobs), log
`/private/tmp/agm-simple-statement-full.log`, including public argument,
game/hardness visibility, derived-budget and standard-axiom guards. The changed
Lean modules have no new warnings, admissions or proof-resource overrides.

## BLS AGM implementation

Retain the existing success inequality:

```text
Adv_BLS(A) <= Adv_DLog11(R_good[A]) + Adv_DLog11(R_bad[A]) + 1/|F|
```

Each solver runs the attacker once. They are separate reductions, not successive
attempts on one transcript. The target is the existing `(1,1)`-DLog challenge
`(g1, X1 = x*g1, g2, X2 = x*g2)`.

1. Implement a lazy private map in the good solver. On the first encounter with
   message `m`, sample and store `rho[m]`. Return `rho[m]*g1` for hashing and
   `rho[m]*X1` for signing, with public key `X2`.
2. Implement a lazy private map in the bad solver. Choose the known signing key
   `kappa`; on a new message store independent `a[m], b[m]`. Return
   `H(m) = a[m]*X1 + b[m]*g1` and `kappa*H(m)` for signatures, with public key
   `kappa*g2`.
3. Share each solver's cache across explicit hash requests, internal signing
   lookups, and final-forgery processing. Repeated requests reuse entries but
   retain their separate chronological reply tokens. Internal lookups add no
   attacker-visible representation tokens. Freeze the attacker's output before
   any new lookup for the final message.
4. Compute extraction from the actual transcript. For hash requests `h_j`,
   signing requests `s_j`, and coefficients `beta, gamma_j, xi_j`, the good guess
   is `(beta + sum_j gamma_j*rho[h_j]) / (rho[mstar] - sum_j xi_j*rho[s_j])`.
   The bad guess is `-(b[mstar] - sum_j xi_j*b[s_j]) /
   (a[mstar] - sum_j xi_j*a[s_j])`. Preserve the existing division-by-zero
   behavior; the probability proof handles successful extraction conditions.
5. Reuse existing algebraic identities. In particular,
   [`baseCoeff_sum`](../Signatures/LinearFunctional/Proofs/LazyAGM.lean) already
   equates the full-domain hash sum with the transcript sum. Prove any remaining
   scalar and signing specializations; preserve repeated queries and the current
   missing/extra coefficient semantics.
6. Prove lazy/eager correspondence for adaptive transcripts and extracted
   outputs, including the joint private randomness needed by the masked branch.
   Merely showing that individual oracle replies are uniform is insufficient.
7. Prove `K <= qH + qS + 1` for the number of stored messages. Derive explicit
   costs for lookups, sampling, arithmetic, and coefficient processing. List
   maps with polynomial, possibly quadratic, overhead are sufficient initially.
   No loop or package data may enumerate the complete message universe.

Audit finding resolved, 2026-10-16: the earlier BLS list-cache lemmas gave the
conservative `K <= 2*q + 1` bound from total queries. The new
[sharp BLS cache proof](../Signatures/BLS/Proofs/LazyAGMCacheBound.lean) connects
the weighted singleton specialization to the entire actual BLS good/bad query
computations. `goodList_cache_bound_by_kind` and `badList_cache_bound_by_kind`
prove `K <= qH + qS + 1` for every supported joint output/cache. Private random
requests and extraction rereads add no entries. The existing polynomial runtime
certificates remain valid with their conservative capacities. Regression cases
cover repeated requests, adaptive queries, and private randomness with zero
hash/sign allowances, on the infinite message type `Nat`.

Sparsity here is relative to the message universe. The attacker may use every
reply it received; no additional sparsity condition is imposed on its output.
The current security argument additionally uses freshness to prove a nonzero
target coefficient, via
[`fresh_coefficient`](../Signatures/BLS/Proofs/Nondegeneracy.lean). Sparsity alone
does not establish the extraction success bound.

The [eager mathematical definitions](../Signatures/Model/LazyAGM.lean) may remain
private proof helpers so the existing probability theorem can be reused. They
need not remain executable implementations or public efficiency endpoints.
Alternatively, prove security directly for the lazy reductions. Avoid deleting
existing certificates before their replacements and callers are validated.

The efficient implementation must not enumerate message indices. Exact transport
of the probability proof to arbitrary message types is now complete, using finite
execution covers only inside the proof. This discharges the former finite-domain
probability obligation. Both lazy native resource/composition certificates and
their polynomial-family corollary are proved and passed full integration
verification and the final audit.

## OOPS and Proximity extensions

Checkpoint, 2026-10-14: the shared
[`WeightedReduction` programs](../Signatures/LinearFunctional/Spec/LazyAGMReduction.lean)
now use separate index/message types and one persistent scalar/pair cache.
Signing evaluates each message's finite weighted base list. Extraction expands
only actual signing-reply occurrences, keeps repeated replies, zero-extends
missing coefficients, and ignores coefficients without a corresponding reply.
The [fixed-table identities](../Signatures/LinearFunctional/Proofs/LazyAGMReduction.lean)
and [joint coupling](../Signatures/LinearFunctional/Proofs/LazyAGMCoupling.lean)
prove both lazy solvers have the exact existing eager distributions; list-cache
refinement holds without any finite-domain premise. The probability replacements
are [`security_lazy_finite_topics`](../Signatures/OOPS/Proofs/LazyAGMSecurity.lean)
and [`security_lazy_finite_slots`](../Signatures/Proximity/Proofs/LazyAGMSecurity.lean).
They retain the existing OOPS admissibility predicate and Proximity's actual
fresh-collision experiment. These finite comparison helpers now support the
[arbitrary-topic OOPS theorem](../Signatures/OOPS/Proofs/LazyAGMArbitraryTopics.lean)
and [arbitrary-slot Proximity theorem](../Signatures/Proximity/Proofs/LazyAGMArbitrarySlots.lean).
The [finite-label presentation](../Signatures/LinearFunctional/Proofs/LazyAGMFiniteLabels.lean)
covers every query and final output along every reply path at generated keys.
Separate index/message [renaming maps](../Signatures/LinearFunctional/Proofs/LazyAGMTransport.lean)
preserve weighted term lists and both complete reductions. Exact
[source-game transport](../Signatures/LinearFunctional/Proofs/LazyAGMGameTransport.lean)
preserves OOPS's distinct-message condition and Proximity's actual collision event.
No finite topic, slot, or public-key premise remains on the new probability
endpoints. The potentially large finite cover is never constructed by the solvers.

The [cache invariants](../Signatures/LinearFunctional/Proofs/LazyAGMCache.lean)
prove all explicitly hashed bases and all bases used in signing are retained.
Evaluation of cached terms is exactly a pure computation, preserving the entire
cache and issuing no fresh draws. The
[complete program cache bounds](../Signatures/LinearFunctional/Proofs/LazyAGMCacheBound.lean)
therefore prove `K <= qH + (qS + 1) * L` for both branches, including an unseen
final target, with no finite index/message/public-key premise. OOPS and Proximity
have exact term-length lemmas `d + 1` and `ell + 1`.

The [term generators](../Signatures/Runtime/WeightedTerms.lean) now compute
OOPS powers incrementally and walk Proximity's fixed structural tuple, preserving
source order, constant terms, and zero-weight terms. Their compiled
[native implementations](../Signatures/Runtime/BackendWeightedTerms.lean) have
exact source terms as their semantic indices. Runtime bounds follow from
individual arithmetic/index primitives and structural costs; retained frames,
natural literals, list construction, and copying are included. Their actual
stored-code bounds charge primitive descriptions and static degree/dimension
unrolling. Generated lists occupy at most `(6 * L + 1) * width` under the
declared product/list encoding laws. The numerical degree/dimension is charged;
these are not bounds polynomial in the binary length of an unrestricted degree.
The Proximity input tuple itself has the derived bound `(2 * ell + 1) * width`
from coordinate and unit encodings; `proximityCode_cost_of_atoms` uses this bound
instead of assuming a dimension-independent vector width. The
[structured index comparisons](../Signatures/Runtime/BackendWeightedKeyEquality.lean)
also have native runtime and stored-code bounds, charging topic/slot equality,
both finite-tag reads, the natural comparison, and branch/encoding operations.

The [native private caches](../Signatures/Runtime/BackendWeightedCache.lean)
now implement both scalar and independent-scalar-pair branches for both index
encodings. The [comparison adapter](../Signatures/Runtime/BackendComparison.lean)
and [compiled comparison routines](../Signatures/Runtime/BackendWeightedComparison.lean)
feed the existing finite-list cache compiler; the internal call label is backed
by that actual code. There is no new assumed structured-comparison primitive.
The [generic cache law](../Signatures/Runtime/BackendStructuredCache.lean)
preserves the joint answer/cache/state distribution. Hits preserve even the
costed execution under sampler replacement, including cached zero and shadowed
entries. Proximity's source `Option (Fin ell)` keys are connected to native
`Fin (ell + 1)` tags by exact injective-encoding laws for both cache branches.
These encoding maps relate states in the proof and are not runtime table construction.

For `fee = overhead (32 * frameWidth width cap)` and
`compare = topicTime + 2 * indexTime + natTime`, the scalar access bound is
`cap * (compare + 391 * fee) + scalarTime + 133 * fee`.
The pair branch uses width `3 * width`, charges two scalar draws and twelve
additional structural fees. Actual stored-code bounds include both scalar
sampler occurrences, the full compiled comparison and its adapter, and all cache
control code. The final branch bounds require only the individual operation,
sampling, encoding and structural contracts; they accept no finished-cache or
finished-comparator budget. Neither bound depends on the topic/slot universe size.

The [native private reads](../Signatures/Runtime/BackendWeightedRead.lean) now
route `(index, cache)` to `(answer, updated cache)` with no transcript insertion.
The [generic adapter](../Signatures/Runtime/BackendCacheRead.lean) explicitly
constructs its fallback and packs cache arguments, invokes the cache and projects
the returned state. Its complete [runtime bounds](../Signatures/Runtime/BackendWeightedReadBudget.lean)
and [stored-code bounds](../Signatures/Runtime/BackendWeightedReadDescription.lean)
charge zero construction even on hits, all structural work, and two independent
scalar draws for the pair branch. Final read bounds are derived from individual
primitive, sampling, encoding and structural contracts.

The [weighted evaluator](../Signatures/Runtime/WeightedEvaluate.lean) computes
its term count, scans to each indexed term, reads the private cache and accumulates
the weighted scalar or pair value. Its [native implementation](../Signatures/Runtime/BackendWeightedEvaluate.lean)
has exact joint value/cache correspondence to the source `evalTerms` computation.
Repeated indices, zero coefficients, query order and an empty input's unused
default row are preserved. The complete evaluator's
[stored-code bounds](../Signatures/Runtime/BackendWeightedEvaluateDescription.lean)
charge the read implementation, sampling, comparison, arithmetic and loop body.
Complete [scalar runtime](../Signatures/Runtime/BackendWeightedGoodEvaluate.lean)
and [pair runtime](../Signatures/Runtime/BackendWeightedBadEvaluate.lean) bounds
now compose the actual indexed scans, private reads, arithmetic, count/init/loop
code and evolving cache. Encoded result/cache widths are proved on every supported
run. The maximum cache length is `initialCacheCap + rowCap`, with no topic/slot
universe-size term. Both bounds are derived from individual primitive, sampler,
encoding and control contracts; no completed-reader or evaluator budget is supplied.

`SignaturesTest.WeightedEvaluate` checks ordered evaluation including zero-weight
and repeated terms, both scalar/pair accumulation, empty inputs, actual compiled
read/evaluator semantics, shadowed cache preservation, and sampler-independent
costed hits. Its guards reject finite topic/slot domains and supplied completed
component budgets, and check transitive standard axioms. The complete evaluator
runtime results have the same guards; body invariants, row-selection/count costs
and reader bounds must be derived, not supplied. Targeted runtime and regression
builds pass. The full `lake build Signatures SignaturesTest` passes (4002 jobs),
log `/private/tmp/agm-bls-routes-weighted-full.log`; the new evaluator modules
have no warnings, admissions, additional axioms or proof-resource overrides.

Complete runtime accounting for weighted hash/sign dispatch, extraction, and
general-caller solvers remains open. Expansion's complete native resource
results are recorded below. The prior
eager machine certificates describe their original implementations and are retained.

For `N = rowCap`, `C = initialCacheCap + N`, let
`E(w,N,C) = (4*N + 8*C + 64)*w`. In the scalar branch,
`W = E(w,N,C)` and `fee = overhead (32 * frameWidth W C)`. The full runtime bound is:

```text
N * (N*(natEqTime + natSubTime + 257*fee)
     + C*(topicTime + 2*indexTime + natEqTime + 391*fee)
     + 2*natAddTime + addTime + mulTime + scalarTime + zeroTime
     + 516*fee + tickTime)
  + zeroTime + tickTime + 128*fee
```

The pair branch uses `W = E(3*w,N,C)` and
`fee = overhead (32 * frameWidth (3*W) C)`, doubles the add/multiply/sample/zero
prices, and uses `600*fee` inside the loop. Its final initialization charges
`2*zeroTime`. The repeated row scans contribute an `N*N` term; the total runtime
also depends on the encoding widths and the structural overhead function.
The proofs track at most one new cache entry per evaluated row and retain the
original ordered semantics for zero weights, repeats and empty inputs.

Whole-evaluator index representation, 2026-10-14:
[`WeightedCacheEncoding.lean`](../Signatures/Runtime/WeightedCacheEncoding.lean)
proves that injective index maps preserve each private read and the complete
ordered weighted evaluation, including the joint returned value/cache distribution.
[`BackendWeightedEvaluateEncoding.lean`](../Signatures/Runtime/BackendWeightedEvaluateEncoding.lean)
connects both actual native branches to Proximity's original `Option (Fin ell)`
indices and proves exact native cache preservation when all terms are cached.
The maps relate finite states in the proof; they are not runtime table construction.
Validation: the target builds (3307 jobs), log
`/private/tmp/agm-weighted-native-encoding.log`, with no new warnings.

Signing-coefficient expansion is now implemented in
[`WeightedCoefficients.lean`](../Signatures/Runtime/WeightedCoefficients.lean)
and [`BackendWeightedCoefficients.lean`](../Signatures/Runtime/BackendWeightedCoefficients.lean):
chronological matching, per-occurrence scaling, nested cons folds and final
reversal. Exact source representation laws and stored-code bounds pass, as do
regressions for repeated messages, zero/missing/surplus coefficients, dimension
zero, original Proximity indices and full shadowed cache preservation.
Validation: `SignaturesTest.WeightedCoefficients` passes (3324 jobs), log
`/private/tmp/agm-weighted-coefficients-tests2.log`.

[`WeightedCoefficientsSize.lean`](../Signatures/Runtime/WeightedCoefficientsSize.lean)
proves exact output length and encoded-size bounds. With at most `N` signing
replies and degree/dimension `d`, the output uses at most
`(6*N*(d+1)+1)*width` under the stated atomic representation bounds. These bounds
include all zero terms and constrain only encountered topics/slots. The module
passes (3261 jobs), log `/private/tmp/agm-weighted-coefficients-size3.log`.

[`BackendWeightedScale.lean`](../Signatures/Runtime/BackendWeightedScale.lean)
derives the actual scaling fold's native runtime from multiplication and structural
cost contracts. With `T` input terms, an accumulator cap `A`, and atomic width `w`,
its bound is `T*(mulTime + 65*fee) + 64*fee`, where
`fee = overhead (128*((16*(A+T)+32)*w))`. The proof charges the retained input and
accumulator lists, the evolving output, every multiplication and fold control.
This completes the inner fold; the composition below now also covers term
generation in retained contexts, the outer fold, reversal and chronological matching.

Integrated validation: `lake build Signatures SignaturesTest` passes (4013 jobs),
log `/private/tmp/agm-weighted-coefficients-full.log`. The regressions include
the expanded output-size and inner-loop axiom/interface guards. New modules have
no warnings, admissions, additional axioms or proof-resource overrides.

Complete native coefficient-expansion runtime, 2026-10-14:
[`BackendWeightedTermsContext.lean`](../Signatures/Runtime/BackendWeightedTermsContext.lean)
extends both actual term generators to retained caller contexts. Their width
includes the full retained environment and their recursion frames.
[`BackendWeightedExpandStep.lean`](../Signatures/Runtime/BackendWeightedExpandStep.lean)
composes term generation, native scaling and all intermediate routing.
[`BackendWeightedExpandRows.lean`](../Signatures/Runtime/BackendWeightedExpandRows.lean)
reserves `remainingReplies * termsPerReply` output cells, proves the outer fold
runtime, and charges the final reversal. The original rows and growing
accumulator stay in its encoded-state bounds.
[`BackendWeightedCoefficientTime.lean`](../Signatures/Runtime/BackendWeightedCoefficientTime.lean)
adds chronological matching, including coefficient scans, zero defaults and both
matching reversals. Finally,
[`BackendWeightedCoefficientBudget.lean`](../Signatures/Runtime/BackendWeightedCoefficientBudget.lean)
proves `Coefficients.oopsCode_cost` and `Coefficients.proximityCode_cost` for the
actual native source-indexed programs. These final theorems derive their generator
and fold costs from individual primitive contracts. They have no finished-generator,
expansion or solver budget premise, and no finite message/topic/slot premise.

The explicit formulas are `oopsCoefficientTime` and `proximityCoefficientTime`.
They depend on signing cap `N`, coefficient cap `C`, terms per reply `L`, encoded
widths and primitive prices. The outer accumulator cap is `N*L`; every zero-weight
term is retained and charged. `coefficientWidth(w,N,C,L)` is
`(8*N*L + 8*N + 8*C + 64)*w`. Whole-solver dispatch, extraction and general-caller
composition remain open. Targeted proof validation passes (3283 jobs), log
`/private/tmp/agm-weighted-coefficient-budget2.log`. Expanded regressions pass
(3335 jobs), log `/private/tmp/agm-weighted-coefficient-cost-tests.log`, and
`lake build Signatures SignaturesTest` passes (4018 jobs), log
`/private/tmp/agm-weighted-coefficient-cost-full.log`. The checks cover retained
contexts, zero-weight rows with a nonempty accumulator, zero signing allowance,
standard axioms, and absence of finite-domain or supplied component-budget
premises on the final scheme bounds. The new modules have no warnings,
admissions, additional axioms or proof-resource overrides.

Native weighted request dispatch now has its own
[general interface](../Signatures/Runtime/GeneralWeighted.lean) and
[represented ports](../Signatures/Runtime/BackendWeightedInterface.lean).
Hash indices and signing messages can have different, infinite types. Only the
randomness arity is bounded by the interface; one dynamically selected sampler
implements every allowed arity. The [dispatcher](../Signatures/Runtime/BackendWeightedHandler.lean)
executes request decoding, retains the original request during the stateful
reply, attaches its exact dependent reply tag, and selects the appropriate
branch. Its exact general-caller law preserves private state and `none` on
fuel exhaustion. Factoring the indexed reply into a typed semantic handler
preserves the actual executed costs; it adds no unpriced runtime decoder.

The [routing bound](../Signatures/Runtime/BackendWeightedHandlerBudget.lean) is
`replyTime + dynamicTime + 2*adapterTime + 40*overhead(32*frameWidth)`, where
`replyTime` bounds both actual reply branches. Separate input-width predicates
and port contracts cover hash indices and signing messages. Store predicates
remain available for cache growth and transcript invariants. The
[stored-code bound](../Signatures/Runtime/BackendWeightedHandlerDescription.lean)
counts both reply programs, one sampler, all four adapter realizers, and explicit
structural code. The general caller is stored once with the dispatcher and its
loop fuel. These are composition lemmas. The actual reply programs are now
installed and given complete runtime bounds below; dispatcher state invariants, extraction and
the full solver remain.

Validation: `lake build Signatures SignaturesTest` passes (4031 jobs), log
`/private/tmp/agm-weighted-dispatch-full.log`. The
[regressions](../SignaturesTest/WeightedHandler.lean) exercise distinct infinite
query domains, exact native reply tags and store updates, adaptive hash/sign/hash
composition, and observable fuel exhaustion. They also check the standard axiom
footprint and reject finite-domain or completed-dispatcher/caller certificate
premises. The new modules and tests have no warnings, admissions, extra axioms,
or proof-resource overrides.

The actual weighted replies are implemented in
[`WeightedReply.lean`](../Signatures/Runtime/WeightedReply.lean) and
[`BackendWeightedReply.lean`](../Signatures/Runtime/BackendWeightedReply.lean).
Each hash request executes one private read. Each signing request executes the
scheme's term generator, constructs the evaluator's fallback term, and evaluates
the whole ordered list in the shared cache. Both scalar and paired-mask branches
then compute a group response and record exactly one explicit reply. Separate
reverse hash/sign logs preserve the distinct query types. The fixed challenge
configuration and all old cache entries remain in the state.

[`BackendWeightedReplySemantics.lean`](../Signatures/Runtime/BackendWeightedReplySemantics.lean)
identifies the actual generated lists with OOPS's source terms and Proximity's
encoded source terms. [`WeightedExecution.lean`](../Signatures/Runtime/WeightedExecution.lean)
proves joint output/cache/chronological-transcript equality to the original nested
weighted simulator for every adaptive source program. The
[native oracle](../Signatures/Runtime/BackendWeightedOracle.lean) installs all four
reply programs and proves their general-caller correspondence. Hashing grows the
cache by at most one; signing grows it by at most the generated term count, while
adding just one signing token and preserving the entire hash log.

Complete [stored-code bounds](../Signatures/Runtime/BackendWeightedReplyDescription.lean)
charge each sampler, generated term program, fallback, response, transcript update
and retained frame. [Local response costs](../Signatures/Runtime/BackendWeightedReplyCost.lean)
are derived from individual group/structural contracts, and
[encoded frame/result bounds](../Signatures/Runtime/BackendWeightedReplySize.lean)
charge both logs and the shared cache.

Complete weighted reply runtime assembly is now checked:

- [`BackendWeightedReplyAssembly.lean`](../Signatures/Runtime/BackendWeightedReplyAssembly.lean)
  derives the reply wrapper overhead from a private value computation. Its frame
  width `32 * width + valueWidth` includes the entire original request/store
  retained across that computation. It charges argument construction, local
  calls, sequence edges, retention, response computation and the log update.
- [`BackendWeightedSignAssembly.lean`](../Signatures/Runtime/BackendWeightedSignAssembly.lean)
  charges the signing prefix's actual term and fallback generators and both
  retained-cache frames. The fallback executes even when all real rows exist.
- [`BackendWeightedSignInputs.lean`](../Signatures/Runtime/BackendWeightedSignInputs.lean)
  derives generated term count, row/list/default sizes, and generator/default
  runtime from primitive contracts. There are `index.bound + 1` rows, each at
  most `5 * width`, and the list is at most `(6 * (index.bound + 1) + 1) * width`.
  The topic/slot bound concerns the supplied message only.
- [`BackendWeightedSignValueBudget.lean`](../Signatures/Runtime/BackendWeightedSignValueBudget.lean)
  composes these actual generators with the complete scalar/pair evaluator
  budgets, including private sampling, coefficient arithmetic, index scans,
  loop ticks and cache growth.
- [`BackendWeightedHashBudget.lean`](../Signatures/Runtime/BackendWeightedHashBudget.lean)
  and [`BackendWeightedSignBudget.lean`](../Signatures/Runtime/BackendWeightedSignBudget.lean)
  derive all four finished reply runtime/output-width bounds from primitive,
  sampler, width and loop-control contracts. None assumes an efficient finished
  reply, generator or evaluator. Separate finite index and message universes are
  unnecessary; the native programs use only encountered entries.

Complete native interaction composition is now checked:

- [`BackendWeightedStateSize.lean`](../Signatures/Runtime/BackendWeightedStateSize.lean)
  bounds the encoded challenge, cache, and both reply logs using separate
  encountered-index/message widths and scalar/pair mask sizes.
- [`BackendWeightedHandlerState.lean`](../Signatures/Runtime/BackendWeightedHandlerState.lean)
  preserves the challenge and key/message bounds through every actual reply.
  Each remaining request reserves `L = degree/dimension + 1` cache entries and
  one explicit log entry. The aggregate store bound is `(32 * cap * L + 32) * w`.
- [`BackendWeightedOracleBudget.lean`](../Signatures/Runtime/BackendWeightedOracleBudget.lean)
  derives both full dispatcher budgets from the actual reply bounds and primitive,
  sampling, port, and control contracts; no completed reply/dispatcher cost is supplied.
- [`BackendWeightedCallerBudget.lean`](../Signatures/Runtime/BackendWeightedCallerBudget.lean)
  proves indexed caller composition for distinct hash-index/signing-message types.
  [`BackendWeightedOracleCallerBudget.lean`](../Signatures/Runtime/BackendWeightedOracleCallerBudget.lean)
  applies it to both actual branches, retaining the final capacity/size invariant.
  The bound is attacker local work plus per-kind query costs and charged caller
  initialization, routing, and loop control. It currently takes caller reachability
  and encoding conditions explicitly, alongside the attacker's own budget.
- [`BackendWeightedOracleDescription.lean`](../Signatures/Runtime/BackendWeightedOracleDescription.lean)
  derives complete dispatcher/caller stored-code bounds, including both replies,
  term generation, samplers, ports, caller code, and bounded-loop syntax.

The [weighted extractor syntax](../Signatures/Runtime/WeightedExtraction.lean)
now executes chronological coefficient expansion, ordered scalar/pair evaluation,
final-target term construction and evaluation, and the source field formula.
[Both compiled extractors](../Signatures/Runtime/BackendWeightedExtraction.lean)
have exact joint output/cache laws. Hash replies use a singleton term of weight
one through the same coefficient routine; its extra stored code is charged.
Zero-weight terms still cause reads, missing coefficients are zero, and surplus
coefficients do not create transcript entries. Division by zero is unchanged.

[Complete extractor stored-code bounds](../Signatures/Runtime/BackendWeightedExtractionDescription.lean)
count both term-generator occurrences, chronological matching, all evaluator/read
bodies, samplers, executed defaults and final arithmetic. The
[cached-transcript laws](../Signatures/Runtime/WeightedExtractionState.lean) prove
that transcript evaluation draws no fresh masks and retains the complete cache,
including shadowed bindings. The
[native cache invariant](../Signatures/Runtime/BackendWeightedExtractionState.lean)
preserves old bindings and key predicates and bounds growth by `degree/dimension + 1`
for the final target alone, conditional on the transcript bases already being cached.

The extractor now calls pure preparation routines in their own argument frames.
The revised syntax retains the exact source/cache laws and stored-code bounds.
[Call assembly](../Signatures/Runtime/BackendWeightedExtractionAssembly.lean)
charges both argument constructions, both native calls, sequencing, and the
retained surrounding frame/cache. Each preparation/evaluation call adds at most
`64 * overhead (1024 * frameWidth)` to its actual component costs.
[Frame bounds](../Signatures/Runtime/BackendWeightedExtractionFrames.lean) count
complete transcripts, coefficient lists (including unused suffixes), defaults,
and scalar/paired caches (including shadowed bindings).

[Signing inputs](../Signatures/Runtime/BackendWeightedExtractionInputs.lean)
derive the actual generator costs and bound expanded rows by
`signReplies * (degree/dimension + 1)`. The
[hash generator budget](../Signatures/Runtime/BackendWeightedHashCoefficients.lean)
also charges its executed constant one and multiplication by one. Complete
[hash-transcript](../Signatures/Runtime/BackendWeightedHashExtraction.lean),
[scalar/paired signing-transcript](../Signatures/Runtime/BackendWeightedSigningExtraction.lean),
and [scalar/paired final-target](../Signatures/Runtime/BackendWeightedTargetExtraction.lean)
call bounds derive preparation and evaluation costs from primitive, sampler,
encoding and loop-control contracts, with no completed component budget supplied.
[Final arithmetic and argument bounds](../Signatures/Runtime/BackendWeightedExtractionCost.lean)
are checked too. The complete
[good extractor](../Signatures/Runtime/BackendWeightedGoodExtractionBudget.lean) and
[bad extractor](../Signatures/Runtime/BackendWeightedBadExtractionBudget.lean)
now compose these calls and discharge every component budget from primitive,
sampling, encoding and control contracts. Their runtime includes executed default
construction, final arithmetic, and all native call/bind routing.
[Outer argument costs](../Signatures/Runtime/BackendWeightedExtractionArgs.lean) and
[retained-frame bounds](../Signatures/Runtime/BackendWeightedOuterExtractionSize.lean)
charge the full attacker output, both transcripts and intermediate values even
when a branch does not use some of them. The generic
[good assembly](../Signatures/Runtime/BackendWeightedGoodExtractionAssembly.lean) and
[bad assembly](../Signatures/Runtime/BackendWeightedBadExtractionAssembly.lean)
allow changing cache invariants; the actual endpoints discharge their call premises.

[Intermediate cache laws](../Signatures/Runtime/BackendWeightedExtractionCallState.lean)
prove that transcript calls keep the exact cache when their bases are already
cached. This recovers the original cache length and key widths at each later call,
including shadowed bindings. The final target may add entries. An explicit
[whole-extractor width](../Signatures/Runtime/BackendWeightedExtractionWidth.lean)
bounds all phases using transcript/coefficient capacities, degree/dimension and
encountered encodings, with no message-domain cardinality. Both final runtime
endpoints retain the cached-transcript invariant as an input state condition;
they do not assume any completed component or extractor budget.

[Request recovery](../Signatures/Runtime/BackendWeightedCallerResources.lean) now
derives request widths, reachability and continuation closure from the caller's
measured `RunsWithin` resources. Hash-index and signing-message encodings stay
independent; shared canonical request encoding has identity size recovery. The
actual port execution remains charged. Both
[native caller bounds from resources](../Signatures/Runtime/BackendWeightedOracleCallerResources.lean)
substitute the attacker's work, query and peak-size bounds, with no supplied
caller invariant or `GeneralCaller.Budget`.

[Native output transport](../Signatures/Runtime/BackendWeightedCallerOutput.lean)
bounds each returned output, including the final zero-fuel readout, and proves
there is no cutoff once fuel covers the measured query bound. For shared tuple
output encoding, [coefficient recovery](../Signatures/Runtime/BackendWeightedExtractionOutput.lean)
derives both coefficient lengths from peak head size, including unused suffixes.
The [positive-cell list law](../Signatures/Runtime/BackendWeightedOutputSize.lean)
is explicit. [Extractor entry bounds](../Signatures/Runtime/BackendWeightedExtractionEntry.lean)
combine the output cap with preserved cache/log capacities: the full input frame
is bounded by `outputCap + (8 * replyCap + 8) * width`, both token types are bounded,
and cache/query/coefficient capacities are recovered.

[Source interaction cache preservation](../Signatures/Runtime/WeightedExecutionCache.lean)
follows every adaptive reply without finite domains or a source runtime premise.
The [actual native caller cache laws](../Signatures/Runtime/BackendWeightedOracleCache.lean)
transfer it using resource-derived termination and exact source correspondence.
Starting with an empty store, both branches return an output, retain their original
challenge configuration and supply the extractor's cached-transcript condition.

Both [complete native programs](../Signatures/Runtime/BackendWeightedSolver.lean)
now perform challenge setup, the measured general caller, output conversion,
cutoff handling and actual extraction. The good branch retains the challenge
public key; the bad branch samples its signing scalar and computes the scaled
key. [Exact source laws](../Signatures/Runtime/BackendWeightedSolverCorrectness.lean)
identify each whole program with the corresponding weighted finite-list source
reduction. Resource-derived termination removes the cutoff on realized source runs.

[Setup bounds](../Signatures/Runtime/BackendWeightedSolverSetup.lean) charge the
empty store, full challenge frame, key conversion, and bad-branch sampling and
scaling. [Terminal bounds](../Signatures/Runtime/BackendWeightedSolverTerminal.lean)
derive all extraction conditions from the saved store and full encoded output.
The [complete runtime proof](../Signatures/Runtime/BackendWeightedSolverBudget.lean)
carries the cached-transcript invariant from the actual caller into extraction,
and charges all sequencing and retained frames. Its assumptions concern measured
attacker resources, source realization, representation laws and individual
operations; no completed caller/extractor budget or internal cache invariant is
supplied by the user.

[Stored-code bounds](../Signatures/Runtime/BackendWeightedSolverDescription.lean)
include attacker initialization, two head-code copies, updates, scalar and dynamic
samplers, ports, fuel, and three term-generator occurrences. Degree/dimension is
explicitly charged, with a common polynomial expression for both generator kinds.
The [fixed-backend certificates](../Signatures/Runtime/BackendWeightedSolverWithin.lean)
combine these bounds with exact source semantics into `goodProgram_within` and
`badProgram_within`. Index and message encodings remain separate, neither domain
is finite, and no arithmetic-language implementation of the attacker is required.

[Whole-program regressions](../SignaturesTest/BackendWeightedSolver.lean) cover
zero-fuel cutoff and retained bad-branch sampling with arbitrary natural topics.
Transitive axiom guards cover the new proofs. Final-endpoint guards reject finite
domains, supplied complete component/certificate bounds, restricted source
certificates and internal state invariants; they require both measured execution
and source realization.

The shared [weighted parameter interface](../Signatures/Runtime/GeneralWeightedParameters.lean)
now fixes the backend, representation/primitive contracts, query allowances and
attacker execution/code limits before choosing the attacker. The attacker
supplies its general native realization, measured resources and actual source
query counts. [Certificate assembly](../Signatures/Runtime/GeneralWeightedCertificates.lean)
derives both complete reduction certificates and their resource-indexed DLog
bounds. Input width covers every generated challenge; solver code charges all
stored native code, and the two time bounds include degree/dimension work.

The [OOPS concrete proof](../Signatures/OOPS/Proofs/GeneralAGM.lean) uses the
original scalar/topic source game and its target-topic distinct-message rule.
The [Proximity concrete proof](../Signatures/Proximity/Proofs/GeneralAGM.lean)
uses the original function-vector/optional-coordinate source interface and
retains the actual fresh-collision probability. Its
[encoding proof](../Signatures/Proximity/Proofs/GeneralAGMEncoding.lean) identifies
both entire source solvers with the native tuple/finite-index versions and
preserves all three query counts through adaptive interaction. This is a proof
relabeling; the attacker's actual implementation, including its encoded output,
is still charged by the native resource contract.

The public [OOPS](../Signatures/OOPS/Statement.lean) and
[Proximity](../Signatures/Proximity/Statement.lean) statements now have five explicit
inputs: curve, security parameter, degree/dimension, query allowances and algebraic
adversary. The conclusion displays the game, twice a DLog success bound at the
maximum derived solver time, and the inverse-field-size loss; Proximity also
displays its collision probability. Separate two-budget statements retain the
sharper bound. Game definitions and hardness suprema are inspectable in each
`GeneralSecurityModel.lean`, and proof bodies live in `Proofs/GeneralSecurity.lean`.
Older arithmetic-source declarations remain available under their existing
names via `ArithmeticStatement.lean` compatibility imports.

[Public-interface regressions](../SignaturesTest/WeightedGeneralSecurity.lean)
check the five-input declarations, proof locations, transitive axiom footprints,
resource contracts and visible loss terms. An adaptive Proximity test checks
hash/sign replies, both coordinate tags and the returned vector encoding with
natural slots and a distinct unused machine message atom.

[Weighted polynomial closure](../Signatures/Runtime/BackendWeightedPolynomial.lean)
now derives polynomial growth of the complete good/bad runtime formulas and the
stored-code formula. The proof composes handler and extractor lemmas, including
term construction and coefficient expansion. One polynomial bounds degree or
dimension across the security parameter; a bound polynomial in its numerical
value is not silently treated as polynomial in its binary encoding length.
Both branch choices are covered, even for an index family that changes schemes.

[Shared family resources](../Signatures/Runtime/GeneralWeightedFamilyResources.lean)
contain only polynomial caller, query, encoding, primitive, sampler and stored
component-code bounds. Completed solver efficiency is derived. One fixed
`Configuration` determines execution and description costs across all parameters.
Groups, topics, slots and message atoms may vary with the parameter; no finite
label/message/public-key domain is assumed. The
[DLog family class](../Signatures/Runtime/BackendWeightedDLogFamily.lean) charges
polynomial code/advice and time and covers every generated challenge.

The [OOPS family statement](../Signatures/OOPS/GeneralAGMFamilyStatement.lean)
uses the original source game and distinct-message rule and concludes negligible
forgery under this nonuniform DLog hardness and negligible inverse field size.
The [Proximity family statements](../Signatures/Proximity/GeneralAGMFamilyStatement.lean)
first give the original collision probability plus a negligible error. Their
negligible-forgery corollary has an explicit negligible-collision hypothesis for
that same source adversary. Proof bodies remain separate. These are conditional
fixed-backend results; they do not construct a uniform program generator or a
conventional-machine instantiation.

[Family regressions](../SignaturesTest/WeightedFamilies.lean) exercise growing
degrees/dimensions and both complete solver formulas, check transitive standard
axioms and forbid assumed completed-solver efficiency or finite label domains.
They require varying group/label/dimension families, fixed-backend hardness and
the original Proximity collision qualification.

Weighted-family validation: `lake build Signatures SignaturesTest` passed
(4119 jobs), log `/private/tmp/agm-weighted-family-full.log`. The eight new
modules/tests have no warnings, admissions, extra axioms or proof-limit overrides.
All 710 local links in the five changed status/review documents were checked.

Concrete/public validation: `lake build Signatures SignaturesTest` passed
(4111 jobs), log `/private/tmp/agm-weighted-general-security-full.log`.
The new modules and regression have no warnings, admissions, extra axioms or
proof-resource overrides. All 692 local links across the five changed status
and review documents were checked. The former arithmetic-source declarations
retain their statements and proofs; only their file locations and scope comments changed.

Whole-solver validation: `lake build Signatures SignaturesTest` passed (4096 jobs),
log `/private/tmp/agm-weighted-solver-full.log`. The eleven new solver modules and
whole-program regression have no warnings, admissions, extra axioms or
proof-resource overrides. All 567 local links in this plan and the two companion
status documents were checked.

Prior recovery validation: `lake build Signatures SignaturesTest` passed (4084 jobs), log
`/private/tmp/agm-weighted-caller-recovery-full.log`. The
[native reply regressions](../SignaturesTest/WeightedReply.lean) cover signing
before explicit hashing, shadowed cache entries, both mask coordinates, zero
degree, and a zero-weight unseen base that still samples and enters the cache.
They check complete returned state and the standard axiom footprint, including
all four complete runtime budgets and both signing-value compositions, and reject
finite-domain or supplied complete-budget premises. The new modules/tests have
no warnings, admissions, extra axioms, or proof-resource overrides.
The [full-interaction regressions](../SignaturesTest/WeightedOracleBudget.lean)
also check an adaptive hash/sign/hash sequence with a shadowed cache entry,
both reply logs, and all new state/runtime/code theorems' transitive axioms.
They reject finite-domain and supplied completed-dispatcher/reply budgets; only
caller composition accepts the attacker's own resource budget. The new final
resource APIs reject supplied caller budgets, custom caller invariants,
coefficient-length limits and completed-native-runtime bounds. Empty-store cache
endpoints reject any supplied cached-transcript premise. A Proximity output test
checks that an arbitrary all-zero coefficient suffix still consumes encoded space.
The [native extraction regressions](../SignaturesTest/WeightedExtraction.lean)
check OOPS chronological coefficients, missing and surplus coefficients, exact
cached extraction, and an unseen final topic whose zero-weight base still draws
and retains a mask. A Proximity case checks both mask coordinates and the final
field division. All cases retain shadowed cache bindings. The new extraction
semantic, stored-code and cache theorems have transitive axiom guards and reject
finite-domain and supplied finished-extractor budget premises.
The guards also cover all new argument/frame/state/assembly bounds. The five
complete call endpoints and both full-extractor endpoints reject supplied runtime
bounds for compiled preparation, evaluation, private readers, or complete native
extractors. The semantic cases exercise the actual native-call syntax.

The import blocker was macOS vnode exhaustion, confirmed by free vnodes reaching
zero during a monitored Lean import. The user applied a temporary vnode-limit
increase from 263168 to 524288, which restored proof checking. Descriptor limits
were also temporarily raised; their original values are recorded for restoration.
No compiler checking settings changed. The remaining security, family and replay
obligations below stay incomplete.

`SignaturesTest.WeightedCache` checks native scalar/pair caches over infinite
topics, both components of each key, cached zero, shadowed keys, empty caches,
degree/dimension zero, pair sampling, and costed sampler replacement on hits.
It checks Proximity's original coordinate encoding and demonstrates the false
hit that a noninjective encoding would introduce. Interface guards reject
finite-domain, finished-cache, and supplied-comparator assumptions on the final
component bounds; transitive axiom checks allow only Lean's standard axioms.
Validation: `lake build Signatures SignaturesTest` passes (3980 jobs), including
the final cache regressions, log `/private/tmp/agm-weighted-cache-full.log`.
The new modules have no warnings, admissions, extra axioms, or proof-resource overrides.

`SignaturesTest.WeightedTerms` checks source and compiled generators over infinite
topic/slot types, distinct topic and message atoms, power order, zero scalar and
zero-coordinate terms, degree/dimension zero, and unrelated retained context.
Compiled key tests distinguish changes in either key component, including the
constant coordinate. The guards check standard axioms, reject finite-domain
premises, and reject whole-program budget premises on the native component results.
Validation: `lake build SignaturesTest.WeightedTerms` passes (3262 jobs), followed
by `lake build Signatures SignaturesTest` (3976 jobs), log
`/private/tmp/agm-weighted-native-full.log`. The new modules have no warnings,
admissions, extra axioms, or proof-resource overrides.

Validation: [`SignaturesTest.WeightedAGMReduction`](../SignaturesTest/WeightedAGMReduction.lean)
passes checks for distinct index/message types over infinite domains, repeated
hash/sign calls, signing before hashing, weighted unseen final targets, both
branches, zero denominators, missing/extra coefficients, empty weighted sums,
adaptive randomness/replies, and pure cache reuse with shadowed entries.
The guards verify standard axioms and the absence of finite-domain premises on
the lazy programs, cache refinements, and entry-count bounds. The full
`lake build Signatures SignaturesTest` passes (3960 jobs), log
`/private/tmp/agm-weighted-full-suite.log`; the new modules have no warnings or admissions.

Arbitrary-domain validation: `SignaturesTest.WeightedAGMTransport` verifies a
finite cover for an adaptive attacker with infinite topic/public-key types,
rejects covers omitting the final target or one reply-dependent signing branch,
and proves exact program recovery including coefficient lists. Collision tests
retain contributions from other slots and extra coefficient behavior; they also
show why merging slots without injectivity can break freshness. The new theorem
guards check standard axioms and reject finite index/message/topic/slot/public-key
premises. The full `lake build Signatures SignaturesTest` passes (3969 jobs), log
`/private/tmp/agm-arbitrary-weighted-full-suite.log`; the new transport modules
have no warnings or admissions. Native weighted resource accounting is next.

Charge generation of these terms, degree/coordinate computations, encoded key
comparisons, and representation lengths. A bound polynomial in the numerical
degree is not automatically polynomial in its binary encoding length. Bound
degree and dimension in the security parameter where an asymptotic claim needs it.

Preserve OOPS's admissibility condition and Proximity's explicit fresh-collision
probability. These are oracle-derived-base games; this work does not establish
standard-model public-setup variants or remove algebraicity.

## Schnorr composition and replay

The single-pass AGM route now has these checked foundations:

- [Finite cache](../Signatures/Runtime/SchnorrAGMCache.lean): an association list
  of encountered message/commitment pairs, retaining the first cached challenge
  and affine explanation on repeated hashes or signing collisions.
- [Adaptive execution](../Signatures/Runtime/SchnorrAGMExecution.lean): exact
  query-tree equality of the complete output and abstracted state, including
  malformed requests, chronological signing bases, and final extraction. This
  correspondence holds for arbitrary query trees, before imposing algebraicity.
- [Storage capacity](../Signatures/Runtime/SchnorrAGMGrowth.lean): at most
  `qS + qH + 1` cached pairs, `qS + 2` affine basis entries, and `qS` signed
  messages, independent of domain cardinality. Private random requests add no
  cache entries. These are entry counts, not encoded-size or runtime bounds.
- [Probability transport](../Signatures/Runtime/SchnorrAGMSecurity.lean): the
  original source forgery bound holds with this finite-store solver and unchanged
  losses. The solver uses its input generator; equality to the old fixed-generator
  solver is proved at the complete DLog-experiment level.
- [Regressions](../SignaturesTest/SchnorrAGMFiniteCache.lean): late explanations,
  signing collisions, signing before hashing, malformed requests, adaptive
  repeated hashes, an unseen final target, and transitive axiom guards.

Validation: `lake build Signatures SignaturesTest` passed (4124 jobs); the new
refinement, capacity, extraction and security declarations use only the standard
`propext`, `Classical.choice`, and `Quot.sound` axioms.

The native cache core is now implemented and charged:

- [Tuple/list layouts](../Signatures/Runtime/SchnorrAGMEncoding.lean) encode
  affine explanations as scalar pairs, cache entries with an explicit optional
  explanation tag, and the full finite source state. Decoding after encoding is
  the identity. Cache lookup commutes with the encoding, including shadowed keys.
- [Key comparison](../Signatures/Runtime/BackendSchnorrAGMComparison.lean) compiles
  message and commitment equality tests, deriving native time and description
  bounds from the two component instructions and structural operations.
- [Fresh-entry sampling](../Signatures/Runtime/BackendSchnorrAGMFresh.lean) retains
  the explanation as runtime data, samples a scalar, builds the entry and updates
  the bad flag through field addition/equality. Its [complete bound](../Signatures/Runtime/BackendSchnorrAGMFreshBudget.lean)
  includes value retention, adapters, arithmetic, and control transitions.
- [Native cache access](../Signatures/Runtime/BackendSchnorrAGMCache.lean) combines
  the actual comparator and fresh-entry sampler with the list-cache compiler.
  Its output/cache/bad flag agrees with the finite-store source read after the
  untouched metadata is restored in the proof relation. A hit preserves the
  entire costed run when the sampler is replaced. Both runtime and stored code
  are derived; the explanation is never hidden in a captured sampler constant.
- [Cache runtime](../Signatures/Runtime/BackendSchnorrAGMCacheBudget.lean) is at
  most `cap * (messageTime + pointTime + 391 * fee) + sampleTime +
  2 * fieldTime + equalityTime + 395 * fee`, where
  `fee = overhead (32 * CacheCompiler.frameWidth (5 * width) cap)`.
  Scalar and explanation sizes are bounded by `width`; keys/entries use the
  explicit `5 * width` cap. The formula charges every cache scan and compiler
  environment. The premises concern primitive operations and sampling, never
  efficiency of the completed cache procedure.
- [Native regressions](../SignaturesTest/BackendSchnorrAGMCache.lean) check
  pre-challenge explanation retention, bad-flag behavior, signing-programmed
  entries, shadowed entries, changed commitments, absent-key sampling, and
  complete no-sampling behavior on hits. Guards reject finite-domain premises
  and circular cache-efficiency assumptions and check transitive axioms.

Native-cache validation: `lake build Signatures SignaturesTest` passed (4132 jobs);
the targeted cache regressions passed (3373 jobs), with no new warnings or
nonstandard axioms.

The [complete native read](../Signatures/Runtime/BackendSchnorrAGMRead.lean) now
executes both surrounding adapters: constructing a zero-tagged fallback,
packing the cache arguments, retaining the full metadata, and returning the
challenge with the updated cache/bad flag. Its joint output/state distribution
is exactly the encoded finite-source read. Replacing the scalar sampler on a
hit preserves the complete costed wrapper run. The default reuses the supplied
affine pair in ignored slots; it is never inserted on a miss.

The [read size invariants](../Signatures/Runtime/BackendSchnorrAGMReadSize.lean)
bound the representation history and signing history separately by `historyWidth`.
These bounds are preserved unchanged across reads; only the cache capacity grows
from `cap` to at most `cap + 1`. Every outer boundary fits
`W = (20 * cap + 200) * width + 4 * historyWidth`.
The [compiled adapter costs](../Signatures/Runtime/BackendSchnorrAGMReadLocalCost.lean)
and [complete read budget](../Signatures/Runtime/BackendSchnorrAGMReadBudget.lean)
derive the bound
`cacheTime + fieldTime + 800 * overhead (256 * W)`.
It charges default creation, tuple projections/construction, retained metadata,
and all local-call/sequence transitions. The stored-code bound is the scalar
sampler's code plus the message/group comparisons, field addition, two zero
instructions, scalar equality and a fixed structural allowance. Neither theorem
assumes a finished adapter, cache, or read is efficient.

[Complete-read regressions](../SignaturesTest/BackendSchnorrAGMRead.lean) check
shadowed hits, late explanations, signing-programmed entries, changed commitments,
miss-induced bad events and preservation of every metadata field. They also
check transitive axioms and reject finite-domain or completed-component premises.
Complete-read validation: the targeted test passed (3377 jobs), and
`lake build Signatures SignaturesTest` passed (4136 jobs), with no new warnings
or nonstandard axioms. All 399 local links in the two edited guides resolve.

[Native affine flattening](../Signatures/Runtime/SchnorrAGMFlatten.lean) now
matches the exact source `flatten`, with no equal-length or algebraicity premise.
It attaches coefficients to the chronological received-basis list using the
existing charged positional matcher, then computes both affine coordinates by
a fold with two field products and two additions per row. Missing coefficients
are zero, surplus coefficients do not create basis entries, and repeated affine
representations remain distinct positions.

The [sum-fold cost](../Signatures/Runtime/BackendSchnorrAGMFlattenSum.lean) is
at most `N * (2 * mulTime + 2 * addTime + 257 * fee) + 32 * fee`, with
`fee = overhead (128 * (6 * N + 32) * width)`. The
[complete flattening bound](../Signatures/Runtime/BackendSchnorrAGMFlattenBudget.lean)
adds the actual coefficient matcher, zero initialization and surrounding retained
frames. For atom/context width `w`, basis cap `N` and full coefficient cap `L`,
set `W = (8 * N + 4 * L + 32) * w`; the bound is
`AttachCompiler.tableTime overhead (3*w) N L ... + zeroTime +
sumTime overhead W N mulTime addTime + 64 * overhead (128 * W)`.
The output has encoded size at most `3*w`. The
[stored-code bound](../Signatures/Runtime/BackendSchnorrAGMFlatten.lean) is the
zero, natural comparison/subtraction/increment, two scalar multiplication and
two scalar addition instructions, plus a fixed structural allowance. These
bounds are derived for arbitrary retained contexts. They require only primitive,
representation and input-size contracts, with no finite-domain or completed-
component efficiency premise. This bound is polynomial in the list caps when
primitive costs and structural overhead are polynomial; it does not assert
linear-time coefficient lookup.

[Flattening regressions](../SignaturesTest/BackendSchnorrAGMFlatten.lean) cover
chronological signing representations, short and surplus coefficients, duplicate
basis entries, an empty basis, transitive axioms, and the resource-contract scope.
Validation: the targeted test passed (3361 jobs), and
`lake build Signatures SignaturesTest` passed (4139 jobs), with no new warnings
or nonstandard axioms. All 406 local links in the two edited guides resolve.

The [decoded hash path](../Signatures/Runtime/BackendSchnorrAGMHash.lean) now
computes the affine explanation before reading the cache and keeps the entire
original state in represented runtime data. It matches the finite-source read
for every coefficient vector, including short and surplus vectors. Supported
executions preserve both histories and the malformed flag exactly. Cache hits
retain the first explanation and skip the sampler, while still charging
coefficient processing.

Its [input/size invariants](../Signatures/Runtime/BackendSchnorrAGMHashSize.lean)
use base width `w`, cache cap `K`, separate history bound `H`, basis cap `N` and
full coefficient cap `L`. With
`W = Read.frameWidth (3*w) K H + (4*L+64)*w`, the
[complete bound](../Signatures/Runtime/BackendSchnorrAGMHashBudget.lean) is
`Flatten.flattenTime overhead W N L ... + Read.readTime overhead (3*w) K H ...
+ 262*overhead(256*W)`. The widened read accommodates both encoded affine
coordinates. [Preparation costs](../Signatures/Runtime/BackendSchnorrAGMHashLocalCost.lean)
include the original input, retained compiler environments, packing and the
local-call frame. The public bound assumes primitive/sampler and representation
contracts, not a completed flattening, read or hash budget. Stored code is
bounded by the component descriptions and a fixed structural allowance.

The [singleton decoder](../Signatures/Runtime/ListSingleton.lean) uses two Boolean
flags and one candidate; no uncharged length operation or natural counter is
needed. Its [native bound](../Signatures/Runtime/BackendListSingleton.lean) is
`L*129*fee + 64*fee`, where `fee = overhead(128*(4*L+32)*w)`; the retained
context and candidate must fit `w`. It scans all input cells, returns an output
of size at most `3*w`, and has description size at most `128*allowance`.
Its validity flag is true exactly when the input is the singleton containing
the returned candidate. In particular, `[[]]` is one coefficient row and two
identical group elements still form an invalid two-element group list.

[Regressions](../SignaturesTest/BackendSchnorrAGMHash.lean) cover these shape
distinctions, first-explanation preservation, sampler-independent cache hits,
exceptional-challenge misses and empty inner vectors, together with transitive
axiom and public-contract guards. The decoded path and decoder are separate
components; the following checkpoint connects them into the all-shape dispatcher.

Validation: the targeted test passed (3402 jobs), and
`lake build Signatures SignaturesTest` passed (4149 jobs). The new declarations
have no nonstandard transitive axioms or new warnings; all 416 local links in
the two edited guides resolve.

The [all-shape hash dispatcher](../Signatures/Runtime/BackendSchnorrAGMHashDispatch.lean)
now scans the complete group list and coefficient-row list, constructs default
candidates, and branches to the decoded hash or rejection routine. Its scalar
and encoded-state output corresponds to the source handler's canonical scalar
reply and complete state for every request shape. A rejected request returns
zero and sets malformed, preserving the cache, representations, signed messages
and bad flag. Changing the sampler leaves the entire costed rejection execution
unchanged. Neither list length nor list shape is supplied as an uncharged primitive.

The [size contract](../Signatures/Runtime/BackendSchnorrAGMHashDispatchSize.lean)
includes group cap `G`, coefficient-row cap `R`, per-row coefficient cap `L`,
basis cap `N`, cache cap `K` and separate history bound `H`. For atom width `w`,
the retained-input bound is
`W = Read.frameWidth (3*w) K H + (4*G + 4*R*(L+1) + 4*L + 128)*w`.
Thus even discarded rows and extra groups are charged. Decoding produces the
existing hash input contract, including a bounded candidate for invalid requests.
The [preparation bound](../Signatures/Runtime/BackendSchnorrAGMHashDispatchLocalCost.lean)
is `P = pointZeroTime + ListSingleton.scanTime overhead (16*W) G +
ListSingleton.scanTime overhead (16*W) R + 512*fee`, with
`fee = overhead(4096*W)`. [Selector and rejection costs](../Signatures/Runtime/BackendSchnorrAGMHashDispatchRouting.lean)
are derived from compiled code and structural laws. The
[complete budget](../Signatures/Runtime/BackendSchnorrAGMHashDispatchBudget.lean)
is `P + max(Hash.hashTime ..., fieldTime + 517*fee) + 5*fee`, including local
calls, branch and sequence transitions. Its public premises concern input sizes,
primitive operations, scalar sampling and representation/structural laws; no
finished dispatch, scan, hash or rejection budget is assumed. The description
bound adds group-zero, scalar-zero and a constant structural allowance to the
decoded hash description, independently of runtime request lengths.

[Dispatcher regressions](../SignaturesTest/BackendSchnorrAGMHashDispatch.lean)
cover duplicate points, missing coefficient rows, multiple empty rows, one empty
row, cache hits retaining the first explanation, sampler-independent rejection,
standard transitive axioms and the public resource-contract scope.

Validation: the dispatcher regression target passed (3408 jobs), and
`lake build Signatures SignaturesTest` passed (4155 jobs), including the final
parameter cleanup. No new warnings or nonstandard transitive axioms occur in
these declarations. All 424 local links in the two edited guides resolve.

The [history append](../Signatures/Runtime/BackendListSnoc.lean) now executes two
reversals and a cons. It preserves every chronological coefficient position,
including duplicates. For cell/context width `w` and history cap `N`, its derived
time is `(34*N+113) * overhead (128*((4*N+12)*((8*N+32)*w)))`; stored code is at most
`96*structuralAllowance`, independent of `N`. Both traversals, intermediate lists
and the retained input/context are charged; no append primitive is assumed.

The [cache-programming compiler](../Signatures/Runtime/BackendCacheProgramming.lean)
scans an association list and inserts the supplied value only on a miss.
Existing entries, cached zero and shadowed duplicates remain unchanged. Its time
bound is `K*(comparisonTime+257*fee)+160*fee`, where
`fee = overhead (128*((4*K+16)*w))`; it needs only comparison and representation
contracts, and adds at most one bounded entry.
The [Schnorr specialization](../Signatures/Runtime/BackendSchnorrAGMProgramming.lean)
implements comparison from message/group primitives, includes the local-call
charge, and exactly realizes the cache part of `signedState`. It has no sampling
command. Its stored code is bounded by the two comparison primitives plus
`264*structuralAllowance+1`.
[Regressions](../SignaturesTest/BackendSchnorrAGMSigningStorage.lean) check
chronological duplicates, empty histories, cached zero, shadowed entries, fresh
insertion and independence of query costs in the full costed programming run.
They also check transitive axioms and exclude completed-component efficiency or
finite-domain premises from the public bounds.

These storage operations are signing components. The following checkpoint
composes the accepted path; malformed-request dispatch remains separate.

Validation: `SignaturesTest.BackendSchnorrAGMSigningStorage` passed (3378 jobs),
and `lake build Signatures SignaturesTest` passed (4161 jobs). The new modules
have no warnings or nonstandard transitive axioms. All 430 local links in the
two edited guides resolve.

The [accepted signing core](../Signatures/Runtime/BackendSchnorrAGMSigning.lean)
now implements both scalar draws in source order (`c`, then `z`), computes
`R = z*g - c*pk`, appends `(z,-c)` and the signed message chronologically,
programs `(c,none)` only on a cache miss, and returns `(R,z)` with the complete
updated state. Existing cache entries and both Boolean flags are preserved.
The native sampler executes twice even on a signing collision. The source
theorem gives exact query-tree and encoded-state correspondence for accepted
signing requests, including arbitrary ignored coefficient rows.

Its [size contracts](../Signatures/Runtime/BackendSchnorrAGMSigningSize.lean)
bound encountered cache entries, basis entries and signed messages by `K,N,S`.
Cache keys/entries fit `15*w`; message-history cells fit `w`; affine cells fit
`3*w` from the scalar representation contract. The sampled input, arithmetic
output, updated histories, programmed state and final output share the bound
`W = (128*K+16*N+8*S+256)*w`. Other retained environments are charged by their
local and control bounds. The output adds at most one cache entry and appends
one basis entry and one signed-message entry. No finite message/group universe is assumed.

The [complete bound](../Signatures/Runtime/BackendSchnorrAGMSigningBudget.lean)
is `A + H + P + 2*sampleTime + 1840*overhead(256*W)`, where
`A = 2*fieldTime+2*scaleTime+groupTime`,
`H = ListSnoc.snocTime overhead (16*W) S + ListSnoc.snocTime overhead (16*W) N`,
and `P` is the derived programming bound at width `15*w` and capacity `K`.
It includes both sampling executions, arithmetic, both appends, cache scans,
retained values, adapters and every control transition. Its runtime premises
are primitive/sampler and representation/control contracts, not assumed
efficiency of any completed signing component. Stored code is bounded by two
sampler descriptions, the used arithmetic/comparison primitives and
`2048*structuralAllowance+32`, independently of all runtime list lengths.
[Regressions](../SignaturesTest/BackendSchnorrAGMSigning.lean) cover distinct
challenge/response values, cached-zero collisions, shadowed entries, repeated
histories, preserved malformed/bad flags and the two-draw query tree. They check
standard transitive axioms and public resource-premise scope.

This is the internal `(g,pk,message,state)` interface. The observation map to
the source signing reply is a proof relation. Actual external request/reply
encoding, charging ignored coefficient rows and malformed-request dispatch
still belong to the complete handler/general-caller work.

Validation: `SignaturesTest.BackendSchnorrAGMSigning` passed (3391 jobs), and
`lake build Signatures SignaturesTest` passed (4166 jobs). The new declarations
have no warnings or nonstandard transitive axioms. All 436 local links in the
two edited guides resolve.

### Schnorr signing dispatch checkpoint, 2026-10-15

The [native dispatcher](../Signatures/Runtime/BackendSchnorrAGMSigningDispatch.lean)
accepts arbitrary incoming group lists and coefficient rows. A compiled
[emptiness scan](../Signatures/Runtime/BackendListEmpty.lean) selects the signing
core only when the group list is empty. It scans actual cells and charges the
retained request; it assumes no constant-time list inspection. Rejection creates
scalar zero and an empty group list, sets the malformed flag and preserves the
entire cache, histories and bad flag. Its full costed run is independent of the
scalar sampler. Acceptance constructs `(z,[R])` after the two-draw signing core.
The whole tuple/list reply and encoded state agree exactly with the source
handler for arbitrary request shapes.

[Representation bounds](../Signatures/Runtime/BackendSchnorrAGMSigningDispatchSize.lean)
charge all incoming groups and every coefficient row, including ignored values.
The [local costs](../Signatures/Runtime/BackendSchnorrAGMSigningDispatchLocalCost.lean)
and [complete budget](../Signatures/Runtime/BackendSchnorrAGMSigningDispatchBudget.lean)
derive scan, routing, branch, reply-construction and accepted-signing costs from
primitive, sampler, representation and control contracts. No completed-handler
efficiency premise is supplied. Stored code is bounded by two sampler
descriptions, the used primitive descriptions, and
`3072*structuralAllowance+64`, independently of runtime list lengths.

[Regressions](../SignaturesTest/BackendSchnorrAGMSigningDispatch.lean) cover rejected
nonempty groups, arbitrary ignored rows, sampler-independent rejection, accepted
reply layout, cached-zero collisions and chronological histories over infinite
`Nat` message labels. They check transitive axioms, finite-domain premises and
the absence of assumed completed-component efficiency in the public budget.
The tuple/list-to-source reply maps are proof relations; converting to the
caller's indexed interface still needs an implemented, charged adapter.

Validation: `lake build Signatures SignaturesTest` passed (4171 jobs), including
the new dispatch regressions. The new declarations have no warnings or
nonstandard transitive axioms. All 444 local links in the two edited guides
resolve. No proof-resource or transparency overrides were added.

### Schnorr randomness-handler checkpoint, 2026-10-15

[Dynamic uniform sampling](../Signatures/Runtime/BackendUniformSampling.lean)
composes implemented request encoding, one backend uniform query and implemented
reply decoding. Its input is a natural arity; it has no enumerated sampler table.
The exact denotation is `Fin.val` mapped over the source uniform query. Its
all-path budget is request conversion plus response conversion plus the external
query/control allowance, and four charged control transitions. Its code size is
the two adapter descriptions plus five, independent of the arity.

The [Schnorr random handler](../Signatures/Runtime/BackendSchnorrAGMRandom.lean)
scans incoming groups, retains or sets the malformed flag, performs that dynamic
query, and constructs an empty-group reply. It draws even on malformed requests.
The query tree and encoded state agree exactly with the source handler for
arbitrary group and coefficient lists. The source's `Fin (n+1)` reply is related
to its natural value; the final caller-index conversion remains to be installed.

[Size invariants](../Signatures/Runtime/BackendSchnorrAGMRandomSize.lean) preserve
cache, affine-basis and signed-message capacities, and include all ignored rows.
The [local costs](../Signatures/Runtime/BackendSchnorrAGMRandomLocalCost.lean) derive
the group scan, flag update and reply construction from compiled expressions.
The [complete bound](../Signatures/Runtime/BackendSchnorrAGMRandomBudget.lean)
adds actual query-interface conversions, the external query, value retention and
every control transition. Its only execution premises concern those local
encoding operations, the external query and backend structural contracts; it
does not assume efficiency of a completed handler or sampler. The arity affects
encoding and external-query contracts; there is no runtime loop proportional to
the domain cardinality. Stored code is bounded independently of runtime list
lengths and arity by the two query adapters and `2048*structuralAllowance+16`.

[Regressions](../SignaturesTest/BackendSchnorrAGMRandom.lean) check malformed
requests still drawing, arbitrary ignored rows, preserved flags and histories,
the singleton randomness domain, and a `2^128` arity using the same dynamic code.
They check standard transitive axioms and exclude finite-domain and assumed
completed-component-efficiency premises.

Validation: targeted random-handler regressions passed (3403 jobs), and
`lake build Signatures SignaturesTest` passed (4177 jobs). The new declarations
have no warnings or nonstandard transitive axioms. All 453 local links in the
two edited guides resolve. No proof-resource or transparency overrides were added.

### Schnorr indexed handler and caller checkpoint, 2026-10-15

The [native interface](../Signatures/Runtime/BackendSchnorrAGMInterface.lean)
encodes the actual explained source requests as random/hash/sign sums, retaining
every group and coefficient row. Request encoding and dependent reply tagging
have actual local backend realizers. Random tagging is total on encoded natural
replies and restores the original `Fin (n+1)` value on reachable samples. Its
conversion cost is a separate backend encoding obligation, not a free cast.

[Compiled component adapters](../Signatures/Runtime/BackendSchnorrAGMHandlerComponents.lean)
pass the generator/public key as represented common state, retain it across each
component and restore it afterward. Hash reply construction now creates the
empty group list explicitly. The
[installed dispatcher](../Signatures/Runtime/BackendSchnorrAGMHandler.lean)
branches over all three implemented handlers, retains the original request and
tags the returned reply with its full dependent source index. Its indexed-handler
view preserves the actual costed execution. Exact index matching makes the
proof-side decoding fallback unreachable.

[Source correspondence](../Signatures/Runtime/BackendSchnorrAGMHandlerSource.lean)
connects all requests and arbitrary adaptive general callers to the established
finite-list reduction, preserving joint output/state query trees and arbitrary
caller output types. The caller implementation/termination contract excludes
fuel cutoff; the executable runner still exposes cutoff rather than silently
replacing it with an output. No arithmetic-source certificate is required.

The [complete stored-code bound](../Signatures/Runtime/BackendSchnorrAGMHandlerDescription.lean)
derives the sizes of all installed components and adapters from primitive and
description contracts. It includes three copies of the scalar sampler, one
dynamic uniform-query implementation, the request encoder, all three reply
taggers, the used arithmetic instructions and `14000*structuralAllowance+256`.
The caller adds its actual initialization/head/update code, fuel description
and structural overhead. There is no table over messages, groups or random
arities. Composing runtime bounds for these adapters and recovering their input
and output widths from general attacker resources are still open.

[Regressions](../SignaturesTest/BackendSchnorrAGMHandler.lean) cover cached-zero
hashes with full request tags, malformed signing, dependent random replies for
all arities, signing followed by a hash of the returned commitment, shared cache
and histories, and zero-fuel terminal/cutoff behavior. They check standard
transitive axioms and reject finite-domain, arithmetic-attacker and assumed
whole-program budget premises in the public correspondence/description laws.

Validation: targeted handler regressions passed (3439 jobs), and
`lake build Signatures SignaturesTest` passed (4184 jobs). The new declarations
have no warnings or nonstandard transitive axioms. All 462 local links in the
two edited guides resolve. No proof-resource or transparency overrides were added.

The composed handler/caller runtime and general resource recovery are now proved.
Native final extraction, its complete runtime, the charged output adapter and
complete solver assembly are described below. The final checkpoint also combines
the runtime bounds into the whole-solver certificate and concrete security theorem.

### Schnorr measured caller resources, 2026-10-15

[Request recovery](../Signatures/Runtime/BackendSchnorrAGMRequestRecovery.lean)
derives data widths, group/row counts and every nested coefficient-row length
from the complete request encoding. Positive list-cell accounting bounds list
lengths; the additional [payload law](../Signatures/Runtime/BackendListPayload.lean)
bounds each stored row's encoding by its enclosing list. Both laws follow from
an additive list encoding with positive cell headers. Conversion may have an
explicit monotone size expansion; equal-size encodings give identity recovery.
The actual decoder and taggers retain their separately charged execution costs.

[Natural-value recovery](../Signatures/Runtime/BackendNatValue.lean) separates
random arity from encoded width. For binary encodings, width `b` permits values
up to `2^b - 1`. Conversely, all values in that range fit `b + header` encoded
units under the binary upper-size law. No polynomial numeric-arity premise or
iteration over that numeric range is added to the handler bound.

[Caller resource substitution](../Signatures/Runtime/BackendSchnorrAGMCallerResources.lean)
uses `RunsWithin` to derive reachable state/head sizes, bounded requests and
closure under every typed reply. It instantiates the native caller bound with
local allowance `work + 2*queries + 2` and conservative per-kind query allowance
`queries`. All handler costs remain derived from primitive and local port
contracts. No custom caller invariant, supplied `GeneralCaller.Budget`, finite
message/group universe or arithmetic attacker implementation is assumed.

[Return and termination laws](../Signatures/Runtime/BackendSchnorrAGMCallerOutput.lean)
transfer the measured head bound to the entire actual returned encoding, including
terminal readout at zero remaining fuel. Fuel at least the measured query bound
excludes cutoff and yields exact joint output/state correspondence with the
finite-list source execution. No extra termination certificate is required.

[Forgery recovery](../Signatures/Runtime/BackendSchnorrAGMOutputSize.lean)
then bounds the encoded forgery, message, scalar, group count, row count and every
row length, including malformed and unused rows. Output conversion may have an
explicit monotone size expansion; equal-size encodings again give identity
recovery. The following checkpoints implement and charge the actual output
adapter and final native extractor; complete solver assembly remains open.

[Regressions](../SignaturesTest/BackendSchnorrAGMResources.lean) cover ignored
signing rows, malformed final outputs, infinite natural message types and binary
arities reaching the full exponential range. They check transitive standard
axioms and reject finite-domain, supplied whole-program-budget and restricted
attacker premises, including in the contract record constructors.

Validation: targeted resource regressions passed (3466 jobs), and
`lake build Signatures SignaturesTest` passed (4203 jobs). The new declarations
have no warnings or nonstandard transitive axioms. All 480 local links in the
two edited guides resolve. No proof-resource or transparency overrides were added.

### Schnorr native final extraction, 2026-10-15

The original DLog solver returns the scalar component of `finish` and discards
its verification Boolean. The [scalar-projection theorem](../Signatures/Runtime/SchnorrAGMExtraction.lean)
proves exact joint scalar/state equality with that final step, and exact equality
of the resulting complete source solver. It preserves all random draws and
state updates. A read exposing the actual first cached entry agrees with the
original challenge read and proves that the returned entry is present in the
updated cache. This lets extraction reuse the entry without another cache scan.

The [native entry read](../Signatures/Runtime/BackendSchnorrAGMEntryRead.lean)
executes the existing setup, cache scan, fresh sampler and metadata retention,
then returns the full cached challenge/affine entry. Its
[complete budget](../Signatures/Runtime/BackendSchnorrAGMEntryReadBudget.lean)
derives runtime from primitive contracts and the scalar sampler, with no completed
read-budget premise. Both histories and the malformed flag are preserved on all
encoded inputs; hits preserve the entire costed run when the sampler changes.

The [full native extractor](../Signatures/Runtime/BackendSchnorrAGMExtraction.lean)
scans both final group and coefficient-row lists, retains the response scalar,
flattens the decoded coefficients against the chronological basis, reads once,
and computes `(z - constant) / (secret + challenge)` when an explanation exists.
Absent explanations return zero, including a signing entry shadowing a later
explained entry. Rejected output shapes return zero and preserve the entire
state, without sampling. The exact source theorem includes the updated cache
and bad-event flag, including zero denominators and previously unseen targets.

[Local adapter costs](../Signatures/Runtime/BackendSchnorrAGMExtractionLocalCost.lean)
charge initial rearrangement, rejection, the field operations and retained state.
The [complete decoded-path bound](../Signatures/Runtime/BackendSchnorrAGMExtractionDecodedBudget.lean)
is the existing flatten/read budget plus `3*fieldTime + divisionTime +
1031*overhead(1024*Hash.frameWidth(w,K,L,H))`. The full
[stored-code bound](../Signatures/Runtime/BackendSchnorrAGMExtractionDescription.lean)
includes the scalar sampler, every used primitive, both singleton scans, adapters
and branch bodies; it is independent of runtime list lengths and message domains.

[Regressions](../SignaturesTest/BackendSchnorrAGMExtraction.lean) exercise first
cached explanations, shadowed entries, absent explanations with nonzero unused
slots, malformed outputs preserving state, fresh targets and exceptional
denominators over infinite natural message labels. They check transitive standard
axioms and exclude finite-domain or assumed completed-component efficiency.

The following checkpoints complete the outer shape-dispatch runtime, actual
source-output conversion and solver assembly, including setup/cutoff/projection
budgets. The final checkpoint completes the combined runtime certificate and
concrete security endpoint. Public statement and family packaging remain open.

Validation: targeted extraction regressions passed (3419 jobs), and
`lake build Signatures SignaturesTest` passed (4213 jobs). The new modules and
regressions have no warnings, admissions, nonstandard transitive axioms or
proof-resource/transparency overrides. All 492 local links in the two edited
guides resolve. The decoded composition uses a generic body lemma so Lean can
reuse component proofs within its normal limits; the public bound derives that
body's budget from primitives and the scalar sampler.

### Schnorr complete extraction overhead and output conversion, 2026-10-15

[Final-output frame bounds](../Signatures/Runtime/BackendSchnorrAGMExtractionSize.lean)
cover the full encoded forgery, both shape lists, every coefficient row, the
retained response and the entire state. Rejection returns zero with the original
state; it does not use the hash handler's malformed-state update.
[Routing budgets](../Signatures/Runtime/BackendSchnorrAGMExtractionRoutingBudget.lean)
charge initial rearrangement, both singleton scans, response retention and
rejection. The [complete native runtime theorem](../Signatures/Runtime/BackendSchnorrAGMExtractionBudget.lean)
then composes the decoded extractor with these stages and sum distribution.
Writing `W = HashDispatch.frameWidth(w,K,H,G,R,L)` and
`fee = overhead(4096*W)`, the bound is
`prepareTime(overhead,W,G,R,pointZeroTime) +
max(decodedTime, fieldTime + 261*fee) + 271*fee`.
This is a bound on the actual full code for every shape, derived from primitive,
scalar-sampler, encoding and control-operation contracts. No finished-extractor
budget is supplied.

[Extraction input recovery](../Signatures/Runtime/BackendSchnorrAGMExtractionResources.lean)
derives the input contract from the full output encoding and the proved caller
store invariant. Positive-cell and payload encoding laws bound all group
payloads, group/row counts and row lengths. Combining caller width and recovered
output width uses their maximum; the existing history bound is preserved. No
separate attacker-output length assumptions or finite message domain are needed.

The [executable output adapter](../Signatures/Runtime/BackendSchnorrAGMSolverOutput.lean)
uses an actual backend realizer for `encodeForgery`, drops the public configuration,
and retains the entire private state. It preserves every group and coefficient
row, including surplus or malformed data. Its complete runtime is at most
`adapterTime + 9*overhead(32*width)`, with stored code at most
`localSize(convert) + 5*allowance + 4`. Only the local representation conversion's
cost and encoded-size expansion are contractual; all wrapper/control costs are
derived. A proof-level encoding equality is not treated as executable conversion.

The extraction regressions now also cover this actual output adapter preserving
surplus rows and private state. Axiom and premise guards include the complete
extraction bound, input recovery and adapter budgets.

The following checkpoint assembles the complete solver and derives its stored-code,
setup, cutoff and projection bounds. The subsequent resource checkpoint completes
runtime certification and application of the original probability/hardness theorem.
The short public/family endpoints remain open.

Validation: targeted extraction regressions passed (3480 jobs), and
`lake build Signatures SignaturesTest` passed (4218 jobs). The new modules and
regressions have no warnings, admissions, nonstandard transitive axioms or
proof-resource/transparency overrides. All 499 local links in the two edited
guides resolve.

### Schnorr complete solver assembly and initialization, 2026-10-15

The [native solver](../Signatures/Runtime/BackendSchnorrAGMSolver.lean) now represents
the complete execution: construction of the initial `[(1,0),(0,1)]` basis and
empty cache/history, the actual input adapter, the general caller, optional-output
inspection, cutoff, actual output conversion, extraction and scalar projection.
The initial basis is built by charged instructions. The boundary uses implemented
local adapters for initial input, returned forgery and optional-result inspection.

[Exact source correspondence](../Signatures/Runtime/BackendSchnorrAGMSolverCorrectness.lean)
connects this whole program to the named finite-list DLog reduction. The caller's
measured resource bound supplies sufficient fuel, and its implementation law
identifies the source adversary. There is no arithmetic-source attacker premise
or assumed complete-solver budget. Cutoff skips extraction: changing the extractor
leaves the entire costed cutoff run unchanged.

The [complete stored-code bound](../Signatures/Runtime/BackendSchnorrAGMSolverDescription.lean)
includes the attacker's initialization/head/update code, four stored sampler
copies, all local adapters and primitives, fuel, and
`23000*structuralAllowance + 512`. It contains no message-domain enumeration.
[Initialization costs](../Signatures/Runtime/BackendSchnorrAGMSolverLocalCost.lean)
derive the empty-state capacity invariant and charge all basis constructors.
The [complete setup bound](../Signatures/Runtime/BackendSchnorrAGMSolverSetup.lean)
is `4*fieldTime + adapterTime + 1028*overhead(1024*setupWidth)`, where
`setupWidth = inputWidth + routeWidth + 64*width`. It includes the input conversion,
state retention and control costs. Cutoff costs at most
`fieldTime + 3*overhead(32*width)` and final projection at most
`2*overhead(32*width)` under their represented input-width contracts.

[Regressions](../SignaturesTest/BackendSchnorrAGMSolver.lean) check initial public-input
and basis order, empty histories/flags, cutoff, and successful extraction from
the first cached explanation even when the discarded verification Boolean is
false. They use infinite natural message labels and guard the transitive axioms
and absence of finite-domain, restricted-attacker or completed-budget premises.

The following checkpoint composes the terminal and complete solver runtime,
constructs the `Within` witness and applies DLog hardness. The short public and
polynomial-family endpoints remain open. The semantic equality and stored-code
bound alone were not used to infer runtime efficiency.

Validation: targeted solver regressions passed (3479 jobs), and
`lake build Signatures SignaturesTest` passed (4224 jobs). The new modules and
regressions have no warnings, admissions, nonstandard transitive axioms or
proof-resource/transparency overrides. All 510 local links in the two edited
guides resolve.

### Schnorr complete native resource certificate and concrete security, 2026-10-15

[Local solver port contracts](../Signatures/Runtime/BackendSchnorrAGMSolverPorts.lean)
cover actual input, output and optional-result adapters. The
[output adapter bound](../Signatures/Runtime/BackendSchnorrAGMSolverOutput.lean)
now distinguishes source return width, native forgery width and retained-state
width. It never extends a conversion-cost assumption beyond the reachable source
width. [Extraction input recovery](../Signatures/Runtime/BackendSchnorrAGMExtractionResources.lean)
also works directly from private state after dropping the public configuration,
preserving the original history bound and every returned coefficient row.

[Terminal composition](../Signatures/Runtime/BackendSchnorrAGMSolverTerminalComposition.lean)
charges actual output conversion, extraction, projection, optional-result
inspection, state retention, distribution and cutoff. The
[complete terminal theorem](../Signatures/Runtime/BackendSchnorrAGMSolverTerminalBudget.lean)
instantiates its extraction budget from primitive, encoding and scalar-sampler
contracts. If `E=max(width,outputWidth)` and `H=historyWidth(width,N,S)`, then
`terminalWidth = width + outputWidth + routeWidth + (60*K+4*N+2*S+27)*width +
Read.frameWidth(3*E,K,H)`. Terminal time is the derived full extraction time at
width `E`, plus `fieldTime + 2*adapterTime + 23*overhead(4096*terminalWidth)`.
Both successful return and cutoff are covered.

The [whole-solver bound](../Signatures/Runtime/BackendSchnorrAGMSolverBudget.lean)
is setup time plus the resource-derived caller time plus terminal time plus
`2*overhead(32*programWidth)`, where
`programWidth=4*(inputWidth+routeWidth+terminalWidth)`.
The caller's returned width follows from its measured head-size bound, rather
than a new assumption on the final forgery. Its local work and query counts are
charged through the established general-caller theorem. No complete handler,
extractor or solver budget is supplied as an efficiency premise.

The [uniform stored-code bound](../Signatures/Runtime/BackendSchnorrAGMSolverDescription.lean)
is `callerCode + 4*samplerCode + 2*randomPortSize + 4*handlerPortSize +
3*solverPortSize + 49*instructionSize + fuel + 23000*allowance + 512`.
Here `callerCode` charges initialization, two head copies and update code.
The [backend resource witness](../Signatures/Runtime/BackendSchnorrAGMSolverWithin.lean)
combines the derived time and code bounds with exact semantics of the named
finite-list DLog reduction at every input. Sufficient measured query fuel excludes
cutoff when connecting to the source adversary. The code and its model are fixed
across challenges.

[DLog resource accounting](../Signatures/Runtime/BackendSchnorrAGMDLog.lean)
requires every `(g,x*g)` challenge to fit the input cap; the pair's encoded size
is at most `2*groupWidth+unitWidth+2*header`.
The [concrete security theorem](../Signatures/Runtime/BackendSchnorrAGMSecurity.lean)
constructs the witness, supplies it to DLog hardness in that same backend class,
and concludes the original bound
`epsilon + (qH+1)/|F| + qS*(qS+qH)/|F|` for the original AGM game.
Arbitrary message types and the source algebraicity condition are preserved.
The only explicit finiteness premise in this endpoint concerns the scalar field.

The [solver regressions](../SignaturesTest/BackendSchnorrAGMSolver.lean) now guard
all new resource/security endpoints for standard transitive axioms, arbitrary
message domains and absence of restricted-source or assumed-complete-budget
premises. Existing semantic regressions cover cutoff, initial state and first
cached explanations. The short public theorem, polynomial closure and family
corollary remain open, along with the separate general ROM work below.

Validation: targeted solver regressions passed (3513 jobs), and
`lake build Signatures SignaturesTest` passed (4228 jobs). The new modules and
regressions have no warnings, admissions, nonstandard transitive axioms or
proof-resource/transparency overrides. All 525 local links in the two edited
guides resolve.

### Schnorr public AGM statement, 2026-10-15

[`Schnorr.agm_security`](../Signatures/Schnorr/Statement.lean) now takes the four
requested inputs: curve, security parameter, query allowances and algebraic
adversary. It displays the actual EUF-CMA probability bounded by the DLog success
supremum at the derived reduction time, plus `(qH+1)/|F| + qS*(qS+qH)/|F|`.

- [`CyclicCurve`](../Signatures/Model/CyclicCurve.lean) supplies one scalar field,
  one group and a generator at each parameter. It has no pairing requirements.
- [`GeneralAGMParameters`](../Signatures/Schnorr/GeneralAGMParameters.lean) fixes
  primitive/encoding/backend contracts and attacker resource limits. The attacker
  supplies general backend code realizing the source on all inputs, its own
  execution/code bounds, and query allowances. No finished-reduction budget is assumed.
- [`reduction_within`](../Signatures/Schnorr/Proofs/GeneralAGM.lean) derives
  challenge-size, whole-program runtime and stored-code bounds. It uses measured
  caller work and query-dependent cache/history capacities, with no finite message domain.
- [`GeneralSecurityModel`](../Signatures/Schnorr/GeneralSecurityModel.lean) writes
  out the game and DLog supremum. The [public proofs](../Signatures/Schnorr/Proofs/GeneralSecurity.lean)
  establish exact source-game equality, public query allowances, the security
  inequality and monotonicity in the DLog time allowance.
- The existing certified arithmetic-source ROM theorem retains its name and is
  re-exported from [`ArithmeticStatement`](../Signatures/Schnorr/ArithmeticStatement.lean).
- [Regression guards](../SignaturesTest/SchnorrGeneralStatement.lean) check the
  public argument shape, proof locations, transitive axioms, explicit game and
  hardness terms, and absence of pairing, finite message-domain, arithmetic-attacker
  or assumed completed-solver premises.

The polynomial-family closure/corollary remains open. General ROM replay and the
nonzero-nonce variant also remain separate; this checkpoint does not claim those results.

Validation used one direct Lean process at a time with `-j1 -M8192` and the
package's implicit-variable settings. All new modules, the public regression
test, existing `SchnorrReduction` and `StatementAssumptions` tests, and the
aggregate `Signatures` import passed without warnings. The full parallel Lake
build was not rerun after the machine's memory-pressure crashes. All 550 local
links in the README and the two edited guides resolve.

### Schnorr AGM polynomial family, 2026-10-15

[`BackendSchnorrAGMPolynomial`](../Signatures/Runtime/BackendSchnorrAGMPolynomial.lean)
now proves polynomial growth of the actual complete runtime and stored-code
formulas. Component lemmas cover flattening, cache reads, hashing, extraction,
the full handler and the terminal before assembling the whole solver result.
Each component resource has a fixed polynomial across parameters; structural
overhead is jointly polynomial in the parameter and encoded frame size.

[`GeneralAGMFamilyResources`](../Signatures/Schnorr/GeneralAGMFamilyResources.lean)
derives total/measured query bounds, complete solver time/code polynomiality and
the native nonuniform executable witness. Only caller work, query allowances,
encoding widths, primitive/sampling/adapter prices and component descriptions
are polynomial premises. The numerical random arity and message-domain size
are absent. Equality of the full backend configuration fixes execution,
random-query costs and description accounting across the family.

The [hardness class](../Signatures/Runtime/BackendSchnorrAGMDLogFamily.lean)
covers all polynomial-time, polynomial-code solver families in that same backend.
Every challenge fits the input cap; one program per parameter handles all inputs.
The [family statement](../Signatures/Schnorr/GeneralAGMFamilyStatement.lean), with
its [separate proof](../Signatures/Schnorr/Proofs/GeneralAGMFamily.lean), concludes
negligible forgery under this DLog hardness and negligible inverse field size.
The two original losses, `(qH+1)/|F|` and `qS*(qS+qH)/|F|`, are proved negligible
using the query polynomials. Fields, groups and arbitrary message types can vary
with the parameter; no uniform program generator is asserted.

[Regression guards](../SignaturesTest/SchnorrAGMFamilies.lean) check the standard
transitive axiom footprint, fixed-backend hardness and family convention,
absence of finished-solver efficiency or polynomial-raw-arity premises, separate
proof/statement locations and preservation of the actual source game. A zero-query
regression retains setup/terminal costs and verifies polynomial closure.

Schnorr AGM's agreed conditional-backend route is complete. General Schnorr ROM
replay and its nonzero-nonce extension remain open as listed below.

Validation: all five new source modules and `SchnorrAGMFamilies` passed, along
with the existing `SchnorrGeneralStatement` regressions and the aggregate
`Signatures` import. Checks used one direct Lean process at a time with
`-j1 -M8192`, package implicit-variable settings and default proof limits.
The modules are warning-free, with no admissions or nonstandard axioms.
All 674 local links in the four edited Markdown guides resolve.

### General Schnorr lazy-tape checkpoint, 2026-10-15

[SchnorrLazySeed](../Signatures/Runtime/SchnorrLazySeed.lean) implements a
finite saved tape plus a consumable remaining tape. Each family consumes its own
next saved reply; a miss makes one ambient query and appends the answer to the
saved tape. The implementation inspects encountered cells only. There is no
advance family enumeration, finite-domain premise or arithmetic caller syntax.
Reset changes the chosen family's prefix/replacement and preserves every other
family, including private draws after the first run's changed challenge.

The projection to the existing typed seeded oracle is exact for an arbitrary
adaptive computation. [The first-pass recording law](../Signatures/Runtime/SchnorrLazySeedLog.lean)
also preserves the joint output and full chronological tape, not only the output
marginal. Its two-pass identity expresses the implemented joint outputs as
first-run logging followed by typed seeded replay of that encountered-path tape.
[Cell/query bounds](../Signatures/Runtime/SchnorrLazySeedBounds.lean)
give at most `q1 + q2 + 1` saved cells and `q1 + 1` remaining cells after two
passes, and at most `q1 + q2` ambient calls. The replacement is supplied to this
two-pass component: its sampling cost must be added by the fork controller.
These are cell counts, not encoded memory or execution-time certificates.

[Regression checks](../SignaturesTest/SchnorrLazySeed.lean) cover private caller
and simulator draws after the fork, a newly encountered sampling family in the
second run, an exhausted family's fresh suffix, a large numerical random range,
empty passes, and the standard axiom footprint. The later complete lazy-fork
checkpoint proves joint probability equality with the pregenerated fork.
Native codecs/costs and general-caller integration remain required.

Validation: all three new modules, the new lazy-tape regression, the existing
`SeedTape` regression and the aggregate `Signatures` import passed serially with
`-j1 -M8192` and default proof limits. No warnings, admissions or nonstandard
axioms were introduced; all 680 local links in the four status guides resolve.

### Joint deferred-sampling checkpoint, 2026-10-15

[SeededDeferredStep](../Signatures/Runtime/SeededDeferredStep.lean) factors a
requested dependent-family reply out of a full generated seed while preserving
the entire residual seed. [SeededDeferred](../Signatures/Runtime/SeededDeferred.lean)
extends this to arbitrary covered adaptive computations: unused entries may be
sampled independently after the run, with their remaining capacities determined
by the actual requests. Its capacity tracker erases exactly to the live source
computation and is proof instrumentation only.

[SeededTrace](../Signatures/Runtime/SeededTrace.lean) reconstructs the original
covered seed from the consumed transcript and unused entries.
[SeededDeferredTrace](../Signatures/Runtime/SeededDeferredTrace.lean) combines
these facts into a joint law whose continuation receives the output, complete
transcript and original seed. This retains the correlations needed by rewinding.
It does not infer a two-run law from a first-run output marginal.

[SeededSuffix](../Signatures/Runtime/SeededSuffix.lean) separates recorded
prefixes from unused suffixes after a selected slot inside the recorded prefix.
[SeededSuffixSampling](../Signatures/Runtime/SeededSuffixSampling.lean) then
removes independent unused entries from the replay's sampling, including families
first visited in the second run and the erased suffix of the changed family.
The family list and generated unused entries occur only in the probability
proof; the lazy implementation still stores encountered cells only.

The distribution statements use the native measure interpretation.
[SeededMeasure](../Signatures/Runtime/SeededMeasure.lean) explicitly transports
the pinned library's discrete proof identities to that interpretation.
[Regressions](../SignaturesTest/SeededDeferred.lean) check an adaptive choice of
sampling family, joint observation of an unused value, untouched families,
native measure specialization, the standard axiom footprint and absence of a
finite-family-universe requirement.

Validation: all seven new source modules, the new regression, the existing
`SchnorrLazySeed` and `SeedTape` regressions and the aggregate `Signatures` import
passed serially with `-j1 -M8192` and default proof limits. No warnings,
admissions or nonstandard axioms were introduced. All 690 local links in the
four status guides resolve.

The following checkpoint completes the controller composition and valid-slot
bridge. Named security transport and native general-caller/code/encoding costs
remain open.

### Complete lazy-fork distribution checkpoint, 2026-10-15

[SeededDeferredContinuation](../Signatures/Runtime/SeededDeferredContinuation.lean)
eliminates unused seed generation under a continuation law on supported first
transcripts, then erases the proof-only capacity counter. Its reset corollary
preserves arbitrary first-run information observed by a second computation.

[SeededLazyFork](../Signatures/Runtime/SeededLazyFork.lean) proves equality of the
complete pregenerated and recorded fork distributions. The proof handles a
missing selector, independent replacement sampling, comparison with the original
selected answer, reset, and agreement of the second selector. The strict bound
on the selected slot ensures that the old answer is determined by the log.
It preserves both outputs jointly and does not assume independence of the runs.

[SeededForkReachability](../Signatures/Runtime/SeededForkReachability.lean) derives
that strict bound from `PathCfReachable`, already used by Schnorr's extraction
proofs. Every supported transcript is the erasure of an intrinsic execution path.

[SchnorrLazyFork](../Signatures/Runtime/SchnorrLazyFork.lean) supplies the complete
finite-list controller. Its encoded first transcript is exactly the reconstructed
typed seed; reset and replay refine the recorded controller by computation equality.
The resulting `fork_eq_seeded` theorem gives native measure equality with the
reference fork. The implementation stores encountered cells only; the finite
family list appears solely in the reference experiment and its proof premises.
Both private families retain post-fork first-run draws. No numeric family-range
enumeration, restricted source syntax, or finite oracle-family universe is added.

[Regressions](../SignaturesTest/SeededLazyFork.lean) cover adaptive branching into
a family first visited on replay, unchanged-answer rejection, the finite-list
codec, native measure interpretation and the standard axiom footprint.
This is a probability/representation result, not a native runtime or bit-memory
certificate. The named Schnorr security endpoint still needs transport through
extraction, and general-caller/native cost integration remains open.

Validation: all four new source modules, the new complete-fork regression,
the existing `SeededDeferred`, `SchnorrLazySeed` and `SeedTape` regressions, and
the aggregate `Signatures` import passed serially with `-j1 -M8192` and default
proof limits. No warnings, admissions or nonstandard axioms were introduced.
All 574 local links in the two updated guides resolve; `git diff --check` passes.

### Named lazy Schnorr security checkpoint, 2026-10-15

[LazyROMReduction](../Signatures/Schnorr/LazyROMReduction.lean) defines the named
lazy DLog solver. It records only encountered randomness, resets at the selected
challenge, retains private suffixes, and uses the established special-soundness
extractor. Neither a family cover nor a private-query capacity is a program input.

[LazyFork](../Signatures/Schnorr/Proofs/LazyFork.lean) instantiates the complete
joint fork law with the same `qH + 1` selectable slots as the fixed-tape theorem.
It deduplicates the proof-only cover without changing its membership-based bound
and derives valid selection from the existing reachability theorem.
[LazySampling](../Signatures/Schnorr/Proofs/LazySampling.lean) explicitly proves
native measure correspondence for the final uniform interpretation.

[LazyROM](../Signatures/Schnorr/Proofs/LazyROM.lean) transports that law through
extraction and the full key-averaged DLog experiment. `LazyROM.security` preserves
the original source game's signing-simulation loss and fork denominator. It adds
no finite/countable-message premise and no source-language certificate. The
proof uses singleton laws for atomic computations, avoiding an unjustified
discreteness assumption on products containing arbitrary messages or caches.

At this checkpoint the reference experiment still required a supplied
finite-family/path bound. The next checkpoint derives that premise. Connecting
the raw two-family computation to the typed finite-list runner and complete
native costs/general-caller composition remain open.

[Regressions](../SignaturesTest/SchnorrLazyROM.lean) check an adaptive replay into
a previously unused private family, duplicate cover entries, native measure
interpretation, arbitrary-message scope, the named source/target experiments,
absence of proof-cover inputs to the program, and the standard three axioms.

Validation: all four source modules, the new `SchnorrLazyROM` regression, the
existing `SeededLazyFork` and `SchnorrFixedTape` regressions, and the aggregate
`Signatures` import passed serially with `-j1 -M8192` and default proof limits.
The new files produce no warnings; the existing fixed-tape test retains its
deprecated `probEvent` notation warning. All 582 local links in the two updated
guides resolve, and `git diff --check` passes.

### Derived reference cover and simpler ROM probability endpoint, 2026-10-15

[FiniteQueryCover](../Signatures/Runtime/FiniteQueryCover.lean) proves that a
terminating oracle computation with finite reply types has a finite family cover
and a finite per-family query bound. The oracle-family universe may be infinite.
The proof combines the finitely many continuation branches at each node; a
second lemma combines finitely many input-indexed computations. A coordinate
replacement lemma retains a sharper independently proved bound for one family.

[LazyQueryBounds](../Signatures/Schnorr/Proofs/LazyQueryBounds.lean) derives the
actual `qH + 1` challenge bound from signing/hash allowances, the CMA-to-NMA
simulation and the final verifier query. Finite scalars and a generating point
imply finitely many public keys, so the generic cover lemma supplies one cover
for all keys. Replacing its challenge coordinate yields exactly the bound used
by the fixed-tape reference theorem.

Consequently [LazyROM.security](../Signatures/Schnorr/Proofs/LazyROM.lean) now
requires only the ordinary source adversary and signing/hash allowances, beside
the field/group and generating-point assumptions. It preserves the same source
game, named lazy reduction and probability inequality. The earlier intermediate
theorem remains available as `security_of_seed_bound`. No private-family list,
private-query capacity, arithmetic source certificate or finite-message premise
is needed at the main endpoint.

This is a proof-only existence argument. It does not run the cover construction,
bound its size polynomially, or supply the native runtime certificate still
needed for the general efficient-attacker endpoint. The executable is unchanged.
The [regression](../SignaturesTest/SchnorrLazyROM.lean) applies the complete bound
to a private-only attacker over messages `Nat → Bool`, with adaptively selected
million-sized sampling arities and zero hash/sign calls. Guards reject additional
seed-cover premises, finite/countable-message requirements and nonstandard axioms.

Validation: both new proof modules, the updated lazy security module, the
expanded `SchnorrLazyROM` regression and the aggregate `Signatures` import passed
serially with `-j1 -M8192` and default proof limits, without warnings or admissions.
The regression checks only the standard three axioms. All 587 local links in the
updated guides resolve; `git diff --check` passes.

### Raw finite-list runner and native dynamic private draws, 2026-10-15

[SchnorrRawTape](../Signatures/Runtime/SchnorrRawTape.lean) reuses the existing
cell lists, scan and reset operations for precisely the raw two-family interface
of `LazyROM`. It proves the complete first-run output/tape law, exact seeded
replay and reset correspondence. Caller and simulator uniform draws remain in
their original families and order; the proof does not assume that splitting or
expanding a private family commutes with a fork.

[SchnorrRawFork](../Signatures/Runtime/SchnorrRawFork.lean) implements the full
finite-list controller. `fork_eq_lazy` and `dlogReduction_eq_lazy` are computation
equalities, including selection, fresh sampling, collision rejection, both runs,
second-selection agreement and extraction. `RawTape.security` therefore inherits
the named theorem without additional attacker or private-seed premises.

[SchnorrRawTapeValid](../Signatures/Runtime/SchnorrRawTapeValid.lean) proves that
recorded private naturals fit their requested sampling ranges, and that draws,
simulation and reset preserve this invariant. A valid hit can return the stored
natural directly instead of running an arity-specific decoder.

[BackendSchnorrRawUniform](../Signatures/Runtime/BackendSchnorrRawUniform.lean)
implements a native private draw from compiled expressions, structural code and
the existing dynamic uniform sampler. The arity is an input value. The program
computes its tag, scans encountered cells, returns and consumes a hit, or samples
and appends a fresh reply. Its theorem preserves the full saved/remaining state
on valid tapes. Its stored description is derived from the actual expression
bodies and interface adapters, independently of input arity and tape length.
This is not yet a native runtime or encoded-memory certificate for the whole
reduction: challenge handling, complete caller/controller assembly and their
resource proofs remain open.

[Regressions](../SignaturesTest/SchnorrRawTape.lean) preserve two post-challenge
private draws in the same family and their order, check reset validity and
million-sized dynamic hit/miss/append behavior, and guard computation equality,
native probability semantics, arbitrary messages and the standard three axioms.

Validation: all four new source modules, the new `SchnorrRawTape` regression,
the existing `SchnorrLazyROM` regression and the aggregate `Signatures` import
passed serially with `-j1 -M8192` and default proof limits. No new warnings,
admissions, nonstandard axioms or proof-option overrides were introduced.
All 597 local links in the updated guides resolve; `git diff --check` passes.

### Raw tape capacities, encoded sizes and native return/save costs, 2026-10-15

[SchnorrRawTapeBounds](../Signatures/Runtime/SchnorrRawTapeBounds.lean) derives
single-draw and adaptive-run saved/remaining capacities and live-query bounds.
A first pass with at most `q₁` requests stores at most `q₁` cells. After reset
and a second pass with at most `q₂` requests, the saved list has at most
`q₁ + q₂ + 1` cells and the remaining list at most `q₁ + 1`. The replacement
challenge and both lists are counted. These are cell/query counts, separately
from encoded size and execution time.

[SeedTapeCellBounds](../Signatures/Runtime/SeedTapeCellBounds.lean) proves that
pop/trim return sublists and successful pop replies come from the input tape.
[BackendSchnorrRawUniformSize](../Signatures/Runtime/BackendSchnorrRawUniformSize.lean)
uses these facts to preserve per-cell natural/field encoding bounds through
prepare, hit, save, reset and the actual native draw program. A state with
capacities `s` and `r` has encoded size at most `(6*(s+r)+3)*width`, under
the ordinary header/product/list encoding laws. Every copy in the two lists is
counted. Native size preservation does not need validity of recorded private
values; the separate source-correspondence theorem still requires that invariant.

[BackendSchnorrRawUniformLocalCost](../Signatures/Runtime/BackendSchnorrRawUniformLocalCost.lean)
derives the actual hit-return and chronological-save runtime bounds. The save
proof uses the charged append implementation, including both reversals and the
entire retained input, and charges fresh-cell construction and structural routing.
It assumes primitive/data/structural contracts, not a completed adapter budget.
The result depends on encoded widths, saved/remaining capacities and zero's
primitive cost, with no enumeration or linear dependence on numeric arity.

At this checkpoint, the complete native scan, draw budget, challenge/reset controller and general
caller/solver runtime certificates remained open. These local cost and encoded-size
results do not establish a whole-reduction runtime or peak-memory certificate.

[Regressions](../SignaturesTest/SchnorrRawTape.lean) now include a private arity
chosen adaptively between `2^64` and `1`, with two-request and two-pass capacity
bounds. They check the standard three axioms for the new bounds and reject
completed-adapter/expression cost premises or numeric-arity parameters in the
save-time formula.

Validation: all four new source modules, the expanded `SchnorrRawTape`
regression and the aggregate `Signatures` import passed serially with `-j1
-M8192` and default proof limits. No warnings, admissions, nonstandard axioms
or proof-option overrides were introduced. All 605 local links in the updated
guides resolve; `git diff --check` passes.

### Complete native private-draw runtime and polynomial closure, 2026-10-15

[BackendSeedTapeScanCost](../Signatures/Runtime/BackendSeedTapeScanCost.lean)
proves native runtime bounds for the original tape scan in an arbitrary trailing
context. Its expression aliases are definitionally equal to the existing weakened
scan; no replacement implementation is assumed. The remaining-input invariant
reserves capacity for the growing accumulator. The proof charges every fold
iteration and fee, the retained original list and context, default creation,
the final reversal and result assembly.

[BackendSchnorrRawUniformPrepareCost](../Signatures/Runtime/BackendSchnorrRawUniformPrepareCost.lean)
instantiates that scan with the full original input, including both saved and
remaining tapes. Tag computation, expression framing, hit/miss selection and
prepared-state assembly are charged from primitive and data/structural laws.

[BackendSchnorrRawUniformBudget](../Signatures/Runtime/BackendSchnorrRawUniformBudget.lean)
composes preparation, selection, hit return, dynamic uniform sampling, retention,
chronological append and every control fee into `NativeUniform.bound`. This is
an all-path `Bounds` certificate for the actual `NativeUniform.code`. It preserves
encoded output/state bounds, allowing at most one additional saved cell and no
remaining-tape growth. Its assumptions concern primitive operations, representation
and control laws, and the uniform query's request/reply adapters and sampling cost.
No completed scan, expression, sampler wrapper or handler budget is assumed.

[BackendSchnorrRawUniformPolynomial](../Signatures/Runtime/BackendSchnorrRawUniformPolynomial.lean)
proves polynomial closure of that actual runtime formula from polynomial encoded
widths, tape capacities and component times, with one joint polynomial structural
overhead bound. Numeric arity does not occur in the formula and need not grow
polynomially. The concrete theorem still requires width and primitive/port cost
bounds for the reachable numeric range. This is a component efficiency theorem,
not a full Schnorr ROM family security endpoint or conventional-machine instance.

[Regression guards](../SignaturesTest/SchnorrRawTape.lean) check the original
scan's equality in any retained context, the standard three axioms for all new
proofs, the all-path native-program conclusion, absence of completed-component
budget premises, and absence of numeric-arity parameters in the runtime formulas.

Validation: all four new source modules, the expanded `SchnorrRawTape`
regression and the aggregate `Signatures` import passed serially with
`-j1 -M8192` and default proof limits, without warnings, admissions, nonstandard
axioms or proof-option overrides. All 613 local links in the updated guides
resolve; `git diff --check` passes.

### Complete native challenge draws, 2026-10-15

[BackendSchnorrRawChallenge](../Signatures/Runtime/BackendSchnorrRawChallenge.lean)
implements the other raw tape family. It scans for tag `1`, consumes the first
recorded challenge on a hit, or executes scalar-sampling code and appends that
exact field value on a miss. Both saved and remaining lists appear in its exact
source-correspondence theorem. The sampler is interpreted after raw tape handling;
the implementation does not split or expand the replayed private families.
Its stored-code bound includes the sampler's whole program and all handler code.

[BackendSchnorrRawChallengeSize](../Signatures/Runtime/BackendSchnorrRawChallengeSize.lean)
reuses the private handler's cell/list/state invariants, preserving each tape's
width and capacity separately. It derives the prepared/output sizes and at most
one additional saved cell. Challenge source correspondence needs no natural-reply
validity assumption because the returned payload is already a field value.

[BackendSchnorrRawChallengeCost](../Signatures/Runtime/BackendSchnorrRawChallengeCost.lean)
charges the scan with the full original state retained, chronological append's
two reversals, framing and reply assembly. Appending a challenge uses data
constructors and copies; its public save-cost theorem needs no supplied primitive
cost certificate. Preparation separately charges comparisons and the default zero.

[BackendSchnorrRawChallengeBudget](../Signatures/Runtime/BackendSchnorrRawChallengeBudget.lean)
composes these costs with hit return, scalar sampling, retention, miss adapters
and every control fee into an all-path bound for the actual challenge handler.
The assumed sampler budget belongs to the supplied scalar-sampling code, not to
the completed tape handler. Polynomial closure of the derived runtime formula
follows from encoded widths, tape capacities, primitive/sampler times and joint
structural overhead. The following checkpoint completes native reset;
controller and full general-caller/solver certificates remain open.

[Regressions](../SignaturesTest/SchnorrRawTape.lean) check interleaved challenge
and private cells, first-challenge consumption, preservation of the later
challenge and saved transcript, miss behavior and chronological field append.
Guards check computation equality, the standard three axioms, complete native
runtime conclusions, absence of completed-handler cost premises, and that the
only assumed component `Bounds` certificate is for the supplied scalar sampler.

Validation: all four new source modules, the expanded `SchnorrRawTape`
regression and the aggregate `Signatures` import passed serially with
`-j1 -M8192` and default proof limits, with no warnings, admissions, nonstandard
axioms or proof-option overrides. All 620 local links in the updated guides
resolve; `git diff --check` passes.

### Complete native reset, 2026-10-15

[BackendSeedTapeResetCost](../Signatures/Runtime/BackendSeedTapeResetCost.lean)
derives native runtime for the existing trim/reset expression under any retained
context. The forward fold reserves one input cell per iteration and bounds the
growing accumulator, while the remaining challenge counter only decreases.
Each iteration charges tag and counter comparisons, subtraction when used,
construction and control. The final reversal and replacement insertion are
charged too. The iteration bound uses stored-list length; the numeric reset
position only supplies an encoded-width/primitive-input condition.

[BackendSchnorrRawReset](../Signatures/Runtime/BackendSchnorrRawReset.lean)
implements raw restart with exact full-state source equality and a stored-code
bound independent of tape capacities or reset position. It preserves all private
cells, keeps the requested challenge prefix, appends the replacement and installs
the same resulting tape as saved and remaining state. Its output invariant
charges both lists, each of capacity at most `savedCap + 1`.

[BackendSchnorrRawResetCost](../Signatures/Runtime/BackendSchnorrRawResetCost.lean)
composes the trim/reset cost with argument construction, the complete retained
original input, both output copies and expression framing. Even the old remaining
tape is charged while retained by the implementation.
[BackendSchnorrRawResetBudget](../Signatures/Runtime/BackendSchnorrRawResetBudget.lean)
adds the executed control instruction and proves an all-path `Bounds` certificate
for the actual code. Its polynomial runtime closure follows from encoded widths,
saved/remaining capacities, comparison/subtraction costs and joint structural
overhead. No completed reset or controller efficiency premise is assumed.

[Regressions](../SignaturesTest/SchnorrRawTape.lean) check retained private suffixes,
challenge-prefix selection, both output copies, discarded old remaining state,
empty tapes and a `2^64` reset position. Guards check source computation equality,
standard axioms, complete runtime conclusions, capacity-independent stored code,
absence of a numeric reset-position runtime factor and absence of assumed
completed-adapter budgets. The following checkpoint assembles the native
controller; its runtime and full caller/solver composition remain open.

Validation: all four new source modules, the expanded `SchnorrRawTape`
regression and the aggregate `Signatures` import passed serially with
`-j1 -M8192` and default proof limits, without warnings, admissions, nonstandard
axioms or proof-option overrides. All 628 local links in the updated guides
resolve; `git diff --check` passes.

### Native fork assembly and selected-challenge lookup, 2026-10-15

[BackendSchnorrRawLookup](../Signatures/Runtime/BackendSchnorrRawLookup.lean)
implements a direct fold over the saved tape with a counter, found flag and field
value. It returns the selected challenge with exact source correspondence and
distinguishes an absent entry from a stored zero. It builds no prefix and never
iterates over the numeric position. Its stored-code bound covers the actual
program. [BackendSchnorrRawLookupCost](../Signatures/Runtime/BackendSchnorrRawLookupCost.lean)
derives accumulator/input sizes, every body/loop cost, initialization, framing and
the complete all-path native budget from primitive/backend laws. Its runtime
formula has polynomial closure in encoded widths, tape capacity and primitive
times, with no numeric-position factor or completed-lookup budget premise.

[BackendSchnorrRawFork](../Signatures/Runtime/BackendSchnorrRawFork.lean) assembles
an actual native controller around supplied pass code, selector realizer and
scalar-sampling code. The controller runs from the pass entry point twice with
the same retained configuration, checks first selection, samples the replacement,
looks up the prior challenge, executes native reset and checks second selection.
It does not assume a free snapshot of the attacker's mutable state. A missing old
challenge still permits replay; an unchanged present challenge rejects. Its
execution law is proved, and `source` gives exact computation equality to the
named raw-tape fork after scalar interpretation. The pass laws are required only
for the first run and selected restart states reached by that run; malformed and
unreachable input tapes need not be handled by a pass-source premise.

[BackendSchnorrRawForkDescription](../Signatures/Runtime/BackendSchnorrRawForkDescription.lean)
counts both actual pass descriptions, both selector descriptions, the scalar
sampler, native lookup/reset, all adapters, result injections and control nodes.
The general-caller pass, source cache/signing implementation and selector still
need to be installed and certified. The controller's complete adapter/routing
runtime and whole-solver resources are not claimed by this checkpoint.

[Regressions](../SignaturesTest/BackendSchnorrRawFork.lean) execute the controller
with actual compiled pass/selector fixtures. They check selection failure,
costed-execution independence of an unreachable sampler, missing entry versus
stored zero, acceptance after missing-entry replay, second-selector mismatch,
interleaved lookup and a `2^64` position. The guards check exact computation
correspondence, standard axioms, actual code/realizer inputs, static-description
scope and primitive-derived complete lookup budgets.

Validation: all four new source modules, the new native-controller regression,
the existing `SchnorrRawTape` regression and the aggregate `Signatures` import
passed serially with `-j1 -M8192` and default proof limits. There are no warnings,
admissions, nonstandard axioms or proof-option overrides. All 638 local links in
the updated guides resolve; `git diff --check` passes.

### Complete native fork-controller runtime, 2026-10-15

[BackendSchnorrRawForkSize](../Signatures/Runtime/BackendSchnorrRawForkSize.lean)
tracks pass validity, encoded configuration/output widths and separate saved and
remaining tape capacities. Product frames count every retained copy; sum frames
charge their tags. The complete controller uses a frame-width allowance
`(16 * (firstCap + secondCap) + 64) * width`. This bounds the encoded values at
controller boundaries; it is not a peak-memory theorem for arbitrary pass code.

[BackendSchnorrRawForkLocalCost](../Signatures/Runtime/BackendSchnorrRawForkLocalCost.lean)
derives the costs of all ten compiled adapters, branch selection and rejection.
Structural adapters require no supplied expression budget. The comparison
adapters use only scalar/natural equality primitive bounds. The
[composition rules](../Signatures/Runtime/BackendSchnorrRawForkComposition.lean)
charge atomic invocation, sequencing, branching and retained frames using the
proved encoded footprints.

[BackendSchnorrRawForkBudget](../Signatures/Runtime/BackendSchnorrRawForkBudget.lean)
now proves `Bounds` for the actual complete native controller. Its bound adds
the first and second pass times, twice the selector time, fresh sampling,
the derived lookup/reset times, the two comparison costs, and
`6000 * overhead (256 * frameWidth)`. This conservative structural allowance
covers all adapters and control costs. The reset, lookup and controller budgets
contain no numeric-position iteration factor.

The theorem takes actual pass, selector and sampler implementations. Only the
two actual pass executions and the fresh sampler have supplied `Bounds`
premises; selector work is bounded as an actual local realizer. The first pass
starts with zero saved/remaining capacity. The replay starts with both capacities
`firstCap + 1`, and its returned saved capacity is independently `secondCap`.
Lookup and reset budgets are derived internally from primitive/backend laws.
Result sum-injection costs are explicit backend operation contracts.
`runtimeBound_polynomial` derives polynomial growth from the component resources
and a single joint polynomial backend overhead.

[Regression guards](../SignaturesTest/BackendSchnorrRawFork.lean) check standard
axioms, the complete all-path conclusion, the allowed three component-budget
premises, both pass invariants, absence of assumed internal controller/lookup/reset
costs, and absence of a numeric-position or domain-cardinality runtime parameter.
The existing executed semantic edge cases remain in place.

The general-caller pass, source cache/signing implementation and selector still
need to be installed and their resources derived from measured attacker work.
This controller theorem does not yet certify the complete ROM DLog solver or
replace the pending public/family endpoints.

Validation: all four new source modules, the expanded native-controller
regression, the existing raw-tape regression and the aggregate `Signatures`
import passed serially with `-j1 -M8192` and default proof limits. The checks
reported no warnings or nonstandard axioms; no admissions or proof-option
overrides were introduced. Local guide links and whitespace checks pass.

### General ROM finite-cache pass and native kernels, 2026-10-15

[SchnorrROMListPass](../Signatures/Runtime/SchnorrROMListPass.lean) interprets the
original CMA query interface for arbitrary attacker oracle computations. Dynamic
uniform requests keep their original arities; no arithmetic-source certificate
or random-family bound is supplied. The reduction reuses the implemented managed
cache/signing routines. The final verification lookup bypasses the managed cache
and consults the independent live cache. Full adaptive answer/state refinement,
the final cached challenge invariant, and exact trace equality to
`Schnorr.LazyROM.main` are proved. The map to function-valued source caches is
proof-only.

[SchnorrROMListGrowth](../Signatures/Runtime/SchnorrROMListGrowth.lean) bounds
each cache from the ordinary signing/hash allowances. Starting empty, either
pass stores at most `qS + qH` managed entries and `qH + 1` live entries, including
the final verification query. Private random requests grow neither cache.
The proofs cover every adaptive reply path and require no finite message or
group universe.

[SchnorrRawForkMap](../Signatures/Runtime/SchnorrRawForkMap.lean) proves that
output representation changes commute with the complete raw-tape fork and that
both accepted outputs are supported outputs of the original pass. These laws
let [SchnorrROMListReduction](../Signatures/Runtime/SchnorrROMListReduction.lean)
transport the finite-cache fork and guarded extractor to the named reduction
by exact computation equality. Fallback sampling is included. The same concrete
EUF-CMA probability bound consequently applies to this finite-cache/tape source
reduction without an attacker-language restriction.

[BackendSchnorrROMCache](../Signatures/Runtime/BackendSchnorrROMCache.lean)
compiles the live-cache access, managed-cache access and signing routines into
actual backend code. Each takes an actual state-passing scalar draw, allowing
the retained tape to pass through sampling. Exact semantics preserve both cache
behavior and the returned sampler state. A live hit is independent of the
sampler even in the costed execution. Stored-code bounds count the sampler once
per hash routine and twice in signing; no arity/capacity enumeration is generated.

[Regressions](../SignaturesTest/SchnorrROMList.lean) use Nat messages and an actual
compiled sampler fixture that advances its state on every draw. They cover a
managed hit disagreeing with the live cache, a managed miss/live hit, a double
miss with one draw, a cached zero, and a colliding signature that preserves the
old challenge while performing two ordered draws. A final-verification case
checks that the live challenge takes precedence over a conflicting managed
entry. Guards reject restricted
attacker-source premises and finite-message requirements, and check exact
computation laws, standard axioms and static cache-code scope.

This checkpoint does not supply complete native cache/signing runtime or a
general-caller pass certificate. In particular, private scalar sampling must run
through the raw uniform tape so its internal queries preserve their original
ordering alongside the attacker's private queries. The remaining work must
derive that composition and its cost, install the request/reply dispatcher,
derive selector/pass resources and finish the whole solver.

Validation: all five new source modules, the new general-ROM/cache regression,
the existing native fork regression and aggregate `Signatures` import passed
serially with `-j1 -M8192` and default proof limits. The checks reported no
warnings or nonstandard axioms; no admissions or proof-option overrides were
introduced. Local guide links and whitespace checks pass.

### Native private sampler composition, 2026-10-15

[BackendStateSimulation](../Signatures/Runtime/BackendStateSimulation.lean)
transforms actual backend code by replacing each oracle query with an implemented
stateful handler. It supports local code, sequencing, branching, retained values,
bounded loops with stop code, and input-counted iteration. The complete
transformed computation equals source simulation, including the returned state.
It requires no arithmetic source implementation of the sampler or attacker.
[The description theorem](../Signatures/Runtime/BackendStateSimulationDescription.lean)
bounds stored code by the original description times the handler/structural
allowance; loop bodies are stored once and query arities are not enumerated.

[BackendSchnorrPrivateSampling](../Signatures/Runtime/BackendSchnorrPrivateSampling.lean)
installs the raw uniform-tape handler into the actual sampler code. The sampler's
internal queries retain their original uniform-family tags and share ordering
with attacker draws. Request/reply conversion uses actual backend realizers.
The typed reply normalizes malformed stored naturals exactly as the source
oracle does, so full source equality holds on all input tapes. The scalar
specialization uses exact sampler computation equality to `$ᵗ F`, not merely
equality of its output distribution; this preserves replay behavior.

[Native description bounds](../Signatures/Runtime/BackendSchnorrPrivateSamplingDescription.lean)
count the sampler, installed handlers and both interface conversions.
[The typed handler runtime](../Signatures/Runtime/BackendSchnorrPrivateSamplingBudget.lean)
derives scan/draw/save costs internally from the existing native uniform bound,
then charges request decoding, retained arity/state, typed reply construction and
all routing. Its result preserves both tape encoding invariants and permits one
new saved cell. Polynomial closure is proved from encoded widths, actual tape
capacities and primitive/interface costs; numeric arity is not a runtime factor.
The full handler theorem assumes no completed `Bounds` certificate.

[Regressions](../SignaturesTest/SchnorrPrivateSampling.lean) exercise adaptive
arities, retained local values, skipped branches, both loop forms, malformed
replies, arity `2^64`, and chronological append on a fresh draw. They also guard
the source equalities, standard axioms, primitive-derived handler budget and
absence of capacity/arity enumeration in generated code.

This completes the native private sampler's semantic and stored-code connection.
The whole-sampler runtime connection is established in the later total-runtime
checkpoint below, counting all internal draws, changing tape capacities, local
work, control steps and retained values.
Native cache/signing runtime and complete general-caller pass/selector assembly
remain unfinished.

Validation: the five new source modules, new private-sampling regression,
existing general-ROM/cache and native-fork regressions, and aggregate import
passed serially with `-j1 -M8192` and default proof limits, without warnings,
admissions, nonstandard axioms or proof-option overrides. Local guide links and
whitespace checks pass.

### Original sampler execution resources, 2026-10-15

[Execution profiles](../Signatures/Runtime/BackendExecutionProfile.lean) measure
the original code's local work, executed control nodes, encoded boundary widths,
reached loop counters and chronological requests. Erasing the profile gives the
original computation exactly. A zero-cost backend primitive still contributes
an executed node; an unchosen branch contributes neither work nor visits.
[Resource algebra](../Signatures/Runtime/BackendExecutionProfileBounds.lean)
recovers boundary sizes and bounds the expression
`local work + visits * routing allowance + queries * handler allowance`.
The total-runtime checkpoint below proves that this price bounds the actual
transformed sampler's execution.

[Joint instrumentation](../Signatures/Runtime/BackendStateSimulationExecution.lean)
records the transformed run and source profile on the same execution path.
[Native erasure](../Signatures/Runtime/BackendStateSimulationErasure.lean)
recovers the exact costed native computation, including its step count.
[Source projection](../Signatures/Runtime/BackendStateSimulationProfile.lean)
recovers the simulated source profile with its returned simulator state.
[Resource recovery](../Signatures/Runtime/BackendStateSimulationResources.lean)
therefore attaches original measured resources to every supported actual native
run, without assuming a completed native runtime certificate.

[Structural bounds](../Signatures/Runtime/BackendStateSimulationRouting.lean)
charge primitive costs and routing for atomic calls, sequencing, branching,
retained local contexts, loop-body distribution and input-counted iteration.
They use encoded-width and primitive implementation laws, including an explicit
cost law for distribution over a sum. They do not enumerate the query domain
or charge the original local computation a second time.

These lemmas support the total sampler inequality proved below, with a store
invariant indexed by queries consumed and the proved raw-tape handler bound.
Time alone need not dominate visits or intermediate encoded widths for
an arbitrary quantitative backend; these original resources must be supplied
explicitly or recovered under additional backend laws.

[Regressions](../SignaturesTest/BackendExecutionProfile.lean) check repeated
local work, zero-cost body visits, skipped large-fuel branches, exhausted and
early-return loops, actual query effects, and separation of native call/copy
costs from source work. Scope guards check exact computation equalities,
standard axioms and absence of completed-native-budget premises in resource
recovery. All seven source modules, the new regression, the existing private
sampling regression and aggregate import passed serially with `-j1 -M8192`,
default proof limits and no warnings. Documentation links and whitespace checks
also pass.

### Complete transformed sampler runtime, 2026-10-15

[Structural accounting](../Signatures/Runtime/BackendStateSimulationAccounting.lean)
derives a per-node allowance from primitive costs, encoded sizes and an explicit
loop-test cost bound. [Loop composition](../Signatures/Runtime/BackendStateSimulationLoopBudget.lean)
charges executed bodies, every test, exhausted stop code and early returns.
The store invariant advances by the number of requests actually consumed, so
sequential calls and repeated loops can increase a finite tape's capacity.

[The whole-program theorem](../Signatures/Runtime/BackendStateSimulationBudget.lean)
covers all seven constructors of actual backend code and proves:

```text
compiled time <= original local work
                + original visits * routing allowance
                + original queries * handler allowance
```

The exact profile coupling supplies original resources for every actual native
run. The theorem also preserves the indexed store invariant and bounds the
number of consumed requests. It does not infer runtime from output-distribution
equality or assume a budget for the completed transformed program.

[The Schnorr sampler instantiation](../Signatures/Runtime/BackendSchnorrPrivateSamplingResources.lean)
derives the typed handler and all structural charges internally from primitive
contracts. Original work, visits, queries and encoded widths are measured on the
original sampler. The final output retains its original width bound. Starting
with `savedCap` saved cells and `remainingCap` replay cells, the returned tape has
at most `savedCap + queries` saved cells and at most `remainingCap` replay cells.
The handler cost is evaluated at the maximum reserved saved capacity; monotonicity
of that actual formula is proved. Polynomial closure follows from these source
resources and backend costs. Numeric query arities and loop counters are absent
from the runtime formula; their encoded values and actual test/conversion costs
remain charged. Existing exact source and stored-code theorems apply to the same
compiled sampler.

[Regressions](../SignaturesTest/BackendStateSimulationBudget.lean) check sequential
store growth, all loop tests, and the zero-iteration case. Guards require a
complete native `Bounds` conclusion, an original execution-profile premise,
standard axioms, and no assumed completed sampler/handler/structural budget in
the Schnorr theorem. No arithmetic source certificate or finite query domain is
required. Cache/signing runtime, caller assembly and whole-solver endpoints are
still unfinished.

Validation: all four new proof modules, the new budget regression, existing
execution-profile and private-sampling regressions, and aggregate import passed
serially with `-j1 -M8192`, default proof limits and no warnings. All 1127 relative
documentation links resolve; whitespace checks pass.

### Native Schnorr ROM live cache and signing cache update, 2026-10-15

[Expression lookup costs](../Signatures/Runtime/BackendLookupExprCost.lean) now
bound the actual compiled list scan with an inlined comparison expression. The
comparison runs with the entire lookup environment retained; its cost includes
those encoded values. The fold charges every visited cell and preserves the
accumulator's value width. Bounds depend on stored entries, not the key universe.
[Schnorr's comparison specialization](../Signatures/Runtime/BackendSchnorrROMComparison.lean)
derives that comparison and full scan cost from the actual message/point equality
primitives, list representations, structural costs and encoded widths.

[The generic cache theorem](../Signatures/Runtime/BackendCacheExprBudget.lean)
charges lookup, branching, hit return, stateful sampling, insertion and retained
contexts for the existing `cacheGetExpr` compiler. A miss may advance the store
invariant; a hit preserves the store and fits the reserved output invariant.
[Native live-cache runtime](../Signatures/Runtime/BackendSchnorrROMLiveBudget.lean)
instantiates this with Schnorr's actual structured comparator. It derives all
lookup/comparison costs internally. The only supplied whole-code component budget
is the actual scalar draw. Its result bounds scalar and entry widths, limits cache
length to the original capacity plus one, and establishes the output store invariant.
Its runtime formula has polynomial closure from widths, capacity, primitive
costs, structural overhead and the draw budget.

[Signing cache programming](../Signatures/Runtime/BackendSchnorrROMProgrammingCost.lean)
now has a derived cost for the actual compiled `cacheProgram hashEq` expression,
including lookup, branch, retained result and insertion. Entry widths and length
at most the input capacity plus one are proved, as is polynomial closure. This
is the pure cache update within signing; the complete two-draw signing routine
still needs its runtime composition and sampler installation.

[Regressions](../SignaturesTest/SchnorrROMCacheBudget.lean) use an infinite message
type and check misses after both kinds of mismatch, state advancement, first-hit
zero values, shadowed duplicates and preservation of a programmed entry. The
costed hit execution is independent of the supplied draw implementation. Guards
check standard axioms, an actual native `Bounds` conclusion, the single permitted
draw budget, and no assumed completed lookup/comparison cost, finite domain or
arithmetic attacker source in the native cache-cost endpoints.

Managed-cache runtime, full signing runtime with the certified sampler,
general-caller pass/selector assembly and whole-solver/public/family endpoints
remain unfinished.

Validation: all five new proof modules and the cache-programming extension,
the new cache regression, existing finite-ROM and sampler-budget regressions,
and aggregate import passed serially with `-j1 -M8192`, default proof limits and
no warnings. The 688 relative links in the two updated guides resolve;
whitespace checks pass.

### Complete native cache/signing runtime and sampler installation, 2026-10-15

[Named syntax and local costs](../Signatures/Runtime/BackendSchnorrROMParts.lean)
identify the existing `managedGet` and `signCached` programs by definitional
equality. Their actual compiled projections, argument packing, cache insertion,
commitment arithmetic and return construction have primitive-derived costs.
[Managed-cache runtime](../Signatures/Runtime/BackendSchnorrROMManagedBudget.lean)
now composes the managed scan, hit return and live-cache miss path. A hit preserves
both lists and the store. A miss consults the live cache and installs the returned
answer in the managed cache. Bounds include both retained lists, at most one
new entry in each, and the sampler's changed store invariant.

[Complete signing runtime](../Signatures/Runtime/BackendSchnorrROMSigningBudget.lean)
charges both sequential draws, two scalar multiplications, subtraction, cache
programming, argument/context adapters and the returned signature/cache. Three
store invariants distinguish the initial state, state after the first draw and
final state. Cache keys use a fixed allowance for the message/point pair; repeated
signing does not multiply that allowance. Both kernels have polynomial runtime
closure, and their existing exact semantics and stored-code bounds still apply.

The initial sampler installation in commit `1cc6529` used `NativePrivate.code`
in all three kernels. Its runtime theorem correctly bounded that code, but the
hash implementation did not match the source game's challenge family. No source
correspondence for that installation had been proved. The correction below
replaces hashing's draw and its tape reservation; the generic kernel budgets
and private signing implementation remain valid.

[Kernel regressions](../SignaturesTest/SchnorrROMKernelBudget.lean) execute two
different draws to check which scalar becomes the challenge and which becomes
the response, state advancement between calls, insertion, and collision with an
existing zero and shadowed duplicate. Scope guards require actual kernel bounds,
the two distinct draw budgets in generic signing, and no completed component
budget in the installed theorem. They also require an original sampler profile,
the presence of a transformed sampler, and standard axioms. That presence check
was insufficient to distinguish hash and signing draw families; the correction
below strengthens it for each individual kernel.

Native caller-state adapters, dispatch, general-caller pass/selector resources,
complete extraction/fallback, public security and family endpoints remain open.
The separate nonzero-nonce variant is also unfinished.

Validation: all four new proof modules, the new kernel regression, existing
cache, finite-ROM and sampler-budget regressions, and aggregate import passed
serially with `-j1 -M8192`, default proof limits and no warnings. All 696 relative
links in the two updated guides resolve; whitespace checks pass.

### Correct hash/private draw installation and ordinary sampler runtime, 2026-10-15

[Original-profile runtime](../Signatures/Runtime/BackendExecutionProfileCost.lean)
now bounds the actual untransformed backend program by
`work + visits * (overhead (3 * width) + tickTime) + queries * queryTime`.
The proof covers all seven code constructors, including exhausted loop tests,
early returns and encoded iteration counters. It derives runtime and final
output width from the same original execution profile used for private-tape
sampling, without a finished program-budget premise. The formula has polynomial
closure without a numeric counter, arity or message-domain factor.

[The challenge adapter](../Signatures/Runtime/BackendSchnorrROMDraws.lean) wraps the
existing native challenge handler in the cache kernels' stateful draw interface.
Its complete computation matches the raw challenge oracle when the original
sampler implements uniform field sampling. Replay consumes a challenge cell and
preserves private cells. A fresh draw executes the original sampler outside the
private replay handler and appends exactly one challenge cell. Stored-code and
complete runtime bounds charge the adapter and sampler; polynomial closure is
proved.

[Corrected kernel installation](../Signatures/Runtime/BackendSchnorrROMPrivateBudget.lean)
uses this challenge adapter in live/managed hashing and `NativePrivate.code` in
signing. Both sampler budgets are derived from the original profile. Hashing
reserves `savedCap + 1`; signing reserves `savedCap + 2 * queries`, evaluating
the second draw at its increased saved capacity. The maximum store-width premise
covers the extra challenge cell even when the sampler makes zero internal
queries. Source profile widths fit the tape's scalar encoding allowance.

[Kernel regressions](../SignaturesTest/SchnorrROMKernelBudget.lean) check hash replay
with interleaved private cells, exactly one fresh challenge append for an arbitrary
sampler, managed hits that skip both live lookup and drawing, and actual private
sampling across two signing draws while preserving the challenge cell. Scope
guards check the installed draw family separately in each kernel.
[Profile regressions](../SignaturesTest/BackendExecutionProfile.lean) check actual
loop-test charges, including zero iterations and immediate return with huge fuel,
and guard the theorem's original-program resource scope and axioms.

Common-store dispatch and complete pass/source correspondence remain open.
These corrected component theorems do not claim a finished source-equivalent
native pass or complete solver efficiency.

Validation: the three changed/new proof modules, kernel and execution-profile
regressions, existing raw-tape/private-sampling/finite-ROM regressions and aggregate
import passed serially with `-j1 -M8192`, default proof limits and no warnings.
All 703 relative links in the two updated guides resolve; whitespace checks pass.

### Shared native ROM state, dispatch and caller source correspondence, 2026-10-15

[Shared source interpretation](../Signatures/Runtime/SchnorrROMSharedState.lean)
combines the established list-cache handler with the raw replay tape. It commutes
with adaptive oracle simulation and preserves complete outputs and state.
[Actual common-store adapters](../Signatures/Runtime/BackendSchnorrROMHandlerComponents.lean)
retain the generator/public key, managed/live caches, and saved/remaining tapes
around all four native components. Signing preserves the live cache; final
verification accesses live state directly, bypassing managed programming.
[Component source laws](../Signatures/Runtime/BackendSchnorrROMHandlerSource.lean)
connect these executed components to the original list handler and final hash.
They hold on all tapes, including malformed natural replies decoded modulo the
requested range. No tape-validity or finite message-domain premise is required.

[Request and dependent-reply ports](../Signatures/Runtime/BackendSchnorrROMInterface.lean)
are actual backend realizers. Random arities are runtime naturals, with no arity
table or code-generation cap. The [complete dispatcher and caller](../Signatures/Runtime/BackendSchnorrROMHandler.lean)
install these ports and components. `code_denote` proves exact source equality;
`executed_erase` relates the same costed code to that source. The arbitrary
quantitative caller realizes adaptive simulation of the original list handler.
`caller_source_of_resources` and `caller_no_cutoff_of_resources` derive successful
termination from the caller's own `RunsWithin` query allowance and implementation
law, without a finished reduction-efficiency premise or arithmetic-attacker restriction.

[Stored-code accounting](../Signatures/Runtime/BackendSchnorrROMHandlerDescription.lean)
bounds the complete dispatcher, final hash and caller. It counts the original
sampler and its private transformation, native cache kernels, all common-store
adapters, request/reply ports and caller initialization/head/update code.
The caller bound adds the actual fuel encoding allowance and structural code
costs; it has no numeric arity or message-domain factor.

[Regressions](../SignaturesTest/SchnorrROMHandler.lean) exercise hash replay with
interleaved private cells, conflicting managed/live values, final-live-hash
selection, two sequential signing draws that preserve live state, and typed
random dispatch from a malformed raw reply. Axiom and theorem-scope guards check
exact computation equality, measured caller resources, arbitrary domains and
absence of completed solver-budget premises.

This checkpoint supplies source correspondence and code accounting for the
interaction phase. Assembled runtime/encoding propagation, executable final
verification/pass output handling, selector, whole solver and public/family
security endpoints remain open. The nonzero-nonce route remains separate.

Validation: all six new proof modules, the new handler regression, existing
kernel/finite-ROM regressions and aggregate import passed serially with
`-j1 -M8192`, default proof limits and no warnings. All 717 relative links in the
two updated guides resolve; whitespace checks pass.

### Complete shared-store ROM component runtime, 2026-10-15

[Adapter costs](../Signatures/Runtime/BackendSchnorrROMHandlerLocalCost.lean) now
bound all eight actual compiled preparation/return expressions. Each takes at
most `1028 * overhead (256 * width)` local time and produces at most `32 * width`
encoded output. Hash and final-hash preparation additionally charge the scalar
zero primitive. Every projection, pair, retained input and constructed default
is covered by the backend contracts.

[Shared-store invariants](../Signatures/Runtime/BackendSchnorrROMHandlerSize.lean)
keep generator/public-key widths, managed/live cache entries and both tape lists
explicit. Cache key/value allowances remain `3 * width` across calls. If the
reserved tape encoding fits `width`, the complete store fits
`(12 * (managedCap + liveCap) + 13) * width`. The common composition frame is
`W = (32 * (managedCap + liveCap) + 128) * width`. Capacity monotonicity and
argument/store encoding bounds are proved.

[Component composition](../Signatures/Runtime/BackendSchnorrROMHandlerComponentBudget.lean)
installs the actual adapters around each native kernel, charging two local
invocations, two sequence boundaries, and retained state. It derives the returned
shared invariant for every execution path. Hashing can grow both caches by one;
final hashing grows only live state; signing grows only managed state; attacker
randomness preserves both caches. Tape reservations follow each underlying draw.

[Primitive-derived complete component budgets](../Signatures/Runtime/BackendSchnorrROMHandlerPrimitiveBudget.lean)
instantiate those rules from original scalar-sampler profiles and primitive,
encoding and control contracts. No finished adapter, sampler or kernel runtime
certificate is a premise. Every wrapped component adds
`2061 * overhead (8192 * W)` to its kernel budget; hashing/final hashing also add
the charged default-zero construction. Signing reserves both private draws;
hashing and attacker randomness reserve one additional tape cell. All four
runtime formulas have polynomial closure, with no numeric arity/counter or
message-domain factor. This certifies the same component programs used by the
previous exact source-correspondence theorem.

The shared [budget weakening rule](../Signatures/Runtime/BackendBudget.lean)
preserves the exact program and input/output predicates when increasing a time
allowance. Using that rule avoids expanding large program semantics merely to
prove arithmetic inequalities; proof-resource limits remain unchanged.
[Regression guards](../SignaturesTest/SchnorrROMHandler.lean) check all new axioms,
the actual four component programs, original sampler resources and the absence
of completed-budget or finite-domain premises. Existing execution examples still
cover cache separation, sequential signing draws and malformed raw random replies.

Indexed request conversion, retention and dependent reply tagging still need
their complete runtime bounds. Then compose the arbitrary caller from measured
resources and complete the final pass/selector, solver and public/family endpoints.

Validation: the four new proof modules and shared budget module compiled without
warnings; extended handler regressions, existing kernel regressions and the
aggregate import passed serially with `-j1 -M8192` and default proof limits.
All 727 relative links in the two guides resolve; whitespace checks pass.

### Complete indexed ROM dispatcher runtime, 2026-10-15

[Interface contracts](../Signatures/Runtime/BackendSchnorrROMHandlerPorts.lean)
charge actual request conversion and each dependent reply tagger. The random
reply contract covers every bounded raw natural, including malformed tape
values that require modulo decoding. Native request encodings and complete
retained-store widths are derived from the component invariants.

[Routing composition](../Signatures/Runtime/BackendSchnorrROMHandlerRoutingBudget.lean)
charges both sum branches, request retention, reply tagging and the initial
boundary conversion. With `W` the shared component frame and
`H = 8 * (W + portWidth)`, the complete dispatcher takes at most
`max (max randomTime hashTime) signingTime + encodeTime + tagTime + 40 * overhead (128 * H)`.
These component times are then discharged by the
[complete actual-code theorem](../Signatures/Runtime/BackendSchnorrROMHandlerBudget.lean)
from original sampler profiles and primitive, encoding, control and port laws.
No completed handler, sampler or compiler runtime certificate is supplied.
The output permits one extra managed/live cache entry and at most
`2 * samplerQueries + 1` additional saved tape cells. This allowance covers
hashing even when the scalar sampler itself makes zero private queries.

[Adaptive reservations](../Signatures/Runtime/BackendSchnorrROMHandlerReserve.lean)
reserve one entry in each cache and `2 * samplerQueries + 1` tape cells per
future call. The actual dispatcher consumes one reservation and preserves all
others, using the fixed maximum-capacity runtime. Its final theorem discharges
smaller-capacity instances internally from the same primitive/original-profile
premises. The shared [predicate consequence rule](../Signatures/Runtime/BackendBudget.lean)
keeps the executed code opaque while changing only its input/output predicates.

[Polynomial closure](../Signatures/Runtime/BackendSchnorrROMHandlerPolynomial.lean)
now covers the entire dispatcher formula, including both original/transformed
samplers and every conversion/retention cost. No numeric arity, counter or
message-domain cardinality factor is introduced. Expanded
[regression guards](../SignaturesTest/SchnorrROMHandler.lean) require the actual
full dispatcher, original sampler resources and local port costs, reject finished
budget/arithmetic-attacker/finite-domain premises, and check the standard axiom
footprint. The existing malformed-random-reply and cache/replay examples still pass.

Next: recover request bounds from measured caller encodings, compose whole-caller
runtime, then assemble the final pass/selector and complete the solver and public
concrete/family endpoints. The existing source correspondence, no-cutoff and
stored-code results are retained.

Validation: all five new modules compiled without warnings. Extended handler
regressions and aggregate imports passed serially with `-j1 -M8192` and default
proof limits. All 739 relative links in the two guides resolve; whitespace checks pass.

### Complete arbitrary ROM caller runtime, 2026-10-15

[Request recovery](../Signatures/Runtime/BackendSchnorrROMRequestRecovery.lean)
derives the full hash key, signing message and random arity bounds from encoded
request size. Canonical equal-size encodings use identity recovery. Natural-value
recovery may allow an exponential numeric range; neither runtime nor code
enumerates that range. Actual conversion costs remain charged by the port laws.

[Caller composition](../Signatures/Runtime/BackendSchnorrROMCallerBudget.lean)
installs the already certified dispatcher in the actual general caller. An
invariant reserves cache/tape capacity for the remaining calls and follows every
typed reply-dependent continuation. Initialization, retained state, returned
replies and loop/control work are included. Its complete time bound is

```text
callerLocalTime + sum_k (queries[k] * dispatcherTime)
  + 3 * overhead (32 * routeWidth)
  + (fuel + 1) * (42 * overhead (32 * routeWidth) + callerTickTime).
```

[Measured-resource composition](../Signatures/Runtime/BackendSchnorrROMCallerResources.lean)
derives request/state/head widths, continuation invariants and the symbolic-price
budget directly from the attacker's `RunsWithin` contract. It uses
`bound.work + 2 * bound.queries + 2` for caller local work and conservatively
bounds each of the three request counts by `bound.queries`. The final theorem
assumes no completed handler/caller budget, arithmetic attacker implementation,
finite message domain or caller-specific invariant. Actual scalar sampling is
charged from its original execution profile; actual boundary conversions remain
explicit local backend contracts.

[Returned-output bounds](../Signatures/Runtime/BackendSchnorrROMCallerOutput.lean)
connect the executed caller to its costed reference and bound the complete
returned encoding by the measured head-size cap. This includes returns at zero
remaining fuel. Existing measured termination and exact source correspondence
still rule out cutoff when sufficient query fuel is supplied.
[Polynomial closure](../Signatures/Runtime/BackendSchnorrROMCallerPolynomial.lean)
covers the entire installed caller runtime formula, including original caller
work, all dispatcher calls and control costs, without a numeric-arity/counter or
message-domain factor.

[Caller regressions](../SignaturesTest/SchnorrROMCaller.lean) check actual zero-fuel
return/cutoff behavior with the full shared store, classify dynamic random arities
as large as `2^64`, and guard the complete runtime/output theorem assumptions and
standard axiom footprints. These are caller-phase certificates; final-live-hash
assembly, fork selection, extraction/fallback and full solver/public/family
endpoints remain to be completed.

Validation: all five new proof modules, the new caller regression and aggregate
imports passed without warnings, serially with `-j1 -M8192` and default proof
limits. All 751 relative links in the two guides resolve; whitespace checks pass.

### Native ROM pass assembly and source correspondence, 2026-10-15

The [actual native pass](../Signatures/Runtime/BackendSchnorrROMPass.lean)
initializes empty managed/live caches, converts the public key into the caller's
input representation, executes the general attacker, and handles its optional
return. A completed return is converted into the native forgery representation
and checked against the live hash cache, retaining the full forgery, both caches
and the replay tape. Cutoff returns an empty result list without running the
final sampler. Completion returns a singleton list. This uses existing arithmetic
types without a default message; the language has lists but no sum constructor.

[Exact source correspondence](../Signatures/Runtime/BackendSchnorrROMPassSource.lean)
identifies the complete native pass with the singleton embedding of the source
finite-cache pass, on every supplied raw tape. The resource-derived endpoint
obtains termination from `RunsWithin` and sufficient query fuel. Every supported
costed execution then returns a singleton. There is no arithmetic-attacker,
finite-message, default-message or completed-runtime premise.

[Stored-code accounting](../Signatures/Runtime/BackendSchnorrROMPassDescription.lean)
covers the entire assembled pass, including the caller, original/transformed
sampling code, cache kernels, boundary conversions and final verification.
[Local adapter costs](../Signatures/Runtime/BackendSchnorrROMPassLocalCost.lean)
charge initialization, final-hash input/output packing, singleton construction
and cutoff. [Encoding invariants](../Signatures/Runtime/BackendSchnorrROMPassSize.lean)
bound both caches, the retained forgery/challenge and both tape lists, and derive
initial capacity reservations. [Final verification composition](../Signatures/Runtime/BackendSchnorrROMPassVerificationBudget.lean)
adds retained-forgery, copying, packing and control costs to the existing live-hash
budget. This is an internal composition lemma; the complete runtime theorem in
the following checkpoint now discharges its component premise and composes it
with initialization, boundary conversion, terminal control and the measured caller.

[Pass regressions](../SignaturesTest/SchnorrROMPass.lean) check that verification
uses the live cache when the managed cache disagrees, preserves private cells
around a replayed challenge, and skips sampling on cutoff even in the complete
costed run. Assumption guards preserve arbitrary callers/messages and check the
standard axiom footprint. The following checkpoint completes pass runtime;
selector certification and whole-solver/public/family endpoints remain open.

Validation: all six new proof modules, the pass regression and aggregate imports
passed without warnings using serial `-j1 -M8192` and default proof limits. All
765 relative links in the two guides resolve; whitespace checks pass.

### Complete general ROM pass runtime, 2026-10-15

[Boundary contracts](../Signatures/Runtime/BackendSchnorrROMPassPorts.lean) account
for actual public-key input, forgery output and optional-return conversions.
They allow different caller and native encodings and contain no completed
reduction-budget premise. [Initialization](../Signatures/Runtime/BackendSchnorrROMPassSetup.lean)
charges cache construction, retained configuration/tape and the actual input
conversion. Its capacity reservations cover both an empty first tape and a
nonempty replay tape.

[Terminal composition](../Signatures/Runtime/BackendSchnorrROMPassTerminalComposition.lean)
charges output conversion, final verification, singleton construction, optional
dispatch and cutoff, preserving the result and both tape-list invariants.
The [complete pass theorem](../Signatures/Runtime/BackendSchnorrROMPassBudget.lean)
derives all component budgets from the original scalar-sampler execution profile,
primitive/encoding/control contracts and the arbitrary caller's `RunsWithin`
resources. Request recovery and measured output widths discharge the caller
and final-verification interfaces. No completed sampler, handler, caller,
verification or pass runtime is assumed. With
`W = routeWidth + (32 * (managedCap + liveCap) + 128) * width`, the bound is

```text
callerTime + finalHashTime + inputTime + outputTime + optionalTime
  + 8192 * overhead (8192 * W).
```

`callerTime` is the previously derived measured-caller formula; `finalHashTime`
is the live-cache/challenge lookup cost derived from the original sampling profile.
The final result has at most one completed pass, at most one extra live-cache
entry and at most one extra saved challenge cell. Runtime covers cutoff too;
the separate source/completion theorem excludes it when query fuel suffices.

[Polynomial closure](../Signatures/Runtime/BackendSchnorrROMPassPolynomial.lean)
covers this entire installed formula from original caller/sampler resources,
encoded widths, capacities and local operation costs. It assumes no polynomial
numeric arity, loop-counter value or message-domain cardinality. Extended
[regression guards](../SignaturesTest/SchnorrROMPass.lean) require the actual full
pass, measured caller/sampler resources and boundary contracts, reject supplied
finished budgets, and check output/tape invariants and standard axiom footprints.
Selector certification, complete fork/solver assembly, complete solver code-family
closure and public/family security endpoints remain open.

Validation: all five new proof modules, the expanded pass regressions and aggregate
imports passed without warnings using serial `-j1 -M8192` and default proof limits.
All 776 relative links in the two guides resolve; whitespace checks pass.

### Native ROM selector source, description and chronological lookup, 2026-10-15

The [actual native selector](../Signatures/Runtime/BackendSchnorrROMSelection.lean)
verifies the returned Schnorr equation, reverses and scans the live cache, and
checks the selected ordinal against `qH + 1`. Empty pass results reject; singleton
results equal the existing source selector exactly. Every result list has defined
semantics (the fold keeps the last result's selection), and its encoded choice
equals its source interpretation on all inputs. Every returned index is at most
`qH`. No default message or finite message domain is required.

The [stored-code bound](../Signatures/Runtime/BackendSchnorrROMSelectionDescription.lean)
counts the actual compiled verifier, reversal, scan and guard, including the
`qH + 1` literal. It stores the scan body once. With `s(op)` the primitive's
stored size and `a` the local description allowance, the bound is

```text
2*s(scale₁) + s(add₁) + 2*s(point₁Eq) + s(messageEq)
  + s(natAdd) + s(natLt) + qH + 4096*a + 16.
```

The [scan-step cost](../Signatures/Runtime/BackendSchnorrROMLiveIndexCost.lean),
[complete fold cost](../Signatures/Runtime/BackendSchnorrROMLiveIndexFold.lean)
and [complete chronological lookup](../Signatures/Runtime/BackendSchnorrROMLiveIndexBudget.lean)
bound the actual compiled canonical expressions. A remaining-cell invariant
bounds the growing ordinal. Reversal, the original cache, intermediate reversed
cache, trailing environments and all copies/control work are charged. Comparison
contracts concern encountered cells and the fixed target; the theorem supplies
the scan and reversal budgets internally. There is no message-space iteration.

[Polynomial closure](../Signatures/Runtime/BackendSchnorrROMSelectionPolynomial.lean)
covers this complete lookup formula and the selector-description formula from
encoded widths, encountered-cache capacity, primitive costs/sizes, query allowance
and structural overhead. This does **not** yet certify the selector's entire
runtime: verification, guard, outer result fold and adapters still need composition.
Installing both passes and this selector in the controller, whole-solver runtime
and stored-code closure, and public/family security endpoints remain open.

[Regressions](../SignaturesTest/SchnorrROMSelection.lean) check empty results,
the final-query slot at `qH = 0`, chronological indexing, out-of-range rejection,
managed/live-cache separation, failed verification, duplicate keys and malformed
multi-result lists. Guards require the actual compiled lookup, reject finished
component budgets and finite/default-message premises, and check standard axioms.

Validation: the six proof modules, new selector regressions and aggregate imports
passed without warnings using serial `-j1 -M8192` and default proof limits. All
788 relative links in the two guides resolve; whitespace checks pass.

### Complete native selector runtime and installed fork source, 2026-10-15

[Local selector costs](../Signatures/Runtime/BackendSchnorrROMSelectionLocalCost.lean)
now charge the two scalar multiplications, group addition, signature-equation
comparison, query-limit guard, lookup preparation and branch control.
[Single-pass selection](../Signatures/Runtime/BackendSchnorrROMSelectionComponentBudget.lean)
derives all those budgets from `CompletedBound` and individual primitive contracts.
The contracts bound primitive output encodings as well as runtime, and are applied
at the fixed `3 * width` field/group/message allowance.

The [complete selector theorem](../Signatures/Runtime/BackendSchnorrROMSelectionBudget.lean)
bounds `Q.cost` of the actual `NativeSelection.selector`, including the outer
empty/singleton fold and input framing. No completed verifier, lookup, guard or
selector efficiency premise occurs. With
`W = (32 * (managedCap + liveCap) + 128) * width`, the bound is

```text
indexTime overhead W liveCap messageTime pointTime incrementTime
  + 2*scaleTime + addTime + pointTime + comparisonTime
  + 1280*overhead(512*W).
```

The index formula already charges reversal, scan, counter increments and retained
copies. Natural encodings cover `max liveCap qH + 1`; the query-limit literal is
also counted in the stored description. The
[polynomial theorem](../Signatures/Runtime/BackendSchnorrROMSelectionPolynomial.lean)
now covers the complete installed selector runtime, from original widths, cache
capacities and primitive/control costs. It assumes no completed component's
polynomial bound or message-space cardinality.

The [installed native fork](../Signatures/Runtime/BackendSchnorrROMFork.lean)
uses the actual general pass, this selector and the scalar sampler in the existing
controller. Measured caller resources and sufficient fuel imply exact equality
with the source finite-cache/raw-tape fork, using its original `selectPass
PrimitiveCosts.unit qH`. The singleton output embedding commutes with the complete
fork; no first-pass, replay or selector source law is left as an external premise.
Every supported costed run rejects or returns two singleton completed results.
Its [complete stored-code bound](../Signatures/Runtime/BackendSchnorrROMForkDescription.lean)
counts both complete pass and selector occurrences, sampling, reset, lookup and
all controller adapters, deriving pass/selector sizes internally.

Extended [selector guards](../SignaturesTest/SchnorrROMSelection.lean) require
the complete actual cost and inspect primitive contracts for hidden finished
budgets. [Fork guards](../SignaturesTest/SchnorrROMFork.lean) require measured
caller resources, the actual installed components and the original source fork,
and reject supplied first/replay/selector laws, restricted arithmetic attackers,
finite/default messages or completed runtime premises.

Remaining: compose installed fork runtime with two pass instances, keeping tape
entry width separate from full retained-output width. The generic controller's
current single-width contract needs this generalization; substituting its large
output width for the pass's tape-entry width creates circular size requirements.
Then finish setup, extraction/fallback, whole-solver resource and code-family
certificates, and public/family security endpoints.

Validation: all six affected proof modules, both selector/fork regression files
and aggregate imports passed without warnings using serial `-j1 -M8192` and
default proof limits. All 800 relative guide links resolve; whitespace and
placeholder/resource-override checks pass.

### Complete installed fork runtime with separate tape widths, 2026-10-15

The [controller width invariants](../Signatures/Runtime/BackendSchnorrRawForkTapeWidth.lean)
now retain a narrow `tapeWidth` for scalar/natural tape fields independently of
the width charging full configurations and pass outputs. State/tape frames keep
that narrow property while their structural costs use the larger width. The
[generalized runtime theorem](../Signatures/Runtime/BackendSchnorrRawForkBudget.lean)
charges lookup/reset at tape-entry width, preserves the narrow replacement-sample
bound, and charges all retained copies at full output width. Its formula has
polynomial closure with both widths separately bounded; the old `bound` theorem
is retained with its original statement as the equal-width specialization.

[Original pass resources](../Signatures/Runtime/BackendSchnorrROMPassResources.lean)
package the existing sampler profile, primitive/encoding/port contracts and
caller capacity reservations. They contain no completed pass, caller, handler or
sampler runtime premise. The actual pass budget follows from these resources and
`R.RunsWithin`; fresh sampling is separately derived from the original execution
profile. Tape width is proved below full width using the existing storage bound.

The [installed fork theorem](../Signatures/Runtime/BackendSchnorrROMForkBudget.lean)
now bounds actual `NativeROMFork.code` on every supported costed run. It derives
both pass budgets, the actual selector budget and fresh sampler budget internally.
Initial execution starts with empty tapes. With first-pass reservation `savedCap`,
its final tape has capacity `savedCap + 1`, and replay starts with capacities
`savedCap + 2` for both lists. The second resource record reserves subsequent draws
separately. Complete singleton results fit
`(16 * (managedCap + liveCap + 1) + 64) * width`, with no finite/default-message
or arithmetic-attacker premise. This resolves the circular width requirement
identified at the preceding checkpoint.

[Controller guards](../SignaturesTest/BackendSchnorrRawFork.lean) cover both theorem
interfaces and require fresh sampling to preserve narrow tape width.
[Installed-fork guards](../SignaturesTest/SchnorrROMFork.lean) require measured caller
resources, both resource records, primitive selector contracts and the actual
complete-code conclusion; they also inspect the resource constructor to reject
hidden completed budgets. Axiom checks cover the new proofs.

Remaining: derive polynomial closure of the fully instantiated fork budget from
the original resource families, then complete setup, extraction/fallback,
whole-solver runtime and stored-code family certificates, and public/family security
endpoints. The generic controller's polynomial theorem does not by itself close
these whole-solver obligations.

Validation: all four affected proof modules, both fork regression files and
the aggregate import pass without warnings under serial `-j1 -M8192` and default
proof limits. All 809 relative links in the two guides resolve; whitespace,
placeholder, axiom and resource-override checks pass.

### Installed fork polynomial closure and complete native solver source, 2026-10-15

[Numerical pass inputs](../Signatures/Runtime/BackendSchnorrROMPassTime.lean) now
factor the complete runtime formula without tying the security parameter to one
curve or message type. `Resources.timeInputs` projects these numbers from the
original contracts; `Resources.time` delegates to the same formula. The polynomial
record bounds only original sampler work, visits, queries, widths/capacities and
primitive/port/control costs. Numeric arities and counter values are absent.

The [installed fork polynomial theorem](../Signatures/Runtime/BackendSchnorrROMForkPolynomial.lean)
derives both pass runtimes, replay capacities, selection and replacement sampling
from those original input families. It proves `PolynomiallyBounded` for the exact
`resourcesTime` formula appearing in `NativeROMFork.code_bound_of_resources`.
It assumes no polynomial finished-pass/selector/sampler runtime.

[Native extraction](../Signatures/Runtime/BackendSchnorrROMExtraction.lean) now
works directly on the controller's pair of result lists. The singleton case
checks equal commitments and distinct challenges, then computes
`(z-z')/(c-c')`; failed guards execute the original uniform sampler. Failed forks
also sample uniformly. Empty lists reject without inventing a message; both
folds have defined behavior on every input list. The actual compiled extraction
is exactly the existing `extractFork` on encoded source fork results.

The [complete solver](../Signatures/Runtime/BackendSchnorrROMSolver.lean) installs
configuration setup, the actual native fork and this extractor. From `R.RunsWithin`,
sufficient fuel and `R.machine.Implements`, its full computation equals the named
`Schnorr.LazyROM.dlogReduction`, including extraction/fallback sampling order.
No external fork/extractor source law or arithmetic-attacker certificate is assumed.

Its [stored-code theorem](../Signatures/Runtime/BackendSchnorrROMSolverDescription.lean)
counts the complete installed fork and setup plus both fallback sampler occurrences.
The extractor adds two field subtractions, division, point/scalar equality, three
zero literals and structural code; the fold bodies are stored once. Component
description bounds are derived internally from original backend/description laws.

Expanded [fork guards](../SignaturesTest/SchnorrROMFork.lean) inspect polynomial
contracts to prevent hidden finished-component efficiency assumptions.
[Solver regressions](../SignaturesTest/SchnorrROMSolver.lean) exercise successful
native extraction, fallback, equal challenges, unequal commitments and empty
outputs; guards require actual installed code and the named source reduction,
measured attacker resources, arbitrary message types and standard axioms.

Remaining: derive setup and guarded-extraction/fallback runtime from primitive,
sampler and encoding contracts, then compose the complete solver runtime. Derive
whole-solver polynomial time and stored code, construct the fixed-backend executable
certificate, and finish concrete/public/family security. Source equality and a
stored-code bound alone do not discharge those runtime and family obligations.

Validation: all seven affected proof modules, both fork/solver regression files
and the aggregate import pass without warnings under serial `-j1 -M8192` and
default proof limits. All 822 relative guide links resolve; whitespace,
placeholder, axiom and resource-override checks pass.

### Complete native Schnorr ROM runtime and polynomial closure, 2026-10-15

The [complete solver runtime](../Signatures/Runtime/BackendSchnorrROMSolverBudget.lean)
now composes actual setup, the installed two-run fork and guarded extraction.
`code_bound_of_resources` concludes `Bounds` for `NativeSolver.code`, with the
original input encoding condition and a returned scalar of size at most
`3 * width`. It takes the attacker's measured execution resources, first/replay
sampler resources, backend encoding/control laws and primitive-operation contracts.
No completed pass, selector, fork, extractor or solver budget is supplied.

[Setup accounting](../Signatures/Runtime/BackendSchnorrROMSolverSetup.lean)
charges packing the generator/public key and the local call itself.
[Extraction primitive contracts](../Signatures/Runtime/BackendSchnorrROMExtractionComponentBudget.lean)
bound point/scalar comparison, field subtraction/division and zero; field
operations also preserve the required scalar encoding bound. The
[local expression proofs](../Signatures/Runtime/BackendSchnorrROMExtractionLocalCost.lean)
charge the actual guard, candidate and branch expressions.
[Fold bounds](../Signatures/Runtime/BackendSchnorrROMExtractionFoldCost.lean)
cover both empty and singleton lists, including their zero seeds and retained
environments. The successful fork's shape and completed-pass invariants provide
these length and encoding bounds; no message-space traversal occurs.

The [complete expression certificate](../Signatures/Runtime/BackendSchnorrROMExtractionExpressionBudget.lean)
counts both caches, both outputs, guard control and intermediate scalar encodings.
The [extractor runtime](../Signatures/Runtime/BackendSchnorrROMExtractionBudget.lean)
then charges framing, selection, successful scalar return, failed-guard fallback
and failed-fork fallback. Its only supplied code budget is the original scalar
sampler. The complete solver derives that budget from the original sampler's
execution profile and composes every setup/sequence/control cost internally.

The [whole-solver polynomial theorem](../Signatures/Runtime/BackendSchnorrROMSolverPolynomial.lean)
bounds the exact `resourcesTime` formula used in the complete runtime theorem.
Both pass executions, fork, extraction and fallback budgets are derived from
original numerical resource families and polynomial backend overhead. It does
not assume any completed component is polynomial, constrain numeric random arity,
or fix curve/message types across security parameters.

[Solver regression guards](../SignaturesTest/SchnorrROMSolver.lean) check the actual
complete runtime and encoded-output conclusion, both original resource records,
measured attacker execution and primitive selector/extractor contracts. They reject
hidden completed-component budgets, arithmetic-attacker certificates, finite
message domains and finished-component polynomial premises. All new local and
complete proofs have only the standard axiom footprint. Existing executable
examples cover successful extraction, empty outputs and both fallback paths.

Remaining: derive stored-code polynomial closure from original descriptions,
construct the fixed-backend executable witness using the proved source/runtime/code
bounds, and connect concrete hardness and public/family security. The nonzero-nonce
variant remains separate. These results are conditional on the declared backend
laws; a conventional-machine instantiation is a separate stronger claim.

Validation: all eight new proof modules, the expanded solver regression file and
the aggregate import pass without warnings under serial `-j1 -M8192` and default
proof limits.

### Schnorr ROM polynomial code, executable witness and concrete hardness, 2026-10-15

[Numerical description inputs](../Signatures/Runtime/BackendSchnorrROMDescriptionInputs.lean)
now project the original primitive realizers, sampler code, caller initialization/
head/update code, boundary conversions, request/reply tags, uniform/private sampling
ports and result injections. `codeDescription_eq` proves that the numerical
`DescriptionInputs.solver` formula equals the existing complete native stored-code
bound. This is an exact bridge, not an assumed finished-component estimate.

[Generic structural closure](../Signatures/Runtime/BackendDescriptionPolynomial.lean)
proves polynomial descriptions for fixed expressions, variables, argument frames
and effectful reduction programs from original operation/effect descriptions.
It imposes no syntax restriction on the arbitrary caller. The
[whole-solver code theorem](../Signatures/Runtime/BackendSchnorrROMDescriptionPolynomial.lean)
uses these lemmas for the fixed cache/tape/controller bodies, deriving polynomial
stored code from original description families, structural allowance, query/fuel
allowances and backend expansion. No completed pass, handler, fork, extractor or
solver description is assumed polynomial. The numerical projection permits varying
curve and message types.

The [general DLog source algorithm](../Signatures/Runtime/BackendSchnorrROMReduction.lean)
uses its generator input, matching the native solver at every input. The named
lazy reduction captures the scheme generator instead. At that generator the full
computations agree, and `reduction_experiment` proves exact equality of their DLog
experiments. This permits hardness for a single executable without assuming equality
at unrelated generators.

The [executable theorem](../Signatures/Runtime/BackendSchnorrROMSolverWithin.lean)
constructs `Within` in the common fixed backend from measured caller/sampler
resources, primitive/encoding/control contracts, description laws and the caller's
implementation law. It derives full runtime, full stored code and source equality
internally. A total encoded-input cap implies both configuration-component bounds;
the internal width must cover that cap. The resulting program realizes the general
source reduction at every input, and is time-bounded on every supported execution
within the cap. No prebuilt solver certificate is an assumption.

The [DLog resource class](../Signatures/Runtime/BackendSchnorrROMDLog.lean) additionally
requires every challenge to fit the input cap. A size lemma derives this from
group/unit/header encoding bounds. The
[concrete security endpoint](../Signatures/Runtime/BackendSchnorrROMSecurity.lean)
constructs the actual solver certificate before applying DLog hardness, then uses
the experiment equality and existing lazy-ROM probability theorem. It preserves
`eps * (eps/(qH+1) - 1/|F|) ≤ epsilon`, where `eps` is forgery probability minus
the original `qS*(qS+qH)/|F|` signing loss, with truncated ENNReal subtraction.
Attackers remain unrestricted and message types arbitrary.

[Resource/security regression guards](../SignaturesTest/SchnorrROMResources.lean)
check the whole source/time/code connection, original description records,
fixed-backend hardness, exact experiment equality and standard axioms. They reject
supplied finished-solver budgets/witnesses, algebraic restrictions, finite message
domains and finished-component polynomial premises. All seven new proof modules,
the resource regression file and aggregate import pass without warnings under
serial `-j1 -M8192` and default proof limits.

Remaining: expose the simple public ROM statement and derive nonuniform family
security from these pointwise certificates, polynomial time/code and the quadratic
forking bound. The nonzero-nonce variant and final API/documentation retirement
remain separate. A conventional-machine instantiation remains a stronger claim
than these conditional fixed-backend theorems.

### Schnorr ROM public statement and nonuniform family security, 2026-10-15

The [public ROM theorem](../Signatures/Schnorr/Statement.lean) now takes exactly
four explicit inputs: curve, security parameter, query allowances and unrestricted
adversary. Its conclusion displays the original lazy EUF-CMA game, signing loss,
`(qH+1)/|F|`, and the square root of `(qH+1)` times the DLog success bound at the
derived runtime. The [quadratic theorem](../Signatures/Schnorr/Proofs/GeneralROM.lean)
is retained. [Forking inversion](../Signatures/Model/ForkingLoss.lean) proves the
convenient direct inequality, including zero hash queries and infinite upper bounds.

The [ROM parameters](../Signatures/Schnorr/GeneralROMParameters.lean) fix only
original backend/encoding/sampler/primitive contracts and attacker allowances.
They impose no AGM or restricted arithmetic-source requirement. The attacker
provides its arbitrary local implementation, source correspondence, measured
execution and query bounds, and stored-code allowance. A
[description monotonicity proof](../Signatures/Runtime/BackendSchnorrROMDescriptionAllowance.lean)
derives the entire solver's uniform code bound from that caller allowance.
The [execution model and game](../Signatures/Schnorr/GeneralROMSecurityModel.lean)
are independently declared for ROM; the
[curve's group sampler](../Signatures/Model/CyclicCurveSampling.lean) follows from
its existing scalar sampler and generator bijection. Supporting public proofs
stay in [their own file](../Signatures/Schnorr/Proofs/GeneralROMSecurity.lean).

The [nonuniform DLog class](../Signatures/Runtime/BackendSchnorrROMDLogFamily.lean)
uses one fixed backend and polynomial time, full stored code/advice and input
bounds. [Family resources](../Signatures/Schnorr/GeneralROMFamilyResources.lean)
bound original caller work, queries, widths, sampling profiles, primitive costs
and stored descriptions; complete solver time/code and actual family membership
are derived. No numerical random-arity, message-universe or finished-solver
polynomial premise is added. Curve, group and message types can vary with the
security parameter.

The [family theorem](../Signatures/Schnorr/GeneralROMFamilyStatement.lean) now
concludes negligible original-game forgery from these resources, nonuniform DLog
hardness and negligible inverse field size. Its
[separate proof](../Signatures/Schnorr/Proofs/GeneralROMFamily.lean) uses the actual
native solver family and exact DLog experiment correspondence.
[Square-root negligibility](../Signatures/Model/ForkingNegligible.lean) closes the
asymptotic implication of the original quadratic forking bound.

[Public/family regressions](../SignaturesTest/SchnorrGeneralROMStatement.lean)
check the four-input API, visible losses/budgets, original-game correspondence,
standard axioms, varying family types and fixed-backend hardness. They reject
AGM restrictions, finite message/group premises and supplied finished solver
budgets. The existing AGM public regression and aggregate import are also checked
serially under default proof limits.

### Nonzero-nonce lazy security and signing implementation, 2026-10-15

The [generic lazy Fiat--Shamir algorithm](../Signatures/Schnorr/LazyFiatShamir.lean)
accepts the actual protocol and signing simulator. Its
[security proof](../Signatures/Schnorr/Proofs/LazyFiatShamir.lean) derives a finite
reference cover internally, proves equality of the complete extracted-witness
law and key-averaged experiment, and applies the established complete-private-tape
bound. The cover is absent from the algorithm. Private randomness is retained
across both executions, including the post-challenge suffix; challenge replay
and final verification keep their existing semantics. The original full-field
algorithm is definitionally the corresponding specialization.

The [nonzero algorithm](../Signatures/Schnorr/NonzeroLazyROMReduction.lean) installs
the exact finite repair simulator from the separate source scheme. Its
[probability endpoint](../Signatures/Schnorr/Proofs/NonzeroLazyROM.lean) preserves
`qS*(qS+qH)/(|F|-1)` signing loss and the full-field `1/|F|` fork term. It takes
ordinary signing/hash allowances, with no finite message domain, private-family
list, private-query capacity or attacker-language certificate. Group finiteness
is derived internally from the finite field and generator bijection.

The [signing syntax](../Signatures/Runtime/SchnorrNonzeroSigning.lean) executes two
field draws and one unconditional nonzero draw. It repairs commitment and response
together, then programs the repaired target while preserving earlier cache entries
on collision. The [native program](../Signatures/Runtime/BackendSchnorrNonzeroSigning.lean)
proves exact store sequencing and a full stored-description bound counting both
field sampler occurrences and the nonzero sampler. Polynomial code growth follows
from original sampler and primitive descriptions. Its
[source theorem](../Signatures/Runtime/BackendSchnorrNonzeroSigningSource.lean)
identifies the compiled kernel with the established simulator plus cache update.
The [local repair bound](../Signatures/Runtime/BackendSchnorrNonzeroRepairCost.lean)
charges the identity comparison, selected arithmetic, projections and retained
branch environment, with output-size and polynomial runtime proofs. These local
results do not yet certify the full signing/replaying solver.

[Field-growth closure](../Signatures/Model/NonzeroFieldGrowth.lean) proves
`1/(n-1) <= 2/n` for `n >= 2`, hence the nonzero signing loss needs no stronger
field-growth assumption. [Regressions](../SignaturesTest/SchnorrNonzeroLazyROM.lean)
check uncountable messages, adaptive private sampling, the final hash slot,
full-field specialization, both repair branches, unconditional third-draw order,
collision preservation, zero public keys and standard axiom footprints.
All nine new implementation/proof modules, the new regression, the existing
nonzero regression and aggregate import pass serially under default proof limits.
The existing regression emits two pre-existing deprecated-probability-API warnings;
the new targets emit none.

### Nonzero signing runtime and finite-cache replay, 2026-10-15

The [complete signing bound](../Signatures/Runtime/BackendSchnorrNonzeroSigningBudget.lean)
now derives runtime for the actual compiled three-draw signer from the original
sampler budgets and primitive/local structural costs. Four separate store
invariants describe the initial state and the states after each draw. Commitment
arithmetic, repair, cache traversal, argument construction, return construction
and all retained environments are charged. The cache's entry width stays fixed;
capacity grows by at most one. Polynomial closure follows from the original
width, capacity, primitive times, three sampler times and joint overhead family.
[Local adapter bounds](../Signatures/Runtime/BackendSchnorrNonzeroSigningParts.lean)
refer to the actual expressions. Storage-size lemmas are separate from runtime
composition so the proof checks under the default heartbeat limit.

The [finite-cache pass](../Signatures/Runtime/SchnorrNonzeroListPass.lean) uses the
actual repaired nonzero simulator and preserves first entries on programming
collisions. Its adaptive handler/state correspondence reaches the original
Fiat-Shamir trace, including the final live hash and verification. The
[finite replay reduction](../Signatures/Runtime/SchnorrNonzeroListReduction.lean)
has exactly the named nonzero lazy solver's computation, including failed
selection, changed-challenge checks, both runs, extraction and fallback. The
original probability theorem therefore applies directly to this finite solver,
with signing loss `qS*(qS+qH)/(|F|-1)` and fork inverse `1/|F|` unchanged.

[Capacity bounds](../Signatures/Runtime/SchnorrNonzeroListGrowth.lean) prove
managed-cache growth at most `qS + qH` and live-cache growth at most `qH + 1` for
arbitrary adaptive callers. Private draws grow neither cache. No finite message
or group universe, private-family cover or attacker source syntax is required.
These source-level results do not assert a whole-solver native runtime bound.

[Signing regressions](../SignaturesTest/SchnorrNonzeroSigningBudget.lean) require
the actual code and derived time in the conclusion, allow exactly the three
original sampler budget premises, and check their distinct invariant transitions.
[Replay regressions](../SignaturesTest/SchnorrNonzeroLazyROM.lean) check complete
solver equality and cache capacities with uncountable messages and adaptive
million-sized random ranges, preserve the actual nonzero simulator/game, and
reject finite-domain requirements. All new theorems have only the standard
Lean axioms. The five new implementation modules, both affected regressions and
aggregate import are checked serially within the existing resource limits.

### Installed nonzero private samplers and common-store signer, 2026-10-15

The [installed signing program](../Signatures/Runtime/BackendSchnorrNonzeroPrivateSigning.lean)
now transforms both original scalar-return sampler programs through the existing
raw private-tape handler, then installs them in the actual three-draw signer.
Two field calls and one nonzero call advance the same tape in order. Its source
law holds for every saved/remaining tape and equals the repaired nonzero
simulator with first-entry-preserving cache programming. Hashing still uses its
distinct challenge-family handler. Stored-code accounting includes both field
sampler occurrences, the nonzero sampler and all tape-handler copies.

The [installed runtime theorem](../Signatures/Runtime/BackendSchnorrNonzeroPrivateBudget.lean)
uses separate original work, visit and query bounds for the field and nonzero
samplers. It derives all three transformed sampler budgets internally at their
successive capacities. The final saved capacity is
`savedCap + 2*fieldQueries + nonzeroQueries`; the remaining-tape capacity is
preserved. Width, primitive, interface and routing contracts charge all tape
traversals, dynamic request/reply conversions, local contexts and signer work.
There is no completed-component budget premise. The
[numeric time/code formulas](../Signatures/Runtime/BackendSchnorrNonzeroPrivatePolynomial.lean)
have polynomial closure from original resource families; numerical random arities
and loop counters do not themselves need polynomial magnitude.

The [common-store signer](../Signatures/Runtime/BackendSchnorrNonzeroComponents.lean)
now installs this actual kernel between the executed input/output adapters. Its
source theorem preserves the configuration, untouched live cache and complete
tape while matching the nonzero finite-pass handler. Its
[complete runtime](../Signatures/Runtime/BackendSchnorrNonzeroComponentsBudget.lean)
combines the original-resource kernel proof with adapter and routing costs;
[polynomial time/code closure](../Signatures/Runtime/BackendSchnorrNonzeroComponentsPolynomial.lean)
uses the same original families. The common-store adapter theorem was generalized
to an arbitrary proved signing core; the existing full-field theorem retains its
original statement and follows as a specialization.

[Regressions](../SignaturesTest/SchnorrNonzeroPrivateSigning.lean) execute the
actual assembled signer on interleaved challenge/field/nonzero families, with
both repair branches, colliding caches, an untouched live cache, a saved prefix
and an unconsumed private suffix. They require both original execution profiles,
reject assumed transformed budgets and finite-domain/attacker-syntax premises,
and check installation of both original samplers into the private handler.
All new theorem axiom footprints are standard. The implementation modules,
new regression, existing full-field handler regression and aggregate import
are checked serially under the existing compiler resource limits.

### Nonzero dispatcher, general caller and complete native pass, 2026-10-15

The [actual dispatcher](../Signatures/Runtime/BackendSchnorrNonzeroHandler.lean)
installs the three-draw nonzero signer and reuses the unchanged random/hash
components. A generic executed-signing parameter was factored out of the shared
routing proof; the old full-field API and behavior remain unchanged. The new
handler's complete computation, dependent reply, both caches, configuration and
replay tape equal the nonzero source handler. Arbitrary implemented callers
inherit exact source correspondence, with termination derived from measured
query resources rather than a separate cover or arithmetic-language restriction.

The [dispatcher budget](../Signatures/Runtime/BackendSchnorrNonzeroHandlerBudget.lean)
is derived from both original sampler profiles and local primitive/port/encoding
contracts. One request grows each cache by at most one entry and saves at most
`2*qField + qNonzero + 1` tape cells; the extra one covers random/hash requests.
The [reservation theorem](../Signatures/Runtime/BackendSchnorrNonzeroHandlerReserve.lean)
preserves room for all future adaptive calls while charging runtime at fixed
maximum capacities. The
[arbitrary caller resource theorem](../Signatures/Runtime/BackendSchnorrNonzeroCallerResources.lean)
recovers request, state and head invariants from the attacker's measured execution
and representation recovery laws. It derives the full caller cost, including
original attacker work, dispatch, initialization, loop control and retained state.
No completed-handler/caller runtime premise remains at this endpoint.
[Caller return sizes](../Signatures/Runtime/BackendSchnorrNonzeroCallerOutput.lean)
are also recovered from measured resources, including return at zero fuel.

The [complete native pass](../Signatures/Runtime/BackendSchnorrNonzeroPass.lean)
now executes setup, this actual nonzero caller, output conversions and final
live-cache hashing. Its source theorem is equality with the nonzero finite-cache
pass on every raw tape, and sufficient measured query fuel guarantees a singleton
completed result. Its
[complete runtime/output bound](../Signatures/Runtime/BackendSchnorrNonzeroPassBudget.lean)
charges all these programs from original resources, including the extra sampler
and repair costs. [Stored-code bounds](../Signatures/Runtime/BackendSchnorrNonzeroPassDescription.lean)
include both original samplers, the attacker's description, all request/reply and
pass boundary conversions, and cutoff/final-hash code.
[Dispatcher](../Signatures/Runtime/BackendSchnorrNonzeroHandlerPolynomial.lean),
[caller](../Signatures/Runtime/BackendSchnorrNonzeroCallerPolynomial.lean) and
[complete pass runtime](../Signatures/Runtime/BackendSchnorrNonzeroPassPolynomial.lean)
have polynomial closure from original resource families. Numeric sampling arities
and loop-counter magnitudes are not required to be polynomial.

[Regressions](../SignaturesTest/SchnorrNonzeroPrivateSigning.lean) now execute all
three dispatcher branches, including nonzero commitment repair, malformed raw
random replies and conflicting managed/live cache values. The theorem guards
require exact nonzero source/pass correspondence, both original sampler profiles,
measured arbitrary attacker execution, future-call reservations including the
nonzero draw, and derived complete runtime formulas. They reject finished-component
budget premises, restricted-attacker syntax and finite-universe requirements, and
check the actual dispatcher/pass definitions for accidental full-field substitution.
The new implementation modules, expanded regression, existing full-field handler
and caller regressions, and aggregate import are checked serially within the
existing compiler resource limits; theorem axiom footprints remain standard.

### Complete nonzero replaying solver and concrete hardness, 2026-10-15

The [original pass resource records](../Signatures/Runtime/BackendSchnorrNonzeroPassResources.lean)
retain both sampler execution profiles and the full adaptive tape reservation.
Their [numeric time inputs](../Signatures/Runtime/BackendSchnorrNonzeroPassTime.lean)
derive complete pass polynomial runtime without restricting numeric sampling
arities or requiring a finite message universe.

The [actual fork](../Signatures/Runtime/BackendSchnorrNonzeroFork.lean) installs
both nonzero passes in the generic replay controller. Exact source equality and
output shape are proved from measured arbitrary-caller execution and the two
original sampling laws. Its [complete runtime bound](../Signatures/Runtime/BackendSchnorrNonzeroForkBudget.lean)
derives both pass, selector and replacement-sampler budgets internally, retaining
the distinction between narrow tape entries and complete controller frames.
[Stored code](../Signatures/Runtime/BackendSchnorrNonzeroForkDescription.lean) and
[polynomial runtime](../Signatures/Runtime/BackendSchnorrNonzeroForkPolynomial.lean)
charge the complete installed fork.

The [complete solver](../Signatures/Runtime/BackendSchnorrNonzeroSolver.lean)
executes setup, that fork, guarded extraction and both fallback paths. Its entire
computation equals the named nonzero lazy reduction; it uses the original field
sampler for replacement challenges and extraction fallback. The
[runtime/output theorem](../Signatures/Runtime/BackendSchnorrNonzeroSolverBudget.lean)
and [stored-code theorem](../Signatures/Runtime/BackendSchnorrNonzeroSolverDescription.lean)
are derived from original resources. Both [runtime](../Signatures/Runtime/BackendSchnorrNonzeroSolverPolynomial.lean)
and [stored code](../Signatures/Runtime/BackendSchnorrNonzeroDescriptionPolynomial.lean)
have polynomial closure. The description proof uses a proved numerical envelope
over shared component formulas and both actual signing programs; it assumes no
finished solver budget.

The [fixed-backend certificate](../Signatures/Runtime/BackendSchnorrNonzeroSolverWithin.lean)
combines exact semantics and full runtime/code bounds. The
[concrete security theorem](../Signatures/Runtime/BackendSchnorrNonzeroSecurity.lean)
constructs that witness before applying DLog hardness. The signing loss remains
`qS*(qS+qH)/(|F|-1)` and the quadratic forking loss still uses `1/|F|`.
The [original description inputs](../Signatures/Runtime/BackendSchnorrNonzeroDescriptionInputs.lean)
and [caller allowance lemma](../Signatures/Runtime/BackendSchnorrNonzeroDescriptionAllowance.lean)
prepare the remaining short public and nonuniform family interfaces.

[Complete-solver regressions](../SignaturesTest/SchnorrNonzeroSolver.lean) cover
adaptive private sampling with an uncountable message type, exact computation
correspondence, both original sampling profiles, actual nonzero pass installation,
derived executable membership and the original probability denominator. They
reject finite-universe, restricted-attacker syntax and finished-component budget
premises and check standard axiom footprints. All 16 new implementation modules,
the new regression, the existing full-field fork and solver regressions, and the
aggregate import pass serially under the existing compiler limits. Their final
logs contain no warnings or errors.

### Nonzero Schnorr public and nonuniform family endpoints, 2026-10-15

The [original-resource parameters](../Signatures/Schnorr/GeneralNonzeroROMParameters.lean)
package both sampling programs, separate nonzero first/replay pass contracts,
primitive/encoding laws and attacker allowances. The unrestricted attacker supplies
its own arbitrary implementation, execution, stored-code/advice and query proofs.
There is no finite-message or algebraic premise and no completed solver budget.
[The resource proof](../Signatures/Schnorr/Proofs/GeneralNonzeroROM.lean) constructs
the actual nonzero fixed-backend certificate, then proves the original quadratic
bound and its square-root consequence.

`Schnorr.NonzeroNonce.rom_security` in [Statement.lean](../Signatures/Schnorr/Statement.lean)
has four explicit inputs: curve, security parameter, query allowances and
unrestricted adversary. Its conclusion displays the actual game, signing loss
with denominator `|F|-1`, forking loss with denominator `|F|`, and DLog success
at the derived reduction time. The [model](../Signatures/Schnorr/GeneralNonzeroROMSecurityModel.lean)
exposes the game and fixed-backend supremum, and [public proofs](../Signatures/Schnorr/Proofs/GeneralNonzeroROMSecurity.lean)
remain separate. The shared execution-model structure introduces no full-field
resource assumption. [Nonzero curve sampling](../Signatures/Model/CyclicCurveNonzeroSampling.lean)
provides the semantic uniform source distribution; actual sampling code and cost
remain original execution contracts.

[Family resources](../Signatures/Schnorr/GeneralNonzeroROMFamilyResources.lean)
derive polynomial complete solver time/code and actual nonuniform membership in
one fixed backend. The [asymptotic statement](../Signatures/Schnorr/GeneralNonzeroROMFamilyStatement.lean)
concludes negligible original-game forgery under DLog hardness and negligible
inverse field size. Its [proof](../Signatures/Schnorr/Proofs/GeneralNonzeroROMFamily.lean)
derives negligible inverse nonzero-field size internally. Fields, groups and
message types may vary with the security parameter.

[Public/family regressions](../SignaturesTest/SchnorrGeneralNonzeroROMStatement.lean)
check the short interface, separate proof placement, both original samplers,
actual nonzero pass contracts, inspectable game/hardness definitions, original
signing denominator, fixed backend and derived polynomial membership. They reject
completed-solver budgets, restricted attacker syntax, algebraicity, finite-message
requirements and accidental full-field resource substitution. The eight new
implementation modules, updated public statement, new regression, existing ROM
and AGM public regressions, and aggregate import pass serially within the existing
compiler limits. All 13 final compiler logs are empty; axiom footprints remain
standard. This is targeted verification, not the final full-suite result.

### Eager AGM API retirement, 2026-10-15

The BLS/OOPS/Proximity `*_lazy_agm_of_dlog_machine_hardness` wrappers are removed,
as is BLS's `ArithmeticAttackerCertificate` alias. Their public replacements are
`agm_security` and `agm_security_two_budgets` in each scheme's `Statement.lean`.
The OOPS/Proximity `ArithmeticStatement` paths now import the current public
statements without restoring retired declarations. The arithmetic-source BLS
co-CDH theorem and Schnorr's separately scoped endpoints remain.

Original eager probability definitions and source/compiler/resource lemmas remain
for reference and exact coupling. Their regression fixtures still check both
complete eager solver certificates. Public axiom checks now cover all seven
current route statements. Assumption guards reject the retired wrappers and alias;
the retained arithmetic co-CDH interface keeps its source-certificate checks.
The [migration guide](API-MIGRATION.md) explains why migration requires the new
backend/attacker/hardness contracts rather than a textual renaming.

The updated BLS arithmetic module and 13 sequential integration targets passed:
three public statements, two migration modules, aggregate imports, original AGM
source/compiler fixtures, assumption/retirement guards, all-seven endpoint axiom
checks, BLS and weighted general interfaces, retained co-CDH certificate and
arbitrary-message transport. Logs are in `/private/tmp/agm-api-retirement-check`;
only the pre-existing upstream representation `#check` emits informational output.
The full suite and completion audit are still pending.

### Integration verification, 2026-10-16

The fresh serial rebuild at `06b5a93` passed all 923 local library modules and
130 regression modules. All four public statement modules (covering seven
concrete routes), all seven family endpoints, the full native solver certificate
chains, and their assumption/axiom guards passed. The run checked source-snapshot
equality before reporting success. The pinned third-party dependencies were reused.

The sharper BLS cache proof and six supported-outcome regressions now also pass,
with empty logs. They connect the singleton weighted invariant to the actual
BLS computations and cover both branches over infinite messages. Current-tree
verification passed all 1,054 targets using source/dependency fingerprints: it
reused unchanged successful baseline targets and recompiled every changed/new
target and dependent. The final source snapshot was unchanged. The new total is
924 library modules and 130 regressions.

Both runs use one compiler at a time, `-j1 -M8192`, with the pinned toolchain and
dependencies. No compiler-limit overrides were added; older scoped source settings
remain unchanged. Older probability modules emit reviewed API deprecations and
proof-style/unused-argument warnings. The upstream compatibility test prints its
expected `#check AGM.GroupRepresentation` output. New sharp-cache proof/test logs
are empty; the entire suite is not claimed to be warning-free.

The completion audit traced the shared caller/encoding/implementation class,
all route-to-hardness connections, fixed-backend family scope, finite-domain proof
transport, and the original OOPS admissibility and Proximity collision conditions.
It covered complete native BLS/weighted extraction, Schnorr AGM's all-shape
extraction and whole-solver composition, and ROM's installed two-pass replay and
sampler costs, including the nonzero route. The measured attacker and primitive
resources imply the completed solvers' runtime, representation, and stored-code
bounds; these final bounds are not premises. Regression gates cover repeated
queries, unseen targets, coefficient shape, adaptive reply paths, malformed
outputs, and private random families first used during replay.

All current-tree logs have been reviewed: no errors, admissions or unclassified
output remain. The requirement-by-requirement audit is complete. The conditional
fixed-backend plan has no remaining proof or integration tasks. Conventional-machine
adequacy is a separate stronger claim, and Proximity retains its collision
qualification.

### Completion evidence map, completed 2026-10-16

The numbers below refer to the 120 checklist items at the end of this plan.
This maps every item to its proof and verification scope. All listed final
regression gates passed in the completed integration verification. The detailed
checkpoints retain component-level source links and earlier targeted results.

The co-CDH review traced `program_within_of_resources` through measured caller
reachability, complete native handler and terminal budgets, source equality at
every challenge, and the stored-description bound. Its primitive contracts price
individual operations and samplers; they do not assume that a cache, dispatcher,
or completed solver is efficient. Family regression guards were also inspected
for all seven routes: actual original resources, fixed backend, polynomial
code/advice, preserved game/loss, and the standard axiom footprint.

| Checklist items | Source evidence and final regression gate |
| --- | --- |
| 1 | [Measured callers](../Signatures/Runtime/GeneralCallerResources.lean), [executable membership](../Signatures/Runtime/BackendWithin.lean), [nonuniform convention](../Signatures/Runtime/BackendFamily.lean); [caller tests](../SignaturesTest/GeneralCaller.lean), [backend assembly tests](../SignaturesTest/BackendAssembly.lean). |
| 2 | [Complete co-CDH certificate from original resources](../Signatures/Runtime/BackendCoronSolverResources.lean), [source equality](../Signatures/Runtime/BackendCoronSolverCorrectness.lean), [whole runtime](../Signatures/Runtime/BackendCoronSolverBudget.lean), [stored code](../Signatures/Runtime/BackendCoronSolverDescription.lean); [family scope tests](../SignaturesTest/BackendFamilies.lean). |
| 3 | [Lazy BLS source](../Signatures/BLS/Spec/LazyAGMReduction.lean), [list refinement](../Signatures/BLS/Proofs/LazyAGMList.lean), [arbitrary-message transport](../Signatures/BLS/Proofs/LazyAGMArbitraryMessages.lean); [adaptive/cache regressions](../SignaturesTest/LazyAGMReduction.lean). |
| 4–11 | [Native replies](../Signatures/Runtime/BackendLazyAGMReplyBudget.lean), [chronological rows](../Signatures/Runtime/BackendTokenRows.lean), [private reads](../Signatures/Runtime/BackendLazyAGMReadBudget.lean), [good](../Signatures/Runtime/BackendLazyAGMGoodExtractionBudget.lean)/[bad](../Signatures/Runtime/BackendLazyAGMBadExtractionBudget.lean) complete extraction; [native extraction regressions](../SignaturesTest/BackendLazyAGMExtraction.lean). |
| 12–15 | [Caller resources](../Signatures/Runtime/BackendLazyAGMCallerResources.lean), [complete native witnesses](../Signatures/Runtime/BackendLazyAGMSolverWithin.lean); [whole-solver tests](../SignaturesTest/BackendLazyAGMSolver.lean). |
| 16–17 | [BLS public statements](../Signatures/BLS/Statement.lean), [family statement](../Signatures/BLS/GeneralAGMFamilyStatement.lean); [public-interface guards](../SignaturesTest/GeneralAGMStatement.lean), [family guards](../SignaturesTest/AGMFamilies.lean). |
| 18–19 | [Weighted cache theorem](../Signatures/LinearFunctional/Proofs/LazyAGMCacheBound.lean), [OOPS transport](../Signatures/OOPS/Proofs/LazyAGMArbitraryTopics.lean), [Proximity transport](../Signatures/Proximity/Proofs/LazyAGMArbitrarySlots.lean); [weighted reduction regressions](../SignaturesTest/WeightedAGMReduction.lean). |
| 20–23 | [Native term generators](../Signatures/Runtime/BackendWeightedTerms.lean), [structured comparisons](../Signatures/Runtime/BackendWeightedKeyEquality.lean), [complete reads](../Signatures/Runtime/BackendWeightedReadBudget.lean); [term](../SignaturesTest/WeightedTerms.lean) and [cache](../SignaturesTest/WeightedCache.lean) regressions. |
| 24–26 | [Evaluator budget](../Signatures/Runtime/BackendWeightedEvaluateBudget.lean), [source encoding](../Signatures/Runtime/BackendWeightedEvaluateEncoding.lean); [evaluator regressions](../SignaturesTest/WeightedEvaluate.lean). |
| 27–29 | [Coefficient expansion budget](../Signatures/Runtime/BackendWeightedCoefficientBudget.lean); [chronology/scaling regressions](../SignaturesTest/WeightedCoefficients.lean). |
| 30–33 | [Oracle budget](../Signatures/Runtime/BackendWeightedOracleBudget.lean), [caller composition](../Signatures/Runtime/BackendWeightedOracleCallerBudget.lean); [reply](../SignaturesTest/WeightedReply.lean), [handler](../SignaturesTest/WeightedHandler.lean), and [oracle budget](../SignaturesTest/WeightedOracleBudget.lean) tests. |
| 34–38 | [Good](../Signatures/Runtime/BackendWeightedGoodExtractionBudget.lean)/[bad](../Signatures/Runtime/BackendWeightedBadExtractionBudget.lean) extraction, [measured caller recovery](../Signatures/Runtime/BackendWeightedOracleCallerResources.lean), [complete solver witnesses](../Signatures/Runtime/BackendWeightedSolverWithin.lean); [extraction](../SignaturesTest/WeightedExtraction.lean) and [solver](../SignaturesTest/BackendWeightedSolver.lean) tests. |
| 39–41 | [OOPS concrete proof](../Signatures/OOPS/Proofs/GeneralAGM.lean), [Proximity concrete proof](../Signatures/Proximity/Proofs/GeneralAGM.lean), [original polynomial resources](../Signatures/Runtime/GeneralWeightedFamilyResources.lean); [public/collision guards](../SignaturesTest/WeightedGeneralSecurity.lean), [family guards](../SignaturesTest/WeightedFamilies.lean). |
| 42–44 | [Schnorr AGM finite execution](../Signatures/Runtime/SchnorrAGMExecution.lean), [capacities](../Signatures/Runtime/SchnorrAGMGrowth.lean), [complete read](../Signatures/Runtime/BackendSchnorrAGMReadBudget.lean); [finite-cache](../SignaturesTest/SchnorrAGMFiniteCache.lean) and [native read](../SignaturesTest/BackendSchnorrAGMRead.lean) tests. |
| 45–51 | [Flattening](../Signatures/Runtime/BackendSchnorrAGMFlattenBudget.lean), [hash dispatch](../Signatures/Runtime/BackendSchnorrAGMHashDispatchBudget.lean), [signing dispatch](../Signatures/Runtime/BackendSchnorrAGMSigningDispatchBudget.lean), [private randomness](../Signatures/Runtime/BackendSchnorrAGMRandomBudget.lean); corresponding [flattening](../SignaturesTest/BackendSchnorrAGMFlatten.lean), [hash](../SignaturesTest/BackendSchnorrAGMHashDispatch.lean), [signing](../SignaturesTest/BackendSchnorrAGMSigningDispatch.lean), and [randomness](../SignaturesTest/BackendSchnorrAGMRandom.lean) regressions. |
| 52–55 | [Primitive-derived handler budget](../Signatures/Runtime/BackendSchnorrAGMHandlerPrimitiveBudget.lean), [caller resource recovery](../Signatures/Runtime/BackendSchnorrAGMCallerResources.lean); [handler](../SignaturesTest/BackendSchnorrAGMHandler.lean) and [resource](../SignaturesTest/BackendSchnorrAGMResources.lean) guards. |
| 56–62 | [Complete extraction](../Signatures/Runtime/BackendSchnorrAGMExtractionBudget.lean), [measured output conversion](../Signatures/Runtime/BackendSchnorrAGMExtractionResources.lean), [whole-solver witness](../Signatures/Runtime/BackendSchnorrAGMSolverWithin.lean); [extraction](../SignaturesTest/BackendSchnorrAGMExtraction.lean) and [solver](../SignaturesTest/BackendSchnorrAGMSolver.lean) tests. |
| 63–67 | [Joint lazy fork](../Signatures/Runtime/SeededLazyFork.lean); [deferred-sampling](../SignaturesTest/SeededDeferred.lean), [joint fork](../SignaturesTest/SeededLazyFork.lean), and [actual Schnorr lazy security](../SignaturesTest/SchnorrLazyROM.lean) regressions. |
| 68–76 | [Raw tape capacities](../Signatures/Runtime/SchnorrRawTapeBounds.lean), [complete native controller](../Signatures/Runtime/BackendSchnorrRawForkBudget.lean); [raw tape](../SignaturesTest/SchnorrRawTape.lean) and [native fork](../SignaturesTest/BackendSchnorrRawFork.lean) tests. |
| 77–84 | [Original sampler resource transport](../Signatures/Runtime/BackendSchnorrPrivateSamplingResources.lean), [installed signing budget](../Signatures/Runtime/BackendSchnorrROMSigningBudget.lean); [finite-list pass](../SignaturesTest/SchnorrROMList.lean), [execution profiles](../SignaturesTest/BackendExecutionProfile.lean), [sampling](../SignaturesTest/SchnorrPrivateSampling.lean), and [kernel budgets](../SignaturesTest/SchnorrROMKernelBudget.lean) tests. |
| 85–90 | [Handler source law](../Signatures/Runtime/BackendSchnorrROMHandlerSource.lean), [caller resources](../Signatures/Runtime/BackendSchnorrROMCallerResources.lean), [complete pass budget](../Signatures/Runtime/BackendSchnorrROMPassBudget.lean); [caller](../SignaturesTest/SchnorrROMCaller.lean), [pass](../SignaturesTest/SchnorrROMPass.lean), and [original-resource](../SignaturesTest/SchnorrROMResources.lean) tests. |
| 91–96 | [Complete selector](../Signatures/Runtime/BackendSchnorrROMSelectionBudget.lean), [installed fork budget](../Signatures/Runtime/BackendSchnorrROMForkBudget.lean), [polynomial closure](../Signatures/Runtime/BackendSchnorrROMForkPolynomial.lean); [selector](../SignaturesTest/SchnorrROMSelection.lean) and [fork](../SignaturesTest/SchnorrROMFork.lean) tests. |
| 97–101 | [Complete ROM solver budget](../Signatures/Runtime/BackendSchnorrROMSolverBudget.lean), [polynomial closure](../Signatures/Runtime/BackendSchnorrROMSolverPolynomial.lean), [executable witness](../Signatures/Runtime/BackendSchnorrROMSolverWithin.lean); [whole-solver regressions](../SignaturesTest/SchnorrROMSolver.lean). |
| 102–112 | [Nonzero solver resources](../Signatures/Runtime/BackendSchnorrNonzeroSolverBudget.lean), [separate executable witness](../Signatures/Runtime/BackendSchnorrNonzeroSolverWithin.lean), [family security proof](../Signatures/Schnorr/Proofs/GeneralNonzeroROMFamily.lean); [lazy probability](../SignaturesTest/SchnorrNonzeroLazyROM.lean), [three private draws](../SignaturesTest/SchnorrNonzeroPrivateSigning.lean), [complete solver](../SignaturesTest/SchnorrNonzeroSolver.lean), and [public/family guards](../SignaturesTest/SchnorrGeneralNonzeroROMStatement.lean). |
| 113–114 | [Schnorr AGM public statement](../Signatures/Schnorr/Statement.lean), [family theorem](../Signatures/Schnorr/GeneralAGMFamilyStatement.lean); [public](../SignaturesTest/SchnorrGeneralStatement.lean) and [family](../SignaturesTest/SchnorrAGMFamilies.lean) guards. |
| 115–117 | [ROM concrete proof](../Signatures/Schnorr/Proofs/GeneralROM.lean), [family theorem](../Signatures/Schnorr/GeneralROMFamilyStatement.lean); [public/family guards](../SignaturesTest/SchnorrGeneralROMStatement.lean). |
| 118 | [Migration guide](API-MIGRATION.md), [current security-game scope](SECURITY-GAMES.md); [legacy/public assumption guards](../SignaturesTest/StatementAssumptions.lean) and [retained arithmetic fixtures](../SignaturesTest/RuntimeAGMSource.lean). |
| 119 | [Exact singleton specialization and both sharp BLS cache bounds](../Signatures/BLS/Proofs/LazyAGMCacheBound.lean); [six supported-outcome regressions, standard-axiom and arbitrary-message guards](../SignaturesTest/LazyAGMReduction.lean). |
| 120 | Completed fresh baseline rebuild (1,053 targets) and current-tree verification (1,054 targets), source-snapshot/dependency checks, all-log review, public/family axiom and assumption guards, and this requirement-by-requirement evidence map. |

The full-build manifest was checked against the actual Lake library declarations:
the baseline includes all 923 local library modules and all 130 regression
submodules, with no omitted local target. The added BLS cache module brings the
current total to 924 library modules. Third-party dependencies remain pinned and
are reused; current-tree verification checks source and dependency fingerprints.

## Implementation order and completion checks

### Verified progress, 2026-10-14

- [`GeneralCaller`](../Signatures/Runtime/GeneralCaller.lean) executes a PolyFun
  `QuantitativeRealization`, charging its initialization, head, and enabled-update
  realizers. Arbitrary continuation computation is included. `run_erase` connects
  execution to the source oracle computation under `ImplementsWithin`; fuel
  exhaustion is explicit and cannot silently become a valid source output.
- [`GeneralCallerBudget`](../Signatures/Runtime/GeneralCallerBudget.lean) proves
  handler substitution from a caller budget and per-handler certificates, with
  reply contracts, state invariants, and integer potentials. The caller budget
  quantifies over all admitted reply paths and all nonnegative query prices.
- [`GeneralCallerRefinement`](../Signatures/Runtime/GeneralCallerRefinement.lean)
  preserves exact costs and results under handler-state representation changes.
  [`GeneralCallerGrowth`](../Signatures/Runtime/GeneralCallerGrowth.lean) derives
  storage growth and quadratic overhead for handlers whose cost grows linearly
  with cache size. Execution counters are proof-only and erased exactly.
- [`GeneralCoron.generalSimulation_bound`](../Signatures/Runtime/GeneralCoron.lean)
  instantiates these results with the existing BLS co-CDH arithmetic-machine
  handlers. It derives the actual simulation cost, including cache scans, from
  the general caller budget. `generalReduction_bound` adds the final hash and
  extraction routine, including an unseen final message. Fuel exhaustion remains
  observable. These remain mixed-model accounting results rather than a complete
  general-attacker security endpoint.
- [`GeneralCoronCorrectness`](../Signatures/Runtime/GeneralCoronCorrectness.lean)
  proves exact source correspondence through the final hash and extraction.
  `generalReduction_erase_original` connects the optional result to the named
  Coron reduction; `generalSolverRun_erase` supplies its ordinary result type and
  proves the cutoff default has no effect for a certified caller. Its all-path
  bound is `generalReductionBound + 1`. The certificate concerns the original
  caller's semantics and termination, never the finished solver's efficiency.
- [`GeneralCallerTrace`](../Signatures/Runtime/GeneralCallerTrace.lean) extracts
  actual conforming execution traces from evaluator support. It proves the exact
  cost equation: backend work plus handler prices plus `2 * queries + 2` control
  charges. Separate backend-work and query-count bounds derive `Budget`; an
  upstream `RunsWithinUnder` certificate also supplies that budget directly.
  Request-dependent fees can charge encoded argument sizes. Actual executions
  inherit output-size bounds through an explicit payload-decoding size law.

### Common-backend assembly, 2026-10-14

- [`BackendProgram`](../Signatures/Runtime/BackendProgram.lean) provides finite
  effectful syntax whose local operations carry actual quantitative realizers.
  Sequencing, branching, retained values, query loops, and input-bounded iteration
  have explicit control costs. Those costs retain encoded-size arguments; copying
  is not inferred to be constant-time. Both loop forms store one body description.
- [`BackendAssembly`](../Signatures/Runtime/BackendAssembly.lean) constructs a
  native program from generic backend constructor implementations and proves its
  exact costed execution. Description expansion is proved separately from runtime.
  [`BackendBudget`](../Signatures/Runtime/BackendBudget.lean) derives all-path
  bounds from local instruction bounds and preserved loop invariants. Dynamic
  iteration is charged in its numerical count, not just its encoding length.
- [`BackendCaller`](../Signatures/Runtime/BackendCaller.lean) constructs caller
  initialization, dispatch, return/cutoff, and update code with explicit value
  routing. [`BackendCallerCorrectness`](../Signatures/Runtime/BackendCallerCorrectness.lean)
  proves the compiled program realizes the source computation with a matching
  stateful handler. [`BackendCallerBudget`](../Signatures/Runtime/BackendCallerBudget.lean)
  derives execution and description bounds from initialization, body, stop, and
  structural costs. Its local premises still need scheme-specific proofs.
- [`BackendWithin`](../Signatures/Runtime/BackendWithin.lean) fixes a common
  hardness class over the backend's actual program type, with separate input-size,
  stored-code/data-description, and online-time limits. Compilation constructs its
  witness from a proved syntax budget. Backend adequacy and the meaning of its
  size measures remain explicit model obligations.
- [`BackendExpression`](../Signatures/Runtime/BackendExpression.lean) compiles
  every arithmetic expression to actual code using primitive and generic data
  constructors, including list folds with an executable body.
  [`BackendLanguage`](../Signatures/Runtime/BackendLanguage.lean) constructs
  state-passing code for all wrapper programs, including input-bounded loops.
  [`BackendLanguageCorrectness`](../Signatures/Runtime/BackendLanguageCorrectness.lean)
  proves exact adaptive-effect semantics, preserving local environments and
  changes to the persistent store.
- [`BackendMachine`](../Signatures/Runtime/BackendMachine.lean) instantiates this
  compiler for the existing cryptographic wrapper machine. Reads, writes, argument
  frames, and initialization are constructed; field/group instructions and sampling
  have individual implementation contracts. The compiled code's erased execution
  equals the original machine's execution. This equality does not transfer the
  old arithmetic step count to backend time.
- [`BackendCoron`](../Signatures/Runtime/BackendCoron.lean) constructs the lazy
  hash/sign reply and final extraction code using this compiler. `backendReply_denote`
  preserves the joint reply/cache law, and `backendFinish_denote` preserves final
  extraction. `backendReply_cache_bound` proves that the new costed execution adds
  at most one cached message per reply. No message-universe enumeration is added.

### Derived local costs and representation bounds, 2026-10-14

- [`BackendLocalCost`](../Signatures/Runtime/BackendLocalCost.lean) states
  primitive/generic-constructor cost laws in encoded sizes. A fold pays its actual
  body code on every iteration; `foldWork_bound` derives a linear bound from a
  list-length cap and a preserved accumulator invariant.
  [`BackendLocalBound`](../Signatures/Runtime/BackendLocalBound.lean) composes
  these laws into executable-code certificates.
- [`BackendExpressionCost`](../Signatures/Runtime/BackendExpressionCost.lean)
  constructs cost certificates recursively for every expression and argument
  frame. Branches charge the selected arm, and folds charge successive accumulator
  values. The only supplied instruction certificates are for individual primitives;
  no complete expression/reduction efficiency premise is introduced.
- [`BackendLanguageCost`](../Signatures/Runtime/BackendLanguageCost.lean)
  derives certificates for the compiler's context retention/restoration, branch
  selection, and loop input/output adapters. `LocalBound.atomic` combines these
  local costs with the backend's separately charged invocation overhead.
- [`BackendCallerCost`](../Signatures/Runtime/BackendCallerCost.lean) derives
  certificates for all local caller-routing adapters. Inspection preserves the
  caller's actual head cost and adds six encoded-size charges; update preserves
  its actual update cost and adds four. These are local routing bounds, not the
  entire caller-loop or handler budget.
- [`BackendSize`](../Signatures/Runtime/BackendSize.lean) supplies explicit
  product/sum/option encoding contracts with a header-size allowance.
  [`BackendCallerSize`](../Signatures/Runtime/BackendCallerSize.lean) derives
  inspection/update overhead from caller state, head, tagged-reply, and wrapper
  store sizes. The matching-reply theorem replaces the optional update size by
  the next state's size, so caller trace bounds can supply the needed caps.
  For overhead function `c`, state cap `S`, store cap `W`, head cap `H`, reply
  cap `D`, and header allowance `h`, the added local charges are at most
  `6*c(3*S + 3*W + 2*H + 6*h)` for inspection and
  `4*c(5*S + D + 4*h)` for an enabled update.

### Additive native caller composition, 2026-10-14

- [`BackendCallerExecution`](../Signatures/Runtime/BackendCallerExecution.lean)
  proves exact costed executions for initialization, return, cutoff, and query
  dispatch. The query equation preserves the handler's joint reply/store law and
  its complete cost, then resumes the caller using that reply and updated store.
- [`BackendCallerComposition`](../Signatures/Runtime/BackendCallerComposition.lean)
  compares every assembled execution path to `GeneralCaller.run` with the same
  implemented handlers. The original caller's initialization/head/update work and
  handler work are charged once; only additional routing and control allowances
  accumulate over the loop. Early termination and the final zero-fuel readout
  are both covered, and the output and final store are preserved.
- [`BackendCallerRouting`](../Signatures/Runtime/BackendCallerRouting.lean)
  discharges those dispatch allowances using product/sum/option size laws,
  local-constructor costs, and explicit backend control-instruction costs.
  If header size, caller states, heads, tagged replies, and wrapper stores have
  encoded width at most `W`, and `c` is the monotone structural-cost bound, a
  return adds at most `20*c(32*W)`, a cutoff/readout `17*c(32*W)`, and a query
  `42*c(32*W)` beyond the caller's original local work and the handler's work.
  Initialization adds `3*c(32*W)` when its input also meets the width bound.
  The constants are conservative; copying large values remains charged.
- [`BackendCallerResource`](../Signatures/Runtime/BackendCallerResource.lean)
  combines the derived dispatch bounds with caller and per-handler certificates.
  `assembled_bound_of_width` proves the all-path bound

  ```text
  T_local + sum_k q_k * handler_price_k
    + 3*c(32*W) + (fuel + 1)*(42*c(32*W) + loop_tick)
  ```

  `assembled_within_of_width` constructs the actual backend program witnessing
  that runtime bound, exact source semantics, and the compiler's description
  bound `factor*(wiring_description + handler_description + fuel)`. Its premises
  concern the caller, primitive contracts, reachable widths, and implemented
  handlers; it does not assume the completed program's runtime bound. This
  certifies the stateful caller phase, not yet a complete signature reduction.

### Lazy cache representation and compiled scan costs, 2026-10-14

- [`BackendDataSize`](../Signatures/Runtime/BackendDataSize.lean) states list
  encoding contracts and derives size bounds from element widths and list length,
  charging every stored cell and its header. Duplicate entries remain counted.
  [`CacheInvariant`](../Signatures/Runtime/CacheInvariant.lean) proves that a
  cache access either retains the list or prepends the requested key and returned
  value. Any predicate on encountered keys is therefore preserved.
- [`BackendCoronSize`](../Signatures/Runtime/BackendCoronSize.lean) applies that
  provenance result to the compiled hash/sign replies. They preserve the challenge
  values, the message-size invariant, and the one-entry-per-list growth bound.
  For message/scalar/coin/group encoding caps `m,f,b,g`, header allowance `h`,
  and maximum list length `K`, the actual store size is at most

  ```text
  3*g + 8*h + K*(3*m + f + b + 5*h).
  ```

  The theorem also bounds the full encoded reply/store result after a lookup.
  It requires size bounds only for encountered messages, with no finite message
  universe. Repeated signing still contributes to the signed-message list even
  when both private tables reuse existing entries.
- [`BackendLookupCost`](../Signatures/Runtime/BackendLookupCost.lean) proves the
  actual compiled lookup expression's cost from the generated local certificates,
  a preserved fold-accumulator invariant, list-size laws, and the comparison
  primitive's cost. If primitive values, unit/booleans, and headers are at most
  `w` encoded units, the cache contains at most `K` entries, comparison costs at
  most `E`, and `c` bounds structural work, its conservative bound is

  ```text
  K*(E + 257*c(128*(4*K + 1)*w)) + 32*c(128*(4*K + 1)*w).
  ```

  All fold iterations and the final fold test are included. Retaining/moving
  the lookup context is charged in its encoded size, so this does not silently
  transfer the old arithmetic interpreter's linear step count to backend time.
  It is polynomial under polynomial comparison/structural-cost and size bounds;
  no work is proportional to the entire message universe.
- [`BackendCoronCost`](../Signatures/Runtime/BackendCoronCost.lean) instantiates
  that result for the scalar and coin lookup expressions used by Coron's two
  caches and final extraction. These local scan certificates are used by the
  complete cache-access bounds below.

### Complete native cache access, 2026-10-14

- [`BackendLanguageBudget`](../Signatures/Runtime/BackendLanguageBudget.lean)
  derives numeric rules for compiled returns, effect calls, binds, branches,
  and saving/restoring local context. Each rule includes native invocation,
  sequencing, retention, and local structural code, with encoded-size costs.
  Bodies still supply their own component certificates; their old arithmetic
  step counts are not reused as native costs.
- [`BackendCacheCost`](../Signatures/Runtime/BackendCacheCost.lean) applies those
  rules to the actual compiled `cacheGet` syntax. Both hit and miss paths are
  covered, including the scan, sampling, insertion, and all local context copies.
  With at most `K` entries, comparison cost `E`, primitive sampling budget `D`,
  and width cap `w` for keys, values, basic values, headers, and the ambient store,
  the complete bound is

  ```text
  K*(E + 257*c(128*(4*K + 32)*w)) + D + 133*c(128*(4*K + 32)*w).
  ```

  The returned cache has at most `K+1` entries and retains the key/value width
  bounds. Sampling retains the ambient store, so cache access provably returns
  that same store; the new cache is an output until the caller writes it.
  Only individual comparison and sampling code need primitive cost contracts.
  The entire cache budget is derived, with no finite key-universe requirement.
- [`BackendCoronCacheCost`](../Signatures/Runtime/BackendCoronCacheCost.lean)
  instantiates this result for the scalar and coin cache programs inside Coron's
  native reply routine. It uses the encountered-message invariant and bounds
  only the actual scalar/uniform sampling leaves. The surrounding reply is now
  covered by the complete handler theorem below; final extraction is also
  certified below. Full solver assembly remains open.

### Complete native Coron hash/sign replies, 2026-10-14

- `BackendLanguageBudget` now includes compiled procedure calls and a bind rule
  with separate initial and resulting store invariants. This allows a cache
  write to increase the store-size bound while charging retained environments.
  [`BackendMachineCost`](../Signatures/Runtime/BackendMachineCost.lean) derives
  the actual read/write and unary-entry adapter budgets from structural and
  data-code laws.
- [`BackendCoronArithmeticCost`](../Signatures/Runtime/BackendCoronArithmeticCost.lean)
  bounds the compiled hash, signing, and extraction expressions from individual
  group/comparison primitive certificates. Native variable access, literals,
  branch dispatch, and intermediate encodings remain charged.
- [`BackendCoronReplyParts`](../Signatures/Runtime/BackendCoronReplyParts.lean)
  decomposes the existing `machineReply` syntax, proves exact equality in both
  signing modes, and derives costs for each argument list and the write-back
  expression. Default scalar/coin initialization and conversion to a natural
  number are explicitly included.
- [`BackendCoronReplySize`](../Signatures/Runtime/BackendCoronReplySize.lean)
  bounds every retained environment and the post-write store. `StoreReady`
  requires an encoded-store cap, bounded stored keys/values, and the two cache
  length caps. `storeReady_machineState` obtains it from the existing
  encountered-message invariant and encoded-store bound. No finite message
  universe is required.
- [`BackendCoronReplyBudget`](../Signatures/Runtime/BackendCoronReplyBudget.lean)
  composes both cache calls, store read/write, final hash/sign arithmetic, context
  retention, and the unary entry adapter into `backendReply_bound`. For an
  initial store/value width cap `w`, cache-length cap `K`, message comparison
  budget `E`, primitive scalar/coin sampler budgets `D_F,D_C`, and common budget
  `P` for the seven remaining primitive-operation allowances, put

  ```text
  W = 64*(K + 2)*w
  R = c(32*W)
  reply_time <= 2*K*(E + 257*R) + D_F + D_C + 7*P + 700*R.
  ```

  This is a bound for the actual compiled `backendReply`, derived from primitive
  and representation contracts. It does not assume a whole-handler runtime
  certificate. The returned point has width at most `w`; the routine also proves
  a conservative post-write store bound. For composition across queries, the
  existing native source-state invariant and `backendReply_encoded_size` supply
  the sharper linear cache/store growth bound; the coarse local frame estimate
  need not be iterated as a store-growth recurrence.

### Complete native Coron final extraction, 2026-10-14

- [`BackendCoronContracts`](../Signatures/Runtime/BackendCoronContracts.lean)
  collects primitive-value, primitive-instruction, and sampler contracts. These
  contracts contain no whole-handler or whole-solver budget.
- [`BackendCoronStateInvariant`](../Signatures/Runtime/BackendCoronStateInvariant.lean)
  carries the encountered-message predicate and cache-count bound through a
  costed reply. Message width and store width are separate: the final hash grows
  the store without widening the assumed message-comparison domain.
  `replyProgram_invariant_bound` also certifies an inline reply call. Its proof
  removes the unary entry adapter's nonnegative work; it does not identify the
  two runtimes.
- [`BackendCoronFinishParts`](../Signatures/Runtime/BackendCoronFinishParts.lean)
  proves exact syntax equality with `machineFinish` and derives its argument
  costs. [`BackendCoronFinishSize`](../Signatures/Runtime/BackendCoronFinishSize.lean)
  bounds every retained extraction frame.
- [`BackendCoronFinishBudget`](../Signatures/Runtime/BackendCoronFinishBudget.lean)
  proves `backendFinish_bound` for the actual compiled routine. With the same
  primitive contracts as the reply, plus group subtraction, put

  ```text
  B = (8*K + 24)*w
  U = 32*B
  R = c(32*U)
  finish_time <= (3*K + 1)*(E + 257*R) + D_F + D_C + 10*P + 1000*R.
  ```

  This includes the final lazy hash, store read, scan of at most `K+1` scalar
  entries, two group operations, argument copying, retained context, and entry
  and control work. The postcondition retains message provenance, cache count
  at most `K+1`, encoded store at most `B`, and output point width at most `w`.
  The existing `backendFinish_denote` provides exact correspondence to the
  source extraction; the new runtime bound is derived independently.

### Stored wrapper descriptions, 2026-10-14

- [`BackendDescriptionLaws`](../Signatures/Runtime/BackendDescriptionLaws.lean)
  separates code-description assumptions from runtime and value-size contracts.
  Its laws bound individual structural/data constructors; composition includes
  both component descriptions and an explicit allowance. A natural literal has
  a conservative value-dependent bound, and a fold includes its body code.
- [`BackendExpressionSize`](../Signatures/Runtime/BackendExpressionSize.lean)
  derives description bounds for every compiled expression and argument frame.
  [`BackendLanguageSize`](../Signatures/Runtime/BackendLanguageSize.lean) extends
  this to state-passing programs, including every context/branch/loop adapter.
  Both branches are stored; a dynamic loop stores its body once.
  [`BackendMachineSize`](../Signatures/Runtime/BackendMachineSize.lean) adds
  sampler implementations, store operations, unary entry, and closed-machine
  initialization/exit code.
- [`BackendCoronDescription`](../Signatures/Runtime/BackendCoronDescription.lean)
  instantiates these rules for the actual native reply and extraction routines.
  With structural/data description allowance `a`, maximum description `p` for
  the instructions appearing in the wrappers, and sampler descriptions `s_F,s_C`,
  the bounds are

  ```text
  reply_description  <= s_F + s_C + 1000*a + 10*p + 100
  finish_description <= s_F + s_C + 1500*a + 14*p + 150.
  ```

  They do not assume a whole-wrapper code-size certificate. The coefficients
  are conservative; the proof uses the actual syntax and its instruction
  occurrences. The generic backend assembly theorem then charges its stated
  description-expansion factor. The primitive/sampler descriptions and allowance
  can depend on representation and parameters; polynomial family bounds still
  need to be supplied. These are local wrapper descriptions, not yet the full
  general solver's description certificate.

### Native dispatcher and indexed composition, 2026-10-14

- [`BackendCoronInterface`](../Signatures/Runtime/BackendCoronInterface.lean)
  supplies explicit executable data adapters for request decoding and tagged
  replies. A single bounded sampler accepts the runtime-selected range; the
  wrapper does not store a table of samplers for every possible range. These
  are primitive encoding/sampling boundaries with separate resource obligations,
  not a supplied implementation of the whole handler.
- [`BackendCoronHandler`](../Signatures/Runtime/BackendCoronHandler.lean)
  constructs the full randomness/hash/sign dispatcher. It retains the original
  request while the existing native reply routine updates the store, then tags
  the reply correctly. `code_denote` proves the joint reply/store law equals the
  general source handler's law after erasing its old cost labels. The theorem
  does not use that equality to transfer old runtime bounds.
- [`BackendIndexedHandler`](../Signatures/Runtime/BackendIndexedHandler.lean)
  factors an actual native dispatcher into the generic typed handler interface.
  The matching-request proof makes fallback decoding unreachable, and
  `handler_run` preserves its exact native step count. The decoder is part of
  this mathematical factorization, not extra uncharged executable work.
- [`BackendCoronCaller`](../Signatures/Runtime/BackendCoronCaller.lean)
  assembles arbitrary backend-realized caller code with the constructed
  dispatcher. `caller_erase` proves exact source simulation and final-store
  preservation, removing the visible cutoff under `ImplementsWithin`.
  This covers the stateful caller phase; challenge initialization and terminal
  extraction are not yet assembled into the complete native solver.
- [`BackendCallerDescription`](../Signatures/Runtime/BackendCallerDescription.lean)
  derives the actual generic caller description from its init/head/update
  codes, handler code, fuel literal, and structural description allowance `a`:

  ```text
  caller_description <= init + 2*head + update + handler + fuel + 55*a + 26.
  ```

  The head code occurs in both the loop body and stop program. The theorem
  charges both stored copies. Arbitrary attacker code is included explicitly.
  [`BackendCoronHandlerDescription`](../Signatures/Runtime/BackendCoronHandlerDescription.lean)
  derives the dispatcher description from its actual branches and data adapters:

  ```text
  handler_description <= 2*s_F + 2*s_C + s_dynamic + 2100*a + 20*p + 4*port + 250.
  ```

  Here `p` bounds the instructions occurring in the reply routines, `port`
  bounds the three data-adapter descriptions (the group tag occurs twice), and
  the sampler terms are their actual code descriptions. No message-domain
  enumeration appears in these bounds.
- [`BackendCallerIndexedResource`](../Signatures/Runtime/BackendCallerIndexedResource.lean)
  proves additive native composition with an invariant indexed by remaining
  execution fuel. A query can increase cache size by one and decrease fuel by
  one, preserving a bound on their sum. This avoids requiring a fixed cache cap
  to remain closed under an unbounded number of additional requests.
  The source caller's symbolic-price budget supplies its local work and query
  counts; every enabled actual handler call must satisfy the proved price cap.
  `assembled_bound_indexed_of_width` derives

  ```text
  localTime + sum(q*handlerPrice) + 3*c(32*W)
    + (fuel+1)*(42*c(32*W) + loopTick).
  ```

  `assembled_within_indexed_of_width` constructs a backend executable with that
  runtime bound, exact source semantics, and the explicit caller-description
  bound above multiplied by the compiler expansion factor. This is a generic
  composition theorem. The following native Coron results now instantiate its
  handler cost and storage obligations from primitive contracts.

### Complete native caller-phase resources, 2026-10-14

- [`BackendDispatchBudget`](../Signatures/Runtime/BackendDispatchBudget.lean)
  derives the cost of a local data adapter retaining the store, and of sum
  dispatch with a retained store. The latter adds `4*c(32*W)` for the actual
  distribution code, invocation, sequence edge, and branch selection. The
  former adds `2*c(32*W)` to the adapter's actual code cost.
- [`BackendCoronHandlerBudget`](../Signatures/Runtime/BackendCoronHandlerBudget.lean)
  derives the complete native randomness/hash/sign dispatcher bound. Its
  `PortCaps` cover only request decoding and response tagging, with explicit
  encoded widths and actual local-code costs. `DynamicSamplingCaps` bounds the
  actual sampling primitive at the requested range. A tagged response may be
  larger than its message; the contract allows `8*w` rather than requiring a
  message-plus-response to fit in the message's own width cap.
  `code_bound` instantiates the proved native reply certificate and derives

  ```text
  D = nativeReplyTime(c,w,K,E,D_F,D_C,P) + D_dynamic
        + 2*adapterTime + 40*c(32*((8*K+24)*w)).
  ```

  This is a conservative common price for all three request kinds. It includes
  saving the original message across a reply, swapping/tagging the result,
  both dispatch levels, request conversion, and every context/control charge.
  There is no premise pricing the whole dispatcher. Primitive encoding and
  sampling adequacy remain explicit contracts of the fixed backend.
- [`BackendCoronHandlerState`](../Signatures/Runtime/BackendCoronHandlerState.lean)
  proves complete-dispatcher cache provenance, preserves the challenge points,
  and bounds the updated cache by one additional entry. `code_stateInvariant`
  uses the sharper encoded-store formula already proved for the actual lists:

  ```text
  store <= 3*g + 8*h + K*(3*messageWidth + scalarWidth + coinWidth + 5*h).
  ```

  Message/value widths remain fixed as the cache grows. `ReservedState` tracks
  `cacheSize + remainingFuel <= K`; `code_reservedState` preserves that relation
  as a query consumes fuel. Choosing the global store cap from the formula
  above avoids repeatedly applying the coarse temporary-frame width bound.
  `executed_reserved_bound` transfers the native budget, tagged-reply width,
  and reserved-cache invariant to the exact typed handler used by the caller.
  This transfer preserves the actual step count; state correspondence alone
  is not used to infer efficiency.
- [`BackendCoronCallerBudget`](../Signatures/Runtime/BackendCoronCallerBudget.lean)
  now instantiates indexed composition with this constructed native dispatcher.
  `caller_bound` derives

  ```text
  native_caller_time <= localTime + sum_k queries[k]*D + 3*c(32*routeWidth)
                         + (fuel+1)*(42*c(32*routeWidth) + loopTick).
  ```

  The attacker premises concern its own realized local-work/query budget,
  reachable state/head/request sizes, and reply-dependent state transitions.
  Its internal algorithm is not restricted to the wrapper language. The
  reduction's cache invariant and full per-request cost are proved from the
  primitive contracts. The theorem preserves the fixed message-width and
  global store/cap invariant for subsequent extraction. It covers the native
  caller phase, not yet the full challenge-to-output solver or a polynomial
  family/conventional-machine instantiation.
- [`BackendCoronSolver`](../Signatures/Runtime/BackendCoronSolver.lean)
  constructs the complete native program: encoded challenge input, empty-cache
  initialization, public-key conversion, the general caller with native handlers,
  optional-result inspection, forgery conversion, final extraction, and output
  projection. Fuel exhaustion takes an explicit zero-output branch. Only actual
  local data adapters are supplied; no completed setup/terminal implementation
  or routine-level budget is assumed. Challenge data is an input, not hidden
  static code, and both terminal branches are counted in the stored program.
- [`BackendCoronSolverCorrectness`](../Signatures/Runtime/BackendCoronSolverCorrectness.lean)
  proves exact equality with the named `coronReductionLazyPK`, including
  `cacheForgeryPK`, at every challenge. `program_denote_original` and
  `program_erase_original` use the caller's termination and source-identification
  proofs. The intermediate bounded-runner bridge also preserves the cutoff.
  Source equality transfers no runtime labels.
- [`GeneralCallerOutput`](../Signatures/Runtime/GeneralCallerOutput.lean) proves
  output invariants through arbitrary reply-dependent continuations, including
  a final readout at zero remaining fuel.
  [`BackendCoronSolverOutput`](../Signatures/Runtime/BackendCoronSolverOutput.lean)
  transfers these facts to the actual native caller. Returned forgery/message
  widths follow from the caller's head/message contracts, rather than an
  assumption about the completed reduction's output.
- [`BackendCoronSolverSetup`](../Signatures/Runtime/BackendCoronSolverSetup.lean)
  derives challenge projection and empty-cache construction costs, key-encoding
  and retention costs, and the initial reserved-cache invariant.
  [`BackendCoronSolverTerminal`](../Signatures/Runtime/BackendCoronSolverTerminal.lean)
  derives optional inspection, forgery decoding, extraction, output projection,
  and cutoff costs. All copying, sequence, and branch charges are included.
- [`BackendCoronSolverBudget`](../Signatures/Runtime/BackendCoronSolverBudget.lean)
  composes these certificates into the actual complete native program. With
  `D` the derived native handler cost, `F` the derived native extraction cost,
  `B = (8*K+24)*w`, and `A` the local solver data-adapter allowance, it proves

  ```text
  time <= localTime + sum_k queries[k]*D
          + 3*c(32*routeWidth)
          + (fuel+1)*(42*c(32*routeWidth)+loopTick)
          + F + opTime + 3*A
          + 100*c(32*(inputWidth+routeWidth+B)).
  ```

  `K >= fuel` reserves cache space from the empty initial state. The global
  encoded store cap follows from fixed message/scalar/coin/group widths and
  the earlier linear store formula. Runtime hypotheses concern only actual
  caller local work/queries and primitive/representation contracts.
- [`BackendCoronSolverDescription`](../Signatures/Runtime/BackendCoronSolverDescription.lean)
  bounds the complete stored program by

  ```text
  initCode + 2*headCode + updateCode + fuel + 3*s_F + 3*s_C + s_dynamic
  + 4000*structuralCode + 40*instructionCode
  + 4*handlerPortCode + 3*solverPortCode + 500.
  ```

  The caller descriptions are actual backend code sizes; both terminal branches
  and each stored head/sampler/adapter occurrence are charged.
  [`BackendCoronSolverWithin`](../Signatures/Runtime/BackendCoronSolverWithin.lean)
  combines complete semantics, runtime, and description bounds into an actual
  fixed-backend executable for the named Coron solver. The witness works at
  every challenge; its runtime bound holds on all supported paths for every
  input within the encoding cap. No premise asserts that the finished solver
  is efficient. This conditional native resource certificate does not yet supply
  a conventional-machine adequacy theorem or polynomial family instance.
- [`GeneralCallerResources`](../Signatures/Runtime/GeneralCallerResources.lean)
  constructs the caller invariant from actual typed execution traces. A general
  `RunsWithin` bound supplies reachable state/head sizes, closure under every
  typed reply, termination, and the symbolic-price budget. The local allowance
  is measured work plus `2*queries+2` evaluator administration; the conservative
  per-kind query caps are the total query cap. Existing trace-count certificates
  remain available for tighter counts.
- [`BackendCoronCallerResources`](../Signatures/Runtime/BackendCoronCallerResources.lean)
  derives native request and final-message widths from those measured head
  sizes and an explicit `BoundaryRecovery` size-expansion law. `canonical`
  proves identity recovery when messages use the native product/sum encodings.
  Conversion code/costs remain separately charged; size recovery does not imply
  free decoding. [`BackendCoronSolverResources`](../Signatures/Runtime/BackendCoronSolverResources.lean)
  instantiates the complete `Within` theorem from these upstream caller resources,
  qualitative source implementation, and primitive/backend contracts. No
  attacker-specific invariant or completed-solver budget is supplied.
- [`BackendCoCDH`](../Signatures/Runtime/BackendCoCDH.lean) defines the native
  co-CDH resource class using that same fixed backend and explicit input, code,
  and time caps. Every challenge in the experiment must fit the input cap;
  `challenge_size` derives a cap from the point/key/unit encoding widths and
  five environment headers.
  [`BackendCoronSecurity`](../Signatures/Runtime/BackendCoronSecurity.lean)
  exposes `security_of_resources`, now imported by `Signatures`. It constructs
  the solver certificate from the general caller contract, compares its derived
  budgets with the hardness limits, and proves

  ```text
  Adv_BLS(A) <= coronFactor(qS) * epsilon_coCDH.
  ```

  The original signing bound and generator/pairing assumptions remain explicit.
  This endpoint now supports arbitrary message types through the exact
  probability transport below. Neither its native runtime nor stored code
  enumerates a message domain. The endpoint's parameter-level regression checks
  prevent a finished-solver or arithmetic-source certificate from replacing
  the general resource contract and reject a finite-message assumption.
- [`PolynomialResources`](../Signatures/Runtime/PolynomialResources.lean) defines
  fixed-polynomial resource families and a joint polynomial bound on structural
  overhead in the security parameter and frame size. The polynomial is fixed
  across parameters; a separately chosen degree at each parameter is insufficient.
  [`BackendCoronPolynomial`](../Signatures/Runtime/BackendCoronPolynomial.lean)
  proves polynomial closure of the actual derived `nativeSolverTime` and the
  full description-bound formula. The family security result below instantiates
  that numerical closure with actual compiled caller and sampler descriptions.
- [`BackendFamily`](../Signatures/Runtime/BackendFamily.lean) defines the
  nonuniform convention: a fixed backend, description measure, encodings, and
  polynomial input cap precede algorithm quantification. One program per
  security parameter implements every input, with fixed polynomial bounds on
  online time and the entire stored code/advice. `executable_family` supplies
  actual program witnesses selected by parameter, never by challenge.
  No uniform program generator or conventional-machine adequacy is asserted.
- [`BackendCoronFamily`](../Signatures/Runtime/BackendCoronFamily.lean) proves
  `nonuniform_within` for the actual lazy Coron solver from general caller
  resources and primitive contracts. Scalar/group/message types and their
  representations may vary with the security parameter. The theorem derives
  the completed solver's polynomial time/code bounds; these are not premises.
  [`BackendCoCDHFamily`](../Signatures/Runtime/BackendCoCDHFamily.lean) defines
  hardness for that same class with explicit coverage of every generated challenge.
- [`PolynomialNegligible`](../Signatures/Runtime/PolynomialNegligible.lean)
  connects fixed-polynomial resource bounds to VCVio's negligible advantage.
  [`CoronLoss`](../Signatures/Model/CoronLoss.lean) proves the exact loss is at
  most `3*(qS+1)`, including `qS=0`, so polynomial signing bounds preserve
  negligible advantage.
  [`BackendCoronFamilySecurity`](../Signatures/Runtime/BackendCoronFamilySecurity.lean)
  now exposes `Coron.NativeSolver.Family.security_of_resources` through
  `Signatures`: co-CDH nonuniform hardness plus the caller/primitive polynomial
  contracts imply negligible BLS forgery success for arbitrary message families,
  with no polynomial-cardinality premise or whole-domain
  enumeration in the runtime. The family theorem does not instantiate a
  particular curve family or a conventional computational backend.
- [`FiniteDomain`](../Signatures/Model/FiniteDomain.lean) proves a finite cover
  for all queried and returned labels across every syntactic path of a finite
  oracle program with finite answer types, also for finite public-input families.
  [`FiniteMessages`](../Signatures/BLS/CoCDH/Proofs/FiniteMessages.lean) specializes
  this to BLS and constructs a finite-subtype attacker whose message embedding
  is exactly the original interactive program. Randomness, adaptive hash/sign
  requests, and output messages are preserved; the cover also accommodates the
  appended verification hash. The cover may be exponential and is never an
  executable table or a proposed resource bound.
- [`MessageTransport`](../Signatures/BLS/CoCDH/Proofs/MessageTransport.lean)
  proves exact signing-query preservation, final-hash commutation, and real-game
  transport through injective message renaming. Scalar caches pull back along
  that map; signed-message sets use finite preimages, preserving freshness.
  [`CoronMessageTransport`](../Signatures/BLS/CoCDH/Proofs/CoronMessageTransport.lean)
  proves the same laws for the coin cache, combined Coron oracle, final extraction,
  complete named lazy solver, and co-CDH experiment. All equalities preserve
  adaptive reply-dependent requests and private randomness.
- [`FinitePublicKeys`](../Signatures/BLS/CoCDH/Proofs/FinitePublicKeys.lean)
  obtains one cover for all generated keys using the finite seed type. The
  proof-only finite-message presentation may use a covered fallback outside
  that range; neither the real attacker nor the executed solver is replaced.
  No finite-public-key assumption is introduced.
  [`ArbitraryMessages`](../Signatures/BLS/CoCDH/Proofs/ArbitraryMessages.lean)
  combines these laws with the original finite-domain probability proof, retaining
  the exact Coron loss and the same named lazy solver. Both native endpoints and
  `BLS.Statement.bls_eufcma_of_cocdh_machine_hardness` now omit `Finite M`/`Fintype M`.
  No cost formula, code budget, or hardness class is weakened by the transport.

The common assembly and hardness interfaces and generic additive composition now
compile. A conventional-machine instantiation is not asserted. Reachable-width
proofs for each scheme remain required; `W` may itself depend on caller resources.
The BLS co-CDH probability transport is complete, as are general caller composition
and its concrete/nonuniform conditional backend endpoints. Other scheme routes
remain open; the new BLS AGM solver progress is recorded below.

Validation: the existing backend/caller checks passed (3318 jobs), followed by
the new family and public-statement guards. The current public integration passed
`lake build Signatures SignaturesTest` (3830 jobs). Regressions cover initialization/terminal costs, reply-dependent
updates, visible fuel exhaustion, early return, and state-dependent dynamic-loop
charges including the final zero test, and accumulator-dependent fold charges.
An assembled one-query regression checks that handler work appears exactly once
and the final readout/zero test use the updated caller state and wrapper store.
A cache regression checks repeated signed messages over an infinite message type
are included in the size invariant even with singleton private caches.
A compiled cache-hit regression proves that replacing all effect implementations
preserves the full costed execution on a hit: no sampler is invoked.
Transitive axiom guards cover source erasure,
composition, state refinement/growth, trace/resource/size transfer, the common-backend
compiler and bounds, the cryptographic wrapper compiler, and Coron correspondence
and cache growth, derived expression/adapter costs, exact caller execution,
additive native composition, width-derived dispatch/resource certificates,
cache-entry provenance, Coron message/store-size preservation, native lookup
costs, compiled control/context budgets, complete cache-access bounds and ambient
store preservation, both Coron cache instantiations, store transitions, native
argument/read/write/entry costs, all three arithmetic expressions, retained-frame
sizes, the complete native hash/sign handler budget, inline-body transfer,
strengthened cache invariants, the complete native final-extraction budget,
generic expression/program/machine description bounds, and both actual Coron
wrapper description bounds, native dispatcher and caller correspondence, exact
costed handler factorization, complete caller/dispatcher descriptions, and indexed
native resource composition including its executable hardness-class witness,
complete native dispatcher runtime, linear encoded-store/reserved-cache
preservation, the native Coron caller-phase resource bound, complete native solver
correspondence and caller-output invariants, setup/terminal costs, full solver
runtime and stored-code bounds, its actual hardness-class executable witness,
general-resource reachability/termination/budget instantiation, boundary recovery,
the public conditional co-CDH endpoint, polynomial runtime/description closure,
family executable witnesses, negligible-loss preservation, and the nonuniform
family security endpoint. The family statement guard checks varying group types,
arbitrary-message scope, challenge coverage, actual caller resource and description
bounds, and rejects a supplied completed-solver efficiency certificate.
The finite-message transport checks use `Nat` messages, private randomness,
answer-dependent signing, repeated hashing, and an unseen final message. They
verify exact reconstruction and final-verifier coverage, guard the absence of
a finite-message premise, and check the new cover/restriction axiom footprints.
Additional transport checks instantiate infinite `Nat` messages and public keys,
preserve the adaptive signing-call budget, and reject finite-message/public-key
premises on the new probability and public concrete theorems. Axiom guards cover
every new cache/game/solver transport theorem and the final arbitrary-message bound.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
The new backend files have no admissions/custom axioms or whitespace issues.
The full repository suite passed for this public BLS integration. Existing
probability files still emit their prior deprecation/style warnings; the new
resource/security/polynomial/finite-domain modules have no warnings.
Latest targeted log: `/private/tmp/agm-arbitrary-message-public-check.log`.
Full integration log: `/private/tmp/agm-arbitrary-message-full-check.log`.

### Lazy BLS AGM progress, 2026-10-14

- [`Spec/LazyAGMReduction`](../Signatures/BLS/Spec/LazyAGMReduction.lean)
  defines both solvers without a finite-message instance. Hashing, signing,
  transcript extraction, and final-target processing share one private scalar
  cache (good branch) or one cache of independent scalar pairs (bad branch).
  Only explicitly delivered replies create representation tokens.
- [`LazyAGMReduction`](../Signatures/BLS/Proofs/LazyAGMReduction.lean) proves
  exact fixed-table interpretations of those complete adaptive programs.
  [`LazyAGMExtraction`](../Signatures/BLS/Proofs/LazyAGMExtraction.lean) proves
  the transcript sums equal the old full-domain extraction formulas, preserving
  repetitions, missing/extra coefficients, and zero-denominator behavior.
- [`LazyAGMCoupling`](../Signatures/BLS/Proofs/LazyAGMCoupling.lean) proves
  joint deferred sampling for both programs. The bad-branch pair table has the
  law of two independent uniform tables. This preserves the attacker, transcript,
  and extractor jointly. [`LazyAGMSecurity`](../Signatures/BLS/Proofs/LazyAGMSecurity.lean)
  transfers the original finite-message success bound to the named lazy solvers,
  retaining both DLog advantages and `1/|F|`.
- [`Spec/LazyAGMList`](../Signatures/BLS/Spec/LazyAGMList.lean) implements the
  private cache as an association list. [`LazyAGMList`](../Signatures/BLS/Proofs/LazyAGMList.lean)
  proves exact adaptive decoding and equality of both complete solvers to their
  symbolic-cache versions, for arbitrary message types. A hit does not sample;
  a miss prepends one binding. No full-domain table is allocated.
- [`LazyAGMQueries`](../Signatures/BLS/Proofs/LazyAGMQueries.lean) proves that
  `q` attacker requests produce at most `q` transcript entries and at most
  `2*q+1` private-interface requests in either complete program. The list-cache
  proofs derive a `2*q+1` entry cap from an empty cache. These are structural
  bounds, not a runtime certificate: local arithmetic, scans, copying,
  coefficient indexing, encoding sizes, and stored code still need prices.

- [`LazyAGMFiniteMessages`](../Signatures/BLS/Proofs/LazyAGMFiniteMessages.lean)
  now constructs finite proof covers over generated keys and every adaptive reply
  path, preserving all coefficient lists and final-target coverage. The shared
  [`CacheTransport`](../Signatures/BLS/CoCDH/Proofs/CacheTransport.lean) laws,
  [`LazyAGMTransport`](../Signatures/BLS/Proofs/LazyAGMTransport.lean), and
  [`LazyAGMGameTransport`](../Signatures/BLS/Proofs/LazyAGMGameTransport.lean)
  prove exact message-renaming laws for private randomness, transcripts,
  materialization, freshness, the actual source game, and both complete lazy
  reductions. The existing Coron transport reuses the same cache lemmas.
- [`LazyAGMArbitraryMessages`](../Signatures/BLS/Proofs/LazyAGMArbitraryMessages.lean)
  combines those laws with the finite-domain helper. Both public probability
  theorems (`security_arbitrary_messages` and its `_list` corollary) omit
  `Finite M`/`Fintype M` and any finite-public-key premise. They preserve the
  original game, solvers, and loss. The possibly exponential proof cover is
  never enumerated by an executed solver or used in a runtime bound.

The full AGM resource/composition checkbox stays open. Compile and cost
extraction, derive complete solver certificates, and compose with general
callers. The native private caches and complete reply certificates are now
checked, as recorded below.
The old eager runtime endpoints are retained until those replacements are complete.

Validation: `lake build Signatures SignaturesTest` passed (3840 jobs), log
`/private/tmp/agm-lazy-bls-full-check.log`. The new
[`LazyAGMReduction` regressions](../SignaturesTest/LazyAGMReduction.lean) cover
signing before hashing, duplicate messages, an unseen target, missing/extra
coefficients, both branches, zero denominators, adaptive requests, and cache hits.
A four-request infinite-message example has exactly two uniform draws and two
stored cells. Guards check standard axioms and reject finite-message premises on
solver definitions, representation refinements, and structural bounds. The new
modules/tests have no warnings or admissions; existing probability API warnings
remain in older dependencies. Local documentation links and whitespace pass.

The arbitrary-message integration subsequently passed the full suite (3846 jobs),
log `/private/tmp/agm-lazy-agm-arbitrary-full-check.log`. The
[`LazyAGMTransport` regressions](../SignaturesTest/LazyAGMTransport.lean) use
infinite `Nat` message/public-key types, private coins, reply-dependent signing,
repeated hashes, nonmatching coefficient-list lengths, and an unseen final target.
They check exact reconstruction, reject a cover missing the final target, and
guard the public probability theorems against finite-message/public-key premises
and nonstandard axioms. Both new transport modules and the reused Coron route
pass without new warnings. The full runtime/general-caller work remains open.

### Native BLS AGM private caches, 2026-10-14

- [`BackendPairSampling`](../Signatures/Runtime/BackendPairSampling.lean)
  constructs independent pair sampling from two actual component programs.
  Its exact denotation is the product sampler used by the probability proof.
  With component times `D_A`, `D_B` and component/unit/header width `w`, the
  derived time is `D_A + D_B + 12*c(8*w)`. The twelve charges cover local
  adapters, retention, and control. Its stored description is at most
  `s_A + s_B + 6*a + 6`; both sampler occurrences are included.
- [`BackendSampledCache`](../Signatures/Runtime/BackendSampledCache.lean)
  compiles the actual list scan, hit/miss branch, sampler call, and insertion
  using an arbitrary implemented sampler. Exact semantics preserve the
  answer/list pair and ambient store and agree with `ListCache.handler`.
  A hit preserves the full costed run when the sampler is replaced, proving
  that no sampler executes on that branch. The cache budget and encoded-output
  invariants follow from the existing complete native cache theorem. The
  stored description is at most `s_sample + s_eq + 250*a + 30`.
- [`BackendLazyAGMCache`](../Signatures/Runtime/BackendLazyAGMCache.lean)
  instantiates these programs for the good scalar cache and bad scalar-pair
  cache. Both exact denotations match the existing `privateListOracle`, over
  arbitrary message types. Write `R(w,K)=c(32*CacheCompiler.frameWidth(w,K))`,
  where `frameWidth(w,K)=4*((4*K+32)*w)`. The complete cache-access bounds are
  `K*(E+257*R(w,K)) + D_F + 133*R(w,K)` for the good branch and
  `K*(E+257*R(3*w,K)) + 2*D_F + 145*R(3*w,K)` for the bad branch. The latter
  uses width `3*w` to cover encoded scalar pairs and prices message comparison
  at that width. Here `w` bounds the ambient store as well as primitive values,
  so it will depend on the reachable-store invariant in the complete solver.
  Both accesses return at most `K+1` cells and preserve the ambient store.
  Descriptions are at most `s_F+s_eq+250*a+30` and
  `2*s_F+s_eq+256*a+36`, respectively.

These certificates cover private-cache accesses. The complete native reply
certificates and store invariants are recorded below. Coefficient/extraction
programs and general caller assembly with setup and terminal costs remain open.
No attacker arithmetic implementation or finished-solver efficiency premise is
introduced.

Validation: `lake build SignaturesTest.BackendLazyAGMCache` passed (3260 jobs),
log `/private/tmp/agm-native-lazy-cache-test.log`. The new regressions use infinite
`Nat` messages, cached zero values, duplicate keys, and a new-message miss with
two independent scalar draws. They check sampler replacement preserves native
execution on a hit, including its time. All new correctness/resource/description
theorems pass standard-axiom guards, and the cache APIs have no finite-message
premise. The new modules and tests have no warnings or admissions.

### Native BLS AGM replies and adaptive state, 2026-10-14

- [`LazyAGMReply`](../Signatures/Runtime/LazyAGMReply.lean) defines typed stores,
  cache arguments, and response expressions for both branches. Hash/sign replies
  prepend to separate transcript lists. The chronological view reverses those
  lists only in the semantic proof; extraction must implement and charge any
  reversal or coefficient matching it needs.
- [`BackendLazyAGMReply`](../Signatures/Runtime/BackendLazyAGMReply.lean)
  constructs the actual reply programs from compiled arguments, the native
  private cache, and compiled response/store updates. Its exact laws preserve
  the reply, configuration, cache, and transcript together. Hash/sign behavior
  is implemented by this code, without an opaque whole-handler primitive.
- [`LazyAGMExecution`](../Signatures/Runtime/LazyAGMExecution.lean) proves the
  flattened cache/transcript interpreter agrees with the existing nested source
  simulation for arbitrary adaptive oracle programs. The law preserves the
  output, chronological transcript, and private cache jointly, including private
  coins and arbitrary initial caches. Each hash/sign call adds exactly one reply
  and at most one cache cell. Encountered-message predicates are preserved.
- [`BackendLazyAGMSimulation`](../Signatures/Runtime/BackendLazyAGMSimulation.lean)
  transfers that adaptive correspondence to both native reply implementations.
  `backendReply_state` also transfers configuration preservation, message
  predicates, and cache/transcript growth to actual costed execution. The
  semantic oracle adapter is proved; native general-caller dispatch and its
  routing costs still need assembly.
- [`BackendLazyAGMReplyDescription`](../Signatures/Runtime/BackendLazyAGMReplyDescription.lean)
  derives complete stored descriptions for the reply programs from individual
  primitive sizes. Good replies use at most
  `s_F+s_eq+s_zero+s_scale+400*a+40`; bad replies use at most
  `2*s_F+s_eq+2*s_zero+3*s_scale+s_add+450*a+50`. Both bounds include frame
  construction, cache code, retained context, and response construction. The
  shared [`BackendWeakeningSize`](../Signatures/Runtime/BackendWeakeningSize.lean)
  lemma preserves expression-description bounds under unused context extension;
  it does not assert that retaining larger runtime frames is free.
- [`BackendLazyAGMStateSize`](../Signatures/Runtime/BackendLazyAGMStateSize.lean)
  bounds the encoded stores from explicit product/list encoding laws. For
  encountered-message, field, and group widths `m,f,g`, header `h`, cache cap
  `K`, and combined hash/sign transcript cap `Q`, good storage is at most
  `2*g + K*(m+f+2*h) + Q*(m+g+2*h) + 7*h`; bad storage is at most
  `f+2*g + K*(m+2*f+3*h) + Q*(m+g+2*h) + 8*h`. Repeated replies count toward
  `Q` even when the cache is unchanged. No message universe is enumerated.

Complete reply runtime bounds are now checked below. Next: implement and cost
final extraction, assemble both solvers with general callers, and derive their
concrete and family security endpoints. Coefficient processing must account for
the actual encoded attacker output, including any excess coefficients.
Transcript length alone does not bound the cost of scanning an arbitrary
coefficient list.

Validation: `lake build SignaturesTest.BackendLazyAGMReply` passed (3275 jobs),
log `/private/tmp/agm-native-lazy-reply-test.log`. The
[new regressions](../SignaturesTest/BackendLazyAGMReply.lean) cover both branches,
signing before hashing, repeated replies, infinite `Nat` messages, private
randomness, and reply-dependent requests. Standard-axiom guards cover the new
semantic, state, stored-code, and size theorems; guards reject finite-message
premises on the native APIs. All new modules/tests pass without warnings or
admissions. This targeted build does not complete the full AGM resource theorem.

### Complete native BLS AGM reply budgets, 2026-10-14

- [`BackendLazyAGMReplyCost`](../Signatures/Runtime/BackendLazyAGMReplyCost.lean)
  derives argument and result-expression costs from individual primitive
  certificates. Good arguments cost at most `Z+32*c(32*w)`; bad arguments cost
  at most `2*Z+40*c(32*w)`. Good result construction costs at most
  `S+192*c(64*w)`; bad result construction costs at most
  `3*S+A+256*c(64*w)`. Here `w` bounds the relevant local environment and
  primitive values. These expressions charge transcript consing, variable
  traversal, context retention, zero initialization, and group arithmetic.
- [`BackendLazyAGMReplySize`](../Signatures/Runtime/BackendLazyAGMReplySize.lean)
  derives the intermediate-frame bounds. The cache retains the entire original
  argument environment, bounded by `5*w` when the message, original store,
  unit, and header are each bounded by `w`. Set
  `W(w,K)=CacheCompiler.frameWidth(5*w,K)=4*((4*K+32)*(5*w))`.
  All surrounding input frames fit `W`; the complete output fits `16*W`.
  The sharper persistent-state bounds above remain available for composition;
  repeated calls need not iterate this coarse frame bound.
- [`BackendLazyAGMReplyAssembly`](../Signatures/Runtime/BackendLazyAGMReplyAssembly.lean)
  composes the actual argument, finite-cache, and result code. Its generic lemma
  includes all three sequences and all three native local invocations, with
  encoded-size control charges. The argument/result obligations are discharged
  by the following specialized theorems.
- [`BackendLazyAGMReplyBudget`](../Signatures/Runtime/BackendLazyAGMReplyBudget.lean)
  proves the complete bounds for both hash and sign modes. Write
  `R(w,K)=c(64*W(w,K))`. Then good replies cost at most
  `K*(E+257*R(w,K)) + D_F+Z+S+384*R(w,K)`; bad replies cost at most
  `K*(E+257*R(3*w,K)) + 2*D_F+2*Z+3*S+A+468*R(3*w,K)`.
  `D_F` bounds the actual scalar-sampler execution, while `Z,S,A` bound the
  individual zero, scaling, and addition primitive realizers. `E` bounds message
  comparisons at widths `5*w` and `15*w`, respectively. The base `w` bounds the
  original store, encountered messages, primitive values, unit/bool, and header;
  `K` bounds the stored cache length. No whole-reply efficiency assumption or
  finite-message premise is used. The pair sampler's two draws and routing are
  included in the bad-branch formula.

Validation: the expanded `lake build SignaturesTest.BackendLazyAGMReply` passed
(3279 jobs), log `/private/tmp/agm-native-lazy-reply-budget-test.log`. Existing
adaptive/repeated-message tests still pass after the syntax refactor to explicit
Boolean cases. Standard-axiom guards now include every new cost, size, assembly,
and complete reply-budget theorem. The complete reply APIs also pass the
finite-message-premise guards. New and changed modules have no warnings or
admissions. Complete native extraction, solver setup/termination, general-caller
dispatch/composition, and final AGM security endpoints remain open.

### Native extraction list accounting, 2026-10-14

- [`BackendIndexCost`](../Signatures/Runtime/BackendIndexCost.lean) bounds the
  actual compiled positional lookup, including arbitrary retained context.
  For coefficient-list cap `L`, local width `w`, equality/subtraction costs
  `E,S`, and monotone backend overhead `c`, its time is at most
  `L*(E+S+257*c(128*((2*L+1)*w))) + 64*c(128*((2*L+1)*w))`.
  The scan charges the entire list, including excess coefficients and the suffix
  after a hit. Natural-value encoding and primitive bounds cover each reachable
  counter. The stored description is at most `s_eq+s_sub+256*a+4`.
- [`BackendReverseCost`](../Signatures/Runtime/BackendReverseCost.lean) bounds
  the compiled cons-fold reversal with arbitrary retained context. For list cap
  `Q` and local width `w`, time is at most
  `Q*(17*c(128*((4*Q+8)*w))) + 16*c(128*((4*Q+8)*w))`;
  its stored description is at most `16*a`. The
  [remaining-input fold invariant](../Signatures/Runtime/BackendFoldGrowth.lean)
  bounds the growing accumulator and every intermediate frame. Retained data,
  list construction, and fold control are charged.
- [`BackendListLength`](../Signatures/Runtime/BackendListLength.lean) states
  the explicit representation contract needed to recover length from size:
  each list cell increases encoded size by at least one. An additive encoding
  with a positive header supplies this law. The
  [AGM output recovery lemmas](../Signatures/Runtime/BackendLazyAGMOutputSize.lean)
  then bound both coefficient-list lengths by the complete encoded attacker
  output size, including excess coefficients. Upper list-size bounds alone do
  not justify this step. This is a contract of the selected encoding, not a
  restriction to arithmetic-language attackers or a conventional-backend instance.

Validation: `lake build SignaturesTest.BackendExtractionLists` passed (3245
jobs), log `/private/tmp/agm-native-extraction-lists-test.log`. The
[regressions](../SignaturesTest/BackendExtractionLists.lean) cover compiled
lookup with retained context, zero/missing coefficients, reversal order, repeated
reply occurrences, and surplus coefficients. They also reject a zero-size list
encoding under the recovery contract and check standard axioms and absence of
finite-domain premises on the new accounting APIs. New modules and tests have
no warnings or admissions. These are extraction prerequisites: coefficient-row
assembly, effectful extraction, full solvers, and general-caller composition
still need their complete native budgets. Coefficient-row assembly is now
completed by the following checkpoint.

### Complete native chronological coefficient rows, 2026-10-14

- [`BackendAttachTableState`](../Signatures/Runtime/BackendAttachTableState.lean)
  bounds the positional counter, growing row list, and retained enclosing frame.
  Its remaining-input invariant reserves one counter increment and one output
  row per unprocessed key. Repeated keys remain separate occurrences.
  [`BackendAttachTableCost`](../Signatures/Runtime/BackendAttachTableCost.lean)
  derives each actual body's cost from the native full coefficient scan,
  natural increment, and row construction.
  [`BackendAttachTableFold`](../Signatures/Runtime/BackendAttachTableFold.lean)
  composes those bounds for the complete loop, including its empty/final case.
- [`BackendAttachTable`](../Signatures/Runtime/BackendAttachTable.lean) derives
  complete time and stored-code bounds for the existing `AGM.attachTable`,
  including reversal of accumulated rows and arbitrary retained trailing context.
  For row cap `N`, coefficient cap `L`, and local width `w`, define
  `W(w,N,L)=(8*N+4*L+32)*w` and `V(w,N,L)=(4*N+8)*4*W(w,N,L)`.
  With `R=c(128*V(w,N,L))`, time is at most
  `N*(L*(E+S+257*R)+A+338*R)+96*R`.
  Here `E,S,A` bound the individual natural equality, subtraction, and increment
  primitive realizers over reachable counters. Stored code is at most
  `s_eq+s_sub+s_add+1024*a+8`, independent of transcript and coefficient counts.
- [`BackendTokenRows`](../Signatures/Runtime/BackendTokenRows.lean) composes
  actual transcript reversal, zero initialization, and positional attachment for
  the existing `AGM.tokenRows`. Let `U=(4*N+8*L+32)*w` and
  `R=c(128*V(U,N,L))`. The complete native runtime is at most
  `N*(L*(E+S+257*R)+A+355*R)+Z+192*R`, where `Z` bounds the zero primitive.
  The stored description is at most `s_zero+s_eq+s_sub+s_add+2048*a+16`;
  encoded output is at most `(4*N+1)*w`. The width assumptions cover encountered
  tokens, scalar encodings, reachable naturals, unit/bool/header, and the retained
  context. The exact semantic theorem preserves chronological occurrences,
  zero defaults for missing coefficients, and ignored surplus coefficients;
  the runtime still charges scanning those surplus entries.

Validation: the expanded `lake build SignaturesTest.BackendExtractionLists`
passed (3250 jobs), log `/private/tmp/agm-native-coefficient-rows-test.log`.
Regressions now cover full attachment with a nonzero default, repeated messages,
chronological matching with nonempty trailing context, and empty transcripts
with surplus coefficients. Standard-axiom guards cover all new semantic, state,
cost, output-size, and description theorems; no finite-domain premises are
accepted. These complete the coefficient-row component. The subsequent checkpoint
below adds native effectful extraction semantics and private-read budgets;
whole-extractor costs, solver setup/termination, general-caller composition, and
AGM security endpoints remain open. Polynomial family endpoints still need their
complete assembled budgets and instantiated primitive/representation contracts.

All five new modules and the expanded test pass without new warnings or
admissions. Whitespace/proof-escape checks and documentation-link checks pass.

### Native effectful extraction and private-read budgets, 2026-10-14

- [`IndexedIteration`](../Signatures/Runtime/IndexedIteration.lean) proves that
  the implemented indexed loop preserves the effectful fold's order, including
  every cache read. [`LazyAGMEvaluate`](../Signatures/Runtime/LazyAGMEvaluate.lean)
  implements actual list-length computation, positional row selection, private
  reads, and scalar/pair accumulation. The
  [source proof](../Signatures/Runtime/LazyAGMEvaluateSource.lean) equates that
  left-accumulating loop with the recursive source sum for arbitrary effects.
  No iteration bound, index operation, or list length is a free host function.
- [`BackendLazyAGMEvaluate`](../Signatures/Runtime/BackendLazyAGMEvaluate.lean)
  compiles the row evaluators with actual private-cache code and proves exact
  joint answer/cache correspondence. These reads do not append transcript tokens.
  [`LazyAGMExtraction`](../Signatures/Runtime/LazyAGMExtraction.lean) and
  [`BackendLazyAGMExtraction`](../Signatures/Runtime/BackendLazyAGMExtraction.lean)
  implement both complete extractors: chronological coefficient matching, good
  hash-then-signature evaluation or bad signature-pair evaluation, final target
  access, and field extraction. The exact laws preserve zero denominators,
  repeated occurrences, and missing/surplus coefficient behavior.
- [`LazyAGMExtractionQueries`](../Signatures/Runtime/LazyAGMExtractionQueries.lean)
  identifies these extraction phases with the suffixes of the established lazy
  solvers. [`BackendLazyAGMExtractionGrowth`](../Signatures/Runtime/BackendLazyAGMExtractionGrowth.lean)
  bounds native cache growth by the row count for evaluation, by `H+S+1` for
  good extraction, and by `S+1` for bad extraction, from any initial cache.
  These are reachable-state bounds, not runtime certificates.
- [`BackendLengthCost`](../Signatures/Runtime/BackendLengthCost.lean) charges
  the actual compiled length fold, with arbitrary retained context. For list cap
  `N`, natural-add cost `A`, width `w`, and `R=c(128*((4*N+16)*w))`, its runtime
  is at most `N*(A+17*R)+32*R`; stored description is at most `s_add+32*a+4`.
  The width assumptions cover cells, context, unit/header, and reachable natural
  encodings through `N+1`.
- [`BackendLazyAGMReadCost`](../Signatures/Runtime/BackendLazyAGMReadCost.lean),
  [`BackendLazyAGMReadAssembly`](../Signatures/Runtime/BackendLazyAGMReadAssembly.lean),
  and [`BackendLazyAGMReadBudget`](../Signatures/Runtime/BackendLazyAGMReadBudget.lean)
  derive complete private-read costs from individual primitive/scalar-sampler
  contracts. With `W(w,K)=4*((4*K+32)*w)` and `R(w,K)=c(32*W(w,K))`, good reads
  cost at most `K*(E+257*R(w,K))+D_F+Z+192*R(w,K)`. Bad reads cost at most
  `K*(E+257*R(3*w,K))+2*D_F+2*Z+212*R(3*w,K)`. Here `K` bounds cache length,
  `E` message comparison, `D_F` scalar sampling, and `Z` scalar zero. Base width
  `w` bounds the initial complete cache, message keys, scalar encodings, and
  unit/bool/header. Bad comparison contracts cover message widths up to `3*w`.
  Frame construction, fallback values, scans, sampling, projections, copies,
  and all local/control invocations are charged. Output entry/length invariants
  are proved as part of each bound.
- [`BackendLazyAGMReadDescription`](../Signatures/Runtime/BackendLazyAGMReadDescription.lean)
  bounds stored descriptions by `s_D+s_eq+s_zero+300*a+40` for good reads and
  `2*s_D+s_eq+2*s_zero+320*a+48` for bad reads, including both stored scalar
  sampler occurrences in the pair branch.

Validation: `lake build SignaturesTest.BackendLazyAGMExtraction` passed (3296
jobs), log `/private/tmp/agm-native-lazy-extraction-test.log`. Tests use infinite
`Nat` messages and cover repeated keys, empty rows, zero-coefficient reads,
ordered misses, both accumulator coordinates, chronology, coefficient mismatch,
zero denominators, and unseen final targets in both branches. Axiom guards accept
only the standard Lean axioms and reject added finite-domain premises on all new
public semantic/resource theorems. New modules and tests have no warnings or
admissions.

The native extraction semantics are complete; the whole-extractor resource proof
is not. Next derive row-selection and accumulation costs with retained-frame
invariants, assemble the evaluator loop and both extractor budgets, then solver
setup/termination and general caller composition. No finished-solver budget is
assumed, and the broader plan remains open.

### Native evaluator resource composition and complete extractor code, 2026-10-14

- [`BackendLazyAGMSelect`](../Signatures/Runtime/BackendLazyAGMSelect.lean)
  bounds actual row selection, including the full row scan and retained frame:
  `N*(E+S+257*c(128*w))+96*c(128*w)`. Here `N` caps rows, `E/S` bound natural
  equality/subtraction, and `w` bounds all required frames and reachable encodings.
- [`BackendLazyAGMUpdate`](../Signatures/Runtime/BackendLazyAGMUpdate.lean)
  charges the counter increment and actual scalar/pair accumulation. Bounds are
  `A_nat+A_field+M_field+128*c(128*w)` and
  `A_nat+2*A_field+2*M_field+192*c(128*w)` respectively.
- [`BackendLazyAGMBody`](../Signatures/Runtime/BackendLazyAGMBody.lean)
  composes selection, private access, and updating with native compiler costs:
  `selectTime+readTime+updateTime+64*c(256*w)`. This component theorem still
  needs its branch-specific hypotheses instantiated for the complete evaluator.
- [`BackendIterationGrowth`](../Signatures/Runtime/BackendIterationGrowth.lean)
  and [`BackendLanguageIteration`](../Signatures/Runtime/BackendLanguageIteration.lean)
  prove complete counted-loop composition with an invariant indexed by remaining
  iterations. Count computation, initialization, retained context, loop tests,
  and final projection are charged. Loop-test cost remains an explicit individual
  control-instruction contract, consistent with the backend model.
- [`BackendLazyAGMEvaluateSize`](../Signatures/Runtime/BackendLazyAGMEvaluateSize.lean)
  bounds full evaluator/update frames and caches by `(4*N+8*K+64)*w`.
  [`BackendLazyAGMEvaluateState`](../Signatures/Runtime/BackendLazyAGMEvaluateState.lean)
  derives actual native counter increments, cache growth, and key validity from
  source correspondence. The remaining-indexed invariant reserves capacity for
  every pending insertion and counter increment.
- [`BackendLazyAGMEvaluateDescription`](../Signatures/Runtime/BackendLazyAGMEvaluateDescription.lean)
  and [`BackendLazyAGMExtractionDescription`](../Signatures/Runtime/BackendLazyAGMExtractionDescription.lean)
  prove stored-code bounds for the complete good/bad evaluators and extractors.
  They charge every stored sampler, fallback, loop body, coefficient operation,
  final target read, and final arithmetic instruction. These bounds depend on
  primitive code sizes and compiler allowance, not the message universe or
  transcript cardinality. They do not assert a runtime bound.

Validation: `lake build SignaturesTest.BackendLazyAGMExtraction` passed (3306
jobs), log `/private/tmp/agm-native-lazy-evaluation-resources-test.log`. The new
resumed-step regression checks selection at a nonzero index, increment, scalar
accumulation, and the resulting private cache. All new theorem axiom/no-finite-domain
guards pass. No new module/test warnings or admissions.

Next instantiate the component bounds to close both complete evaluator runtime
budgets, then compose coefficient preparation, evaluations, final target access,
and field arithmetic into extractor runtime budgets. Solver setup/termination,
general caller composition, and the remaining signature routes stay open.

### Complete native good/bad evaluator runtime bounds, 2026-10-14

The native evaluator runtime gap is now closed under the stated backend primitive,
encoding, and control-instruction contracts. The complete extractor and solver
runtime gaps remain open.

- [`BackendLazyAGMGoodBody`](../Signatures/Runtime/BackendLazyAGMGoodBody.lean)
  and [`BackendLazyAGMBadBody`](../Signatures/Runtime/BackendLazyAGMBadBody.lean)
  instantiate selection, actual private reads, counter increments, and scalar/pair
  updates. Each theorem preserves the remaining-indexed invariant and derives its
  time bound from individual primitive/scalar-sampler contracts. It does not take
  an iteration-efficiency premise.
- [`BackendLazyAGMEvaluateBudget`](../Signatures/Runtime/BackendLazyAGMEvaluateBudget.lean)
  assembles the actual count computation, initialization, counted loop, retained
  contexts, and final accumulator projection. This generic composition rule is
  instantiated in both complete branch theorems below.
- [`BackendLazyAGMGoodEvaluate`](../Signatures/Runtime/BackendLazyAGMGoodEvaluate.lean)
  and [`BackendLazyAGMBadEvaluate`](../Signatures/Runtime/BackendLazyAGMBadEvaluate.lean)
  prove complete native evaluator runtime and output/cache encoding bounds. They
  include computing the input list's length, scanning rows on every iteration,
  cache scans and possible insertion, scalar/pair sampling, field arithmetic,
  all copied/retained frames, and loop tests. No whole-evaluator budget is assumed.

For `N` input rows and initial cache capacity `K`, let `C=K+N`,
`E(w,N,C)=(4*N+8*C+64)*w`, and `W_cache(w,C)=4*((4*C+32)*w)`.
Base `w` bounds full row/default encodings, message keys in the initial cache,
all field encodings, reachable natural encodings through `N+1`, and unit/bool/header.
Primitive time bounds are `E_nat`, `S_nat`, `A_nat`, `E_message`, `D_F`, `Z`,
`A_field`, and `M_field`. `L` bounds a loop-control instruction for every
reachable counter and encoded frame of size at most `7*W`.

For the good evaluator, `W=E(w,N,C)` and `R=c(32*W_cache(W,C))`. Its derived
runtime is at most:

```text
N * (N*(E_nat+S_nat+257*R) + C*(E_message+257*R)
     + 2*A_nat+A_field+M_field+D_F+Z+516*R+L)
  + Z+L+128*R
```

For the bad evaluator, `W=E(3*w,N,C)` and `R=c(32*W_cache(3*W,C))`. Its bound is:

```text
N * (N*(E_nat+S_nat+257*R) + C*(E_message+257*R)
     + 2*A_nat+2*A_field+2*M_field+2*D_F+2*Z+600*R+L)
  + 2*Z+L+128*R
```

Both output and private-cache encodings have size at most their branch's `W`.
Message-comparison contracts cover argument widths up to `W` for good and `3*W`
for bad. Neither bound depends on the cardinality of the message universe.
These formulas are polynomial when their input sizes and primitive/control cost
functions have the required polynomial bounds; this checkpoint does not yet
provide the complete AGM solver's polynomial-family endpoint.

Validation: `lake build SignaturesTest.BackendLazyAGMExtraction` passed (3311
jobs), log `/private/tmp/agm-whole-lazy-evaluator-test.log`. Existing semantic
regressions cover empty and repeated rows, ordered misses, both coordinates,
zero coefficients, retained caches, and the complete extractors. All new complete
runtime and helper theorems pass standard-axiom/no-finite-domain guards, with no
new module/test warnings or admissions.

Next compose chronological coefficient preparation with these evaluator bounds,
charge default-row creation (including the group zero), final-target access and
field extraction, and retain all attacker output/transcript encodings in the
outer frame costs. Then assemble solver setup/termination, general caller
composition, and the hardness/family endpoints. Other signature routes remain open.

### Complete chronological evaluation calls and extraction locals, 2026-10-14

- [`BackendLazyAGMExtraction`](../Signatures/Runtime/BackendLazyAGMExtraction.lean)
  now also names the actual compiled `backendEvaluateTokens` routine. It executes
  chronological coefficient preparation followed by effectful evaluation; it is
  the same typed routine called by the existing extractors.
- [`BackendLazyAGMExtractionState`](../Signatures/Runtime/BackendLazyAGMExtractionState.lean)
  proves preservation of an arbitrary predicate on cache keys across private
  term evaluation and the complete native chronological call. Cache growth is
  bounded by the actual transcript length. These facts preserve the original
  per-message encoding bound while larger aggregate frames are retained.
- [`BackendLazyAGMTokensSize`](../Signatures/Runtime/BackendLazyAGMTokensSize.lean)
  bounds the complete preparation input, prepared rows, and cache. For token cap
  `N`, coefficient cap `L`, initial cache cap `K`, and base width `w`, define
  `W_tok=E(9*w,N,K+N)+(4*N+4*L+16)*w`, where
  `E(w,N,C)=(4*N+8*C+64)*w`. All coefficient entries contribute to the retained
  input size, including surplus coefficients. Prepared rows have the original
  transcript length; each row has size at most `3*w` and its message at most `w`.
- [`BackendLazyAGMTokensAssembly`](../Signatures/Runtime/BackendLazyAGMTokensAssembly.lean)
  composes preparation and evaluation with the actual call-argument and context
  costs. The generic rule adds at most `64*c(512*W_tok)` to the two component
  times. It is instantiated in
  [`BackendLazyAGMGoodTokens`](../Signatures/Runtime/BackendLazyAGMGoodTokens.lean)
  and [`BackendLazyAGMBadTokens`](../Signatures/Runtime/BackendLazyAGMBadTokens.lean).
  Their complete bounds are the proved chronological `rowsTime` at base width
  `3*w`, plus the respective complete evaluator bound at base width `3*w`, plus
  this routing/context overhead. `goodTokenTime` and `badTokenTime` give the exact
  closed formulas. The branch theorems assume only individual primitive,
  scalar-sampler, encoding, and loop-control contracts. They do not assume that
  the complete call is efficient. Both output/cache encodings are at most
  `W_tok`; the final cache has at most `K+N` entries and retains key widths at most
  `w`, ready for composition with the next phase.
- [`BackendLazyAGMExtractionCost`](../Signatures/Runtime/BackendLazyAGMExtractionCost.lean)
  charges actual default-row construction, including group zero, by
  `Z+Z_group+32*c(128*w)`. Final good arithmetic costs at most
  `A_field+S_field+D_field+64*c(128*w)`; bad arithmetic costs at most
  `2*S_field+Neg_field+D_field+64*c(128*w)`. Division-by-zero behavior is unchanged.
- [`BackendLazyAGMExtractionArgs`](../Signatures/Runtime/BackendLazyAGMExtractionArgs.lean)
  bounds each caller's hash/sign argument construction by `64*c(128*w)` and final
  target selection by `9*c(16*w)` for good or `7*c(16*w)` for bad. Here `w` bounds
  the full local input frame, including all retained output/transcript data.

Validation: `lake build SignaturesTest.BackendLazyAGMExtraction` passed (3324
jobs), log `/private/tmp/agm-complete-token-evaluation-test.log`. The new native
chronological-call regression checks ordering, surplus coefficients, and cache
reuse with an infinite message type. Existing complete-extractor regressions and
all new theorem standard-axiom/no-finite-domain guards pass. No new module/test
warnings or admissions. Local compiler opacity avoids repeatedly normalizing
compiled routines during proof composition; no heartbeat limit was increased.

Next compose the full good/bad extraction wrappers, preserving each cache-capacity
transition and charging the complete outer frames. Then assemble solver
setup/termination, general caller composition, and the hardness/family endpoints.
The complete extractor runtime certificates and the broader plan remain open.

### Complete native good/bad extractor runtime bounds, 2026-10-14

This checkpoint completes the extractor composition left open in the preceding
checkpoint. The broader solver/general-attacker plan remains open.

- [`BackendLazyAGMExtractionSize`](../Signatures/Runtime/BackendLazyAGMExtractionSize.lean)
  bounds default construction, retained caller frames, cache encodings, and the
  actual argument frames. With base width `w`, per-transcript query cap `N`,
  coefficient cap `L`, and initial cache cap `K`, both branches use
  `W=tokenFrameWidth(5*w,N,L,K+N)+128*w`. The base input bound includes the complete
  attacker output and both transcripts, including unused hash data in the bad
  branch and surplus coefficient entries. Cache invariants preserve key widths
  while allowing the aggregate cache to grow.
- [`BackendLazyAGMGoodExtractionAssembly`](../Signatures/Runtime/BackendLazyAGMGoodExtractionAssembly.lean)
  and [`BackendLazyAGMBadExtractionAssembly`](../Signatures/Runtime/BackendLazyAGMBadExtractionAssembly.lean)
  compose the actual native wrappers. Good extraction evaluates hash and signing
  occurrences before reading the target; bad extraction evaluates signing
  occurrences and then reads the target. Both charge default creation, argument
  routing, copying, retained frames, and final field arithmetic.
- [`BackendLazyAGMGoodExtractionBudget`](../Signatures/Runtime/BackendLazyAGMGoodExtractionBudget.lean)
  and [`BackendLazyAGMBadExtractionBudget`](../Signatures/Runtime/BackendLazyAGMBadExtractionBudget.lean)
  instantiate every component from individual primitive, sampler, encoding, and
  loop-control contracts. `backendExtractGood_bound` and `backendExtractBad_bound`
  do not assume a budget for a finished token call or extractor. Their named
  `goodExtractionTime` and `badExtractionTime` definitions give the closed bounds.
  Writing `Tg(K)` and `Tb(K)` for the proved token times at base width `5*w`,
  `Rg` and `Rb` for the proved final-read times at base width `W`, and
  `R=c(4096*W)`, these are:

  ```text
  good: Tg(K) + Tg(K+N) + Rg(K+2*N) + Z + Z_group + Add + Sub + Div + 512*R
  bad:  Tb(K) + Rb(K+N) + Z + Z_group + 2*Sub + Neg + Div + 512*R
  ```

  Final result size is at most `w`, final cache size at most `W`, and final cache
  entry counts at most `K+2*N+1` (good) or `K+N+1` (bad). These bounds mention no
  message-universe cardinality. Existing semantic theorems identify the actual
  extracted output and joint cache distribution; the new theorems bound the
  execution of that same compiled code.

Validation: `lake build SignaturesTest.BackendLazyAGMExtraction` passed (3329
jobs), log `/private/tmp/agm-complete-extractor-runtime-test.log`. Existing native
regressions cover chronology, repeated messages, surplus/missing coefficients,
unseen final messages, zero denominators, and unused bad-branch hash data. All
new size/composition/runtime theorems pass standard-axiom and no-finite-domain
guards. No new module/test warnings, admissions, or increased heartbeat limits.

Next assemble challenge initialization, the adaptive caller phase, extraction,
and termination into complete native solver certificates. Then derive the AGM
general-caller hardness and family endpoints. Conventional-machine instantiation
and the remaining signature routes are still separate open tasks.

### Native general-request AGM dispatch and caller semantics, 2026-10-14

- [`BackendCoronInterface`](../Signatures/Runtime/BackendCoronInterface.lean)
  now permits arbitrary caller input/output types in its request/reply data
  ports. Existing co-CDH callers remain unchanged; AGM outputs can carry their
  algebraic coefficients through the same interface.
- [`BackendSignatureHandler`](../Signatures/Runtime/BackendSignatureHandler.lean)
  implements reusable native randomness/hash/sign dispatch. It decodes requests,
  retains the queried message, calls the native reply, and restores the dependent
  request/reply tag. Its executed typed handler preserves the exact native step
  count. The caller source law covers arbitrary adaptive computations realized
  on the backend, without an arithmetic-source attacker restriction.
- [`BackendSignatureHandlerBudget`](../Signatures/Runtime/BackendSignatureHandlerBudget.lean)
  derives routing, copying, tagging, and dispatch costs. For a frame bound `W`,
  reply cost `T_reply`, data-port cost `T_port`, and dynamic sampling cost
  `T_random`, its bound is
  `T_reply+T_random+2*T_port+40*c(32*W)`. Its component reply-budget premise is
  discharged by the concrete AGM dispatcher theorems below.
  [`BackendSignatureHandlerDescription`](../Signatures/Runtime/BackendSignatureHandlerDescription.lean)
  counts both group branches and one dynamic sampler. No table of messages or
  sampling arities is stored in the dispatcher code.
- [`BackendLazyAGMHandler`](../Signatures/Runtime/BackendLazyAGMHandler.lean)
  installs the actual good/bad native reply routines. Its source refinements
  preserve the fixed challenge configuration, list cache, transcript, and output.
  `goodCaller_source` and `badCaller_source` prove exact adaptive correspondence
  for the complete native caller phase, under the attacker's own realization and
  termination certificate. These are semantic statements, not yet its complete
  resource-substitution theorem.
- [`BackendLazyAGMHandlerState`](../Signatures/Runtime/BackendLazyAGMHandlerState.lean)
  tracks cache and transcript capacities separately. Each reserves space for
  remaining requests, since a cache hit can still append a transcript entry.
  Message widths remain at most `w`; for capacity `K`, both stores have encoded
  size at most `W=(12*K+16)*w`, assuming header/field/group encodings at most `w`.
- [`BackendLazyAGMHandlerBudget`](../Signatures/Runtime/BackendLazyAGMHandlerBudget.lean)
  proves `goodCode_bound` and `badCode_bound` from individual primitive, scalar
  sampler, dynamic sampler, and port contracts. The actual native reply budgets
  are instantiated at base width `W`; both consume one unit of reserved capacity
  and preserve original message widths. No completed-handler efficiency premise
  remains. `goodHandlerTime` and `badHandlerTime` expose the closed formulas.
  [`BackendLazyAGMHandlerDescription`](../Signatures/Runtime/BackendLazyAGMHandlerDescription.lean)
  composes the actual stored-code bounds for both complete dispatchers.

Validation: `lake build SignaturesTest.BackendLazyAGMHandler` passed (3323 jobs),
log `/private/tmp/agm-native-handler-test.log`. Regressions use `Nat` messages and
AGM output types, checking tagged hash hits, signing before hashing with a shared
pair cache, separate transcript entries, and dynamic randomness preserving state.
All new semantic, runtime, size, and description theorems pass standard-axiom and
no-finite-domain guards, with no new warnings or admissions. The existing backend
assembly and statement-assumption targets also passed together (3767 jobs), log
`/private/tmp/agm-statement-interface-test.log`, checking compatibility of the
generalized ports and the clarified BLS arithmetic-attacker certificate alias.

The following checkpoint completes indexed caller resource substitution with
these dispatcher budgets and reserved-state invariants. Remaining work is
challenge setup, extraction/termination assembly, and the concrete
general-attacker hardness endpoint.
The simple public interface above is a completion requirement. Asymptotic
packaging remains subsequent work; the other signature routes remain open.

### Native AGM caller resources and returned representations, 2026-10-14

- [`BackendSignatureCallerBudget`](../Signatures/Runtime/BackendSignatureCallerBudget.lean)
  derives native caller cost by substituting the actual executed handler, with
  its exact step count, into indexed caller composition. For local work `T`,
  per-kind query bounds `q`, dispatcher cost `D`, routing width `W`, fuel `f`,
  and loop charge `L`, the bound is
  `T + sum_k(q[k]*D) + 3*c(32*W) + (f+1)*(42*c(32*W)+L)`.
  It preserves a remaining-request store invariant, including on cutoff paths.
- [`BackendLazyAGMCallerBudget`](../Signatures/Runtime/BackendLazyAGMCallerBudget.lean)
  instantiates this result for both native AGM branches, discharging dispatcher
  costs from primitive/sampling/port contracts and proving the final cache and
  transcript bounds. There is no assumed completed-handler/caller runtime bound.
- [`BackendSignatureCallerResources`](../Signatures/Runtime/BackendSignatureCallerResources.lean)
  derives request sizes, entire return sizes, and continuation closure from
  the attacker's `RunsWithin` execution bound. `RequestRecovery` describes
  request decoding's size expansion; its canonical instance follows from sum
  payload laws. The native port contracts still charge actual decoding code.
  [`BackendLazyAGMCallerResources`](../Signatures/Runtime/BackendLazyAGMCallerResources.lean)
  removes custom caller invariants and separate caller budgets from both branch
  endpoints. It uses the conservative local allowance `bound.work+2*bound.queries+2`
  and per-kind counts `bound.queries`; the preceding budget theorem also accepts
  independently proved tighter counts.
- [`BackendSignatureCallerOutput`](../Signatures/Runtime/BackendSignatureCallerOutput.lean)
  transfers invariants to supported native runs, including final readout at zero
  remaining fuel. With fuel covering measured queries, the attacker's source
  realization and resource bound prove exact simulation and rule out cutoff.
  [`BackendLazyAGMCallerOutput`](../Signatures/Runtime/BackendLazyAGMCallerOutput.lean)
  derives the full canonical AGM output size, message size, both coefficient-list
  lengths, and their combined bound from the measured head-size cap and the
  positive-cell list law. Surplus coefficients are covered; no coefficient-length
  premise or transcript-length shortcut is used.
- [`BackendLazyAGMHandlerDescription`](../Signatures/Runtime/BackendLazyAGMHandlerDescription.lean)
  now bounds complete caller descriptions. Each includes the attacker's actual
  init/head/update descriptions, one dispatcher, fuel, and structural overhead.
  The good and bad formulas respectively have `895*allowance+138` and
  `995*allowance+158` structural terms, plus the displayed primitive/port code
  sizes. They do not enumerate messages or randomness arities.

Validation: `lake build SignaturesTest.BackendLazyAGMHandler` passed (3353 jobs),
log `/private/tmp/agm-native-caller-test.log`. Native zero-fuel return and cutoff
regressions extend the existing cache/tag/randomness tests. All new semantic,
resource, output-size, and description theorems pass standard-axiom and
no-finite-domain guards. The concrete resource endpoints additionally reject
whole-component budget premises and arithmetic-source certificates.

This completes the caller phase. The following checkpoint assembles complete
solver programs and proves their semantics; their total resource certificates
remain separate. The short public general-attacker statement is still pending;
the legacy BLS certificate alias is only a readability change.

### Complete native AGM solver programs and source laws, 2026-10-14

- [`BackendLazyAGMSolver`](../Signatures/Runtime/BackendLazyAGMSolver.lean)
  constructs both native programs on the `(g1, X1, g2, X2)` challenge. The good
  setup uses public key `X2`; the bad setup samples `kappa` and computes
  `kappa*g2`. Both construct empty caches/transcripts, execute the native caller,
  adapt its full algebraic output, and invoke the native extractor with the
  caller's existing cache and both transcripts. Explicit option inspection
  sends a cutoff to scalar zero. Key/output conversions are actual local code.
- [`BackendLazyAGMSolverCorrectness`](../Signatures/Runtime/BackendLazyAGMSolverCorrectness.lean)
  proves `goodProgram_source` and `badProgram_source`: at every challenge, the
  assembled native program equals the corresponding named `goodReductionList`
  or `badReductionList`. The source adapter maps the caller's output tuple to
  the game's algebraic output. The proof preserves the joint output, private
  cache, and chronological transcripts before extraction. Resource variants
  derive the required termination from `RunsWithin` and the query-fuel bound.
  No arithmetic-source attacker or finite message-domain premise is introduced.

Validation: `lake build SignaturesTest.BackendLazyAGMSolver` passed (3356 jobs),
log `/private/tmp/agm-native-solver-test.log`, with standard-axiom and no-finite-domain
guards for all component and complete-program semantic laws. Full-program cutoff
regressions check both branches, including preservation of the bad branch's
initial scalar-sampling operation. No new warnings or admissions remain.

The following checkpoint completes the setup/terminal and resource-composition
work left open by this semantic checkpoint.

### Complete BLS AGM resources and public statement, 2026-10-14

- `BackendLazyAGMSolverSetup` derives both actual setup costs, including the bad
  branch's scalar sample and public-key multiplication. `BackendWidthBudget`
  supplies explicit encoded-width composition rules.
- `BackendLazyAGMSolverState` derives extraction input, token, cache, and full
  coefficient-length bounds from the caller's state and decoded output.
  `BackendLazyAGMSolverPorts` supports noncanonical encodings through actual
  key/output/option adapters with explicit cost and size contracts.
- `BackendLazyAGMSolverTerminal` discharges both extractor costs from primitive
  contracts, charges output decoding, all argument construction/copying, final
  projection, and cutoff. Neither complete terminal has an extractor-budget premise.
- `BackendLazyAGMSolverBudget` composes setup, actual caller execution, and
  terminal extraction with both sequencing costs. Local attacker work is added
  once; handlers and all reduction work have explicit separate allowances.
- `BackendLazyAGMSolverDescription` bounds both complete stored programs,
  including the attacker's init/head/update code, all samplers, every stored
  branch, handlers, adapters, and extraction. The conservative common formula is
  caller code + 9 scalar-sampler descriptions + dynamic sampler + fuel +
  80 instruction descriptions + 4 handler ports + 3 solver ports +
  10000 structural allowances + 1024. It has no message-universe factor.
- `BackendLazyAGMSolverWithin` constructs both named list solvers in the fixed
  backend's actual program class, with semantic equality at every challenge.
  `BackendLazyAGMDLog` requires every experiment challenge to fit the input cap.
  `BackendLazyAGMSecurity.security_of_resources` applies DLog hardness to these
  derived witnesses and preserves the original sum of two advantages plus `1/|F|`.
- `BLS.GeneralAGM.security` is the short public concrete theorem.
  `BLS.GeneralAGM.Family.security` selects parameters at `securityParameter`.
  Query allowances are separate random/hash/sign bounds. The attacker record
  contains general code, source correspondence, measured resources, and stored
  code/advice. The parameter record fixes the backend independently of the attacker.
  `Model.advantageBound` exposes the supremum over the specified solver class;
  numerical hardness upper-bounds it through `advantageBound_le`.

Validation: the solver and public-statement tests plus existing statement and
paper-statement assumption checks pass (3862 jobs), log
`/private/tmp/agm-native-public-tests.log`. The guards check standard axioms,
absence of finite message/public-key premises, and absence of hidden
whole-component budgets or arithmetic-attacker certificates, including inside
the public record constructors. Existing full-program cutoff regressions remain.
The full `lake build Signatures SignaturesTest` also passes (3951 jobs), log
`/private/tmp/agm-native-full-suite.log`. No new warnings or admissions remain.
The final public-interface guard passes separately (3442 jobs), log
`/private/tmp/agm-general-public-guard.log`: the concrete theorem has two explicit
arguments and the family theorem three.

This closes the concrete BLS AGM efficiency/composition task and its public
interface. It does not instantiate a conventional machine, prove an arbitrary
parameter family polynomial, or complete the remaining signature routes.

### BLS AGM polynomial families, 2026-10-14

[`BackendLazyAGMPolynomial`](../Signatures/Runtime/BackendLazyAGMPolynomial.lean)
proves polynomial closure of the complete `goodProgramTime`, `badProgramTime`
and `programDescription` formulas. The proof composes chronological coefficient
processing, both extractors, handlers, setup and general caller execution. It
uses fixed polynomial bounds on caller resources, encoded widths, primitive
prices and component descriptions, plus a single jointly polynomial structural
overhead bound. It assumes no completed solver's time or code bound.

[`BackendConfiguration`](../Signatures/Runtime/BackendConfiguration.lean)
bundles the backend, random interface, execution costs and description measure.
The family requires this exact configuration to be constant across security
parameters; group/message types and their encodings may vary.
[`BackendLazyAGMDLogFamily`](../Signatures/Runtime/BackendLazyAGMDLogFamily.lean)
defines nonuniform DLog hardness against all polynomial-time, polynomial-code
families in that backend. One executable per parameter must realize its solver
at every input, and every challenge must fit the polynomial input cap.

[`GeneralAGMFamilyResources`](../Signatures/BLS/GeneralAGMFamilyResources.lean)
derives both actual list-reduction family certificates from the pointwise
implementations. It bounds the attacker's complete stored code/advice and the
samplers/adapters/structural descriptions, and derives execution-query bounds
from the three query allowances. No finite message or public-key assumption is
introduced. The [family statement](../Signatures/BLS/GeneralAGMFamilyStatement.lean)
and [separate proof](../Signatures/BLS/Proofs/GeneralAGMFamily.lean) conclude
negligible forgery success from DLog hardness and negligible `1/|F|`, preserving
the original two-reduction-plus-inverse-order loss. This is a nonuniform
conditional-backend result; it asserts no uniform program generator or
conventional-machine instantiation.

Validation: `SignaturesTest.AGMFamilies` passes (3456 jobs), log
`/private/tmp/agm-family-tests2.log`; `lake build Signatures SignaturesTest`
passes (4025 jobs), log `/private/tmp/agm-family-full.log`. The new guards check
standard transitive axioms, fixed-backend/family/field-growth scope, no finite
message/public-key premise, and no supplied finished-solver budget, including
inside the polynomial-resource record. Zero-query regressions exercise both
complete runtime formulas. The new modules have no warnings, admissions,
additional axioms or proof-resource overrides.

- [x] Define the common execution, cost, encoding, and hardness interfaces,
  with an explicit polynomial code/advice convention for the fixed backend.
- [x] Prove general caller/handler composition and instantiate BLS co-CDH first
  (conditional fixed-backend concrete/nonuniform endpoints for arbitrary messages).
- [x] Implement both lazy BLS AGM solvers and prove correspondence, finite-support
  extraction, finite-list refinement, and the arbitrary-message probability bound.
- [x] Derive complete native BLS AGM private-cache and hash/sign reply budgets,
  with exact semantics, stored-code bounds, and encoded-store invariants.
- [x] Derive complete native chronological coefficient-row time, stored-code,
  and output-size bounds, including coefficient scans and both reversals.
- [x] Implement native effectful row evaluation and complete good/bad extraction
  with exact joint cache laws, source-solver factorization, and cache-growth bounds.
- [x] Derive actual length-computation and complete private-read runtime/code bounds.
- [x] Derive row-selection/update costs, generic body/loop resource composition,
  and full evaluator/extractor stored-code bounds.
- [x] Derive complete native good/bad evaluator runtime and encoded-output/cache
  bounds from individual primitive and control-instruction contracts.
- [x] Derive complete chronological preparation/evaluation call budgets and
  cache-state invariants; charge default creation, caller arguments, target
  selection, and final extraction arithmetic locally.
- [x] Derive complete native good/bad extractor runtime and encoded-result/cache
  bounds, composing every call and charging retained caller frames.
- [x] Implement native general-request AGM dispatch with exact adaptive caller
  source laws, derived dispatcher runtime/code bounds, and reserved-state invariants.
- [x] Derive both native AGM caller-phase runtime/code bounds from attacker
  execution resources; recover request/output sizes, coefficient lengths, and
  termination without custom caller invariants or arithmetic-source restrictions.
- [x] Assemble both complete native BLS AGM solver programs and prove exact
  correspondence to the named lazy reductions, with resource-derived termination.
- [x] Derive complete native BLS AGM solver runtime/code certificates and hardness endpoints.
- [x] Expose short concrete BLS AGM/DLog and unrestricted co-CDH statements,
  indexed by security parameter, with transparent resources and hardness scope;
  keep supporting proof bodies in a separate proof file.
- [x] Derive BLS AGM polynomial solver time/code bounds and the nonuniform
  negligible-success corollary in a backend fixed across the parameter family.
- [x] Implement shared weighted lazy OOPS/Proximity solvers with joint
  eager/lazy correspondence, finite-list refinement, finite-topic/slot probability
  bounds, and the encountered-base cache cap, preserving admissibility/collision scope.
- [x] Remove the proof-side finite topic/slot restrictions for weighted reductions,
  preserving generated-key scope, admissibility, and the exact collision term.
- [x] Implement OOPS/Proximity term generation with exact source semantics and
  derived native runtime, stored-code, and encoded-output bounds, including retained frames.
- [x] Derive the Proximity tuple input width from coordinate encodings and prove
  native runtime/code bounds for both structured cache-key comparisons.
- [x] Compile both weighted private-cache branches with derived runtime/code
  bounds, exact source-index encoding laws, and no sampler execution on hits.
- [x] Derive complete native weighted private-read runtime/code bounds, including
  executed fallback construction and cache/state routing.
- [x] Compile weighted scalar/pair evaluators with exact ordered source value/cache
  semantics and complete stored-code bounds.
- [x] Derive complete weighted evaluator runtime bounds by composing the actual
  loop body, cache growth, natural-index scans and scalar/pair reads.
- [x] Connect complete native weighted evaluation to injectively encoded source
  indices, including Proximity's original optional coordinate and exact cache state.
- [x] Implement native signing-coefficient expansion with exact source
  representation, stored-code and encoded-output bounds.
- [x] Derive the inner scaling fold's native runtime, including its retained
  input/accumulator lists and growing output.
- [x] Derive complete native signing-coefficient expansion runtime bounds,
  composing chronological matching, term generation, both folds and reversal.
- [x] Implement native dispatch with distinct hash-index/signing-message types,
  exact general-caller semantics, and derived routing/runtime/stored-code bounds.
- [x] Install actual weighted hash/sign replies with exact adaptive source/cache/
  transcript correspondence, complete stored-code bounds and local response/frame bounds.
- [x] Compose complete weighted hash/sign reply runtime bounds, deriving actual
  term/fallback generation, evaluator, response and retained-frame costs.
- [x] Preserve native weighted challenge/cache/log invariants and compose the actual
  reply budgets into complete dispatcher/general-caller runtime and stored-code bounds.
- [x] Implement both complete native weighted extractors with exact joint source/
  cache correspondence, derived stored-code bounds and final-target-only cache growth.
- [x] Derive complete weighted hash/sign transcript and final-target call runtime,
  including actual preparation, ordered evaluation and retained argument/cache frames.
- [x] Compose complete weighted extractor runtime across these calls, default
  construction, final arithmetic and the full retained output/transcript state.
- [x] Recover weighted caller reachability, request/return widths, and coefficient
  lengths from general attacker resources and encoding contracts.
- [x] Derive whole weighted native solver runtime/code bounds, charging
  degree/dimension, term construction, coefficient expansion, and general caller composition.
- [x] Connect weighted certificates to the original OOPS/Proximity concrete
  security bounds, including exact Proximity source-interface and query-count transport.
- [x] Expose short OOPS/Proximity public statements with separate proof files,
  original admissibility/collision conditions and explicit resource-indexed DLog bounds.
- [x] Derive weighted polynomial-family resources and asymptotic security,
  with explicit polynomial degree/dimension and Proximity's original collision loss.
- [x] Refine Schnorr AGM to finite-list execution, preserve its original probability
  bound, and derive query-dependent cache/basis/signing-history capacities.
- [x] Implement Schnorr AGM tuple/list layouts and native cache core, with exact
  source semantics and derived comparison/sampling/scan/runtime/code bounds.
- [x] Implement the complete native Schnorr AGM read, with exact whole-state
  semantics, preserved history bounds and derived adapter/control/runtime/code costs.
- [x] Implement native Schnorr AGM representation flattening, preserving all
  positional/zero-padding semantics and deriving complete time/code/output-size
  bounds including coefficient suffixes and retained contexts.
- [x] Compose the decoded singleton hash path with exact source semantics and
  derived preparation/control/runtime/code bounds; implement and bound the
  singleton-list decoder needed by the all-shape dispatcher.
- [x] Connect both singleton scans to the all-shape native hash dispatcher, with
  exact source scalar/reply-state correspondence, no sampling on rejection,
  full malformed-input size charges and derived all-path runtime/code bounds.
- [x] Implement chronological history append and first-entry-preserving signing
  cache programming, with derived native time/code bounds and an exact source
  signing-cache correspondence.
- [x] Compose the complete accepted signing core, including both draws, response
  arithmetic, history updates, cache programming and state packing, with exact
  source semantics and derived time/code/representation bounds.
- [x] Add signing request dispatch, including the group-emptiness scan, malformed
  rejection, ignored incoming rows and construction of scalar/group-list replies,
  with exact source semantics and derived all-path time/code bounds.
- [x] Add the random handler with one runtime-selected uniform query, preserved
  store capacities, malformed-state updates and fully charged native conversions,
  scanning, retention and reply construction.
- [x] Install indexed request/reply adapters and all three handlers in the native
  general caller, with exact adaptive finite-list source correspondence and
  complete stored-code bounds.
- [x] Derive shared request/store invariants and all five compiled common-store
  adapter costs. Compose primitive-derived random/hash/signing budgets with
  config retention, reply construction and control costs; preserve each
  component's cache/history capacity growth without any finite-domain premise.
- [x] Derive the complete indexed handler runtime from primitive and local port
  contracts, charging the original request, reply tags, decoder and routing.
  Prove capacity reservations and additive caller overhead using the attacker's
  own local-work/query budget; no finished-handler budget is assumed.
- [x] Recover request/return widths, coefficient lengths, random arities,
  reachability and termination from measured attacker resources and explicit
  encoding laws, then instantiate the native caller bound with those results.
- [x] Implement all-shape native Schnorr AGM final extraction with exact joint
  scalar/state correspondence, full stored-code bounds and primitive-derived
  entry-read, adapter and complete decoded-path runtime bounds.
- [x] Compose the final shape-dispatch runtime and derive complete all-path
  extraction costs, including both scans, retained response and malformed output.
- [x] Recover extraction input bounds from measured output/state resources and
  implement and charge actual source-output conversion with full row retention.
- [x] Assemble the complete native Schnorr AGM solver and prove exact source
  correspondence from measured caller resources, plus its full stored-code bound.
- [x] Derive initial-state reservations and setup, cutoff and final-projection
  runtime bounds, including actual input conversion and initial basis construction.
- [x] Compose successful-terminal and optional-return routing budgets, then combine
  setup, caller and terminal into the complete Schnorr AGM runtime/`Within` certificate.
- [x] Apply DLog hardness to the derived Schnorr AGM solver witness, preserving
  the original probability losses and checking every challenge's encoded input size.
- [x] Define lazy retained randomness for arbitrary replay computations; prove
  exact single-run seeded semantics, joint first-run recording, preservation of
  private suffixes on reset, and query-dependent tape-cell/ambient-call bounds.
- [x] Prove joint deferred sampling with the original seed and complete first
  transcript, and remove unused independent suffixes after a valid reset,
  including dependent families first queried in the second run.
- [x] Prove the complete joint lazy-fork probability bridge, including replacement
  sampling, collision/acceptance checks, finite-list tape correspondence and
  valid-slot derivation from intrinsic selector reachability.
- [x] Transport that fork equality through extraction and the key-averaged
  experiment to the named lazy Schnorr security endpoint, preserving the original
  source game, signing-simulation loss, fork denominator and arbitrary messages.
- [x] Derive the probability reference's private-family coverage without source
  syntax or additional caller premises; retain the actual `qH + 1` hash bound and
  remove the seed cover/private capacity from the main ROM probability endpoint.
- [x] Implement the raw finite-list controller and extractor with exact
  computation equality to the named lazy reduction and its security theorem.
- [x] Preserve tape validity through replay/reset and implement native dynamic
  private draws with full-state correspondence and arity-independent code bounds.
- [x] Derive raw saved/remaining capacities and live-query bounds, preserve native
  encoding invariants, and charge hit-return and chronological-save execution.
- [x] Derive native tape-scan costs and compose the complete dynamic private-draw
  budget, with polynomial closure of its actual runtime formula.
- [x] Implement native challenge draws with exact full-state semantics, stored-code
  and encoding bounds, complete runtime and polynomial closure from sampler resources.
- [x] Implement native reset with exact full-state semantics, stored-code and
  both-list encoding bounds, complete primitive-derived runtime and polynomial closure.
- [x] Implement direct selected-challenge lookup with exact source semantics,
  code/encoding bounds, complete primitive-derived runtime and polynomial closure.
- [x] Assemble the native fork around actual pass/selector/sampler code, prove
  exact source correspondence at reached restart states, and count its entire stored code.
- [x] Derive complete native controller adapter/routing runtime, including both
  pass budgets, retained output/configuration copies, lookup/reset and polynomial closure.
- [x] Connect a finite-cache pass for arbitrary CMA oracle computations to the
  original ROM pass; derive managed/live capacities from ordinary query allowances.
- [x] Prove exact computation equality for the finite-cache/tape fork plus
  extraction/fallback and transport the original concrete probability bound.
- [x] Compile native live/managed-cache and signing kernels with exact state-passing
  semantics and actual stored-code bounds, including both private signing draws.
- [x] Transform actual private sampler code to share the raw uniform tape, with
  exact computation correspondence and stored-code bounds; derive typed per-draw
  runtime/encoding bounds and polynomial closure from primitive contracts.
- [x] Couple original execution profiles to actual transformed costed runs and
  derive structural routing bounds from primitive costs and encoded widths.
- [x] Lift measured sampler execution resources through the stateful transformation,
  deriving total native runtime, final encoding/tape capacities and polynomial closure.
- [x] Derive actual structured-key lookup, stateful live-cache access and pure
  signing cache-update costs, with entry/capacity bounds and polynomial closure.
- [x] Derive native cache/signing runtime with challenge-family draws for hashing
  and private sampling for signing, recovering both sampler runtimes from original
  profiles, with cumulative tape capacities, fixed cache-width allowances and
  polynomial runtime closure.
- [x] Install common-store adapters and indexed dispatch preserving the ordering
  of kernel and attacker queries; prove exact arbitrary-caller source correspondence,
  termination from measured query resources and complete stored-code bounds.
- [x] Derive all eight common-store adapter costs and complete wrapped-component
  runtime/encoding invariants from original sampler resources and primitive laws,
  with polynomial closure and fixed cache-entry width allowances.
- [x] Derive complete indexed dispatcher runtime and polynomial closure from
  primitive/original sampler contracts, preserving cache/tape reservations for
  adaptive calls and charging actual request/dependent-reply conversions.
- [x] Derive whole-caller runtime, request/returned-output widths and polynomial
  runtime closure from measured arbitrary executions and local encoding contracts.
- [x] Assemble the complete native pass, prove source correspondence and singleton
  completion on every replay tape, and derive complete stored-code bounds, local
  adapter costs, result encodings and final-verification composition.
- [x] Derive complete pass runtime from measured caller/sampler resources and
  local boundary contracts, including setup, terminal handling and both outcomes;
  prove polynomial closure of the full installed runtime formula.
- [x] Implement native selection, prove source correspondence on every result
  list and singleton agreement, and charge its entire stored description.
- [x] Derive complete chronological live-index runtime, including reversal,
  scan, growing counters and retained copies, with polynomial closure.
- [x] Derive complete selector verification/guard/outer-fold runtime and its
  polynomial closure from primitive and encoding contracts.
- [x] Install the actual general pass and selector in the native controller,
  prove exact two-run source correspondence and singleton output shape from
  measured resources, and derive complete stored-code bounds.
- [x] Generalize controller tape/output width invariants and derive complete
  installed fork runtime from the measured first/replay pass resources.
- [x] Derive polynomial closure of the fully instantiated fork runtime from
  original resource families, with no finished component efficiency premise.
- [x] Implement native guarded extraction and fallback, assemble the complete
  solver, prove exact equality to the named lazy reduction and count all stored code.
- [x] Derive setup/extraction/fallback and complete solver runtime/output-size
  bounds from original resources, including retained data and both fallback paths.
- [x] Prove polynomial closure of the actual complete solver runtime from original
  resource families, without assuming finished component efficiency.
- [x] Derive whole-solver stored-code polynomial closure and construct the
  fixed-backend executable certificate from its source/runtime/code theorems.
- [x] Complete general Schnorr full-field ROM replay and security.
- [x] Give the nonzero-nonce route a named lazy replay reduction with the original
  probability bound and internally derived reference cover.
- [x] Implement its three-draw signing kernel, prove exact source/store laws and
  stored-code polynomial closure, and derive local repair runtime/output bounds.
- [x] Derive negligible inverse nonzero-field size from the existing field-growth assumption.
- [x] Derive the complete nonzero signing runtime and polynomial closure from all
  three original sampler budgets, primitive costs and retained storage widths.
- [x] Refine the nonzero finite-cache pass and whole replay/extraction computation
  to the named lazy solver; prove query-dependent managed/live cache capacities.
- [x] Install both original nonzero-route samplers in the private replay handler;
  derive complete installed/common-store signing time/code and polynomial bounds
  from separate original execution profiles, including all three tape transitions.
- [x] Complete nonzero native dispatcher, adaptive reservation and arbitrary
  caller resource proofs from both original sampler profiles and attacker measurements.
- [x] Assemble the actual nonzero native pass, prove exact source correspondence,
  derive full runtime/code/output bounds and polynomial runtime closure.
- [x] Install both nonzero native passes in the replaying solver; derive complete
  solver runtime/code bounds, polynomial closure and fixed-backend executable membership.
- [x] Apply fixed-backend DLog hardness to the derived nonzero solver certificate,
  preserving the original signing and quadratic forking losses.
- [x] Complete the separate nonzero-nonce short public and nonuniform family security endpoints.
- [x] Add the short Schnorr AGM public statement with inspectable game, hardness
  and derived resources; keep proofs separate and preserve the original query losses.
- [x] Derive the Schnorr AGM polynomial solver resources and nonuniform family
  corollary in one fixed backend, preserving both original query losses.
- [x] Complete the general Schnorr ROM concrete DLog-hardness endpoint using the
  derived fixed-backend witness and the original probability losses.
- [x] Complete the general Schnorr ROM nonuniform family security endpoint.
- [x] Present the full-field ROM endpoints through the simple public scheme/parameter,
  qualified-adversary, query-allowance, game, and bound interface described above;
  keep execution/encoding certificates internal and hardness scope explicit.
- [x] Update status documentation and retire superseded eager runtime endpoints
  after replacement proofs and affected callers pass their checks.
- [x] Prove the explicitly requested BLS cache cap `qH + qS + 1` for both list
  solvers, connecting the singleton weighted-cache invariant to the actual BLS programs.
- [x] Run the full integration suite and complete the requirement-by-requirement audit.

For each endpoint, require a proved semantic/probability connection, a derived
solver resource certificate, and a hardness assumption covering that solver's
full computation class and budget. Do not substitute query counting, a compiler
for restricted attackers, or a premise that the finished solver is efficient for
the general composition proof.

Validate affected Lean targets and transitive axiom footprints. Add meaningful
regressions for repeated messages, signing before hashing, an unseen final target,
adaptive choices, missing/extra coefficients, and both AGM branches. Replay
regressions must cover private randomness after the fork and divergent second-run
paths. Preserve existing probability losses and check primitive cost assumptions
against their encoding-size bounds. Run the full suite when integrating the
completed shared framework, without treating a successful build as a proof of
model adequacy or polynomial cost.

The complete Coron `BackendWithin` certificate and public security endpoint now
follow from general caller resources and representation contracts. The nonuniform
family convention, asymptotic success corollary, and arbitrary-message probability
transport are now proved. Both lazy AGM solvers now have checked probability
correspondence, list-cache refinements, full resource certificates, and the short
general-caller concrete statement. BLS, OOPS and Proximity AGM now also have
polynomial-family closure and nonuniform security corollaries; Proximity retains
its collision qualification. Schnorr AGM now also has its complete native resource
certificate, short concrete security theorem and derived polynomial-family
corollary. General Schnorr full-field ROM now also has its complete native
certificate, short concrete statement and derived nonuniform family theorem.
The nonzero-nonce route now also has a complete native certificate, derived
polynomial resources, concrete hardness transport, short public statement and
nonuniform family theorem. Eager API retirement and affected-caller checks are
complete. Continue with full integration checks and the final requirement audit.
Preserve the distinction between the proved conditional native endpoint and
an instantiated conventional-machine claim. The broader plan remains open.
