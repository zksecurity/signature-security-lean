# General adversary reduction plan

Updated 2026-10-15. Status: implementation in progress. The shared general-caller
framework now proves source erasure, resource substitution, indexed native
composition, and explicit code-description bounds. BLS co-CDH now has a complete
native challenge-to-output solver with exact source correspondence, a runtime
bound derived from primitive contracts, and a stored-code bound. `program_within`
constructs its executable in the common fixed-backend hardness class. The public
`security_of_resources` endpoint now derives its caller conditions from a general
`RunsWithin` bound and explicit representation recovery, then applies hardness.
Polynomial closure of the derived time and code budgets and the nonuniform
family security corollary are proved. Exact probability transport now permits
arbitrary BLS ROM message types, with no finite-public-key assumption. Reachable
storage grows with encountered messages and queries, not the message universe.

Both BLS AGM lazy solvers now have sparse extraction, joint distributional
correspondence to the established reductions, and a finite-list cache refinement.
The original probability bound now holds for arbitrary message types, for both
symbolic-cache and finite-list solvers. Their query/transcript/cache-entry bounds
are proved. Both private caches now have native implementations with exact
list-handler semantics and derived runtime/description bounds, including a
two-scalar implementation of pair sampling. Native hash/sign replies now have
exact adaptive correspondence, complete runtime and stored-code bounds, and
encoded-store invariants. Native chronological transcript/coefficient matching
now has complete runtime, stored-code, and output-size bounds. Coefficient-list
lengths are recovered from output size under an explicit positive-cell encoding
contract. Native effectful row evaluation and both complete extractors now have
exact joint output/cache correspondence and reachable-cache bounds. Their private
reads have complete runtime and stored-code bounds, and computing loop lengths
is charged. Whole-evaluator/extractor stored-code bounds are now proved. Row
selection/update costs and complete good/bad evaluator runtime bounds are now
derived from primitive and control-instruction contracts. Complete chronological
preparation-and-evaluation calls now have combined runtime/encoding bounds and
cache-state invariants. Both complete extractor runtime bounds now compose
default creation, chronological calls, final-target access, and field arithmetic,
including retained output/transcript data and changing cache capacities. Both
native general-request dispatchers now have derived runtime/code bounds and
remaining-request store invariants. General caller execution has exact adaptive
source correspondence for arbitrary output types. Both native caller phases now
have additive runtime and stored-code bounds derived from primitive contracts
and the attacker's own execution resources. Request/return sizes, reachability,
and termination follow from those resources; canonical AGM coefficient lengths
follow from the full returned encoding. Both complete native solver programs are
assembled and exactly realize the named finite-list reductions. Complete solver
runtime/code bounds and fixed-backend executable certificates are now proved.
The concrete hardness endpoint covers general realized attackers over arbitrary
message types. The public BLS statements now distinguish AGM/DLog from
unrestricted co-CDH. `BLS.agm_security` follows the requested English statement:
curve, security parameter, query allowances, and algebraic adversary, with the
named BLS game and twice one resource-indexed DLog bound plus `1/|F|` in the conclusion.
The shared time allowance is the maximum of the two proved solver times;
`agm_security_two_budgets` preserves the sharper two-budget statement.
The declared execution model is separate from the mathematical curve.
`BLS.cocdh_security` has the same four-input shape with an unrestricted attacker,
the actual lazy ROM game, and the Coron factor times the resource-indexed co-CDH
success bound. Only the AGM route uses `GeneralAGM.Parameters`.

The canonical `Signatures/BLS/Statement.lean` contains both short theorem
statements. Their proof bodies are in `BLS/Proofs/GeneralSecurity.lean`; the
inspectable models, game definitions and explicit hardness suprema are in
`BLS/GeneralSecurityModel.lean`. Detailed arithmetic-source statements remain in
`ArithmeticStatement.lean`. `Security.lean` and `SecurityModel.lean` preserve the
old AGM-only names as compatibility imports. Regression guards check both public
theorems' defining module and argument list, and reject algebraic requirements in
the unrestricted co-CDH contracts.

The BLS AGM family corollary now derives polynomial runtime and stored code for
both native reductions from component resources. It concludes negligible forgery
success under nonuniform DLog hardness in one fixed backend and negligible inverse
field size. Groups and message types may vary with the security parameter.

OOPS/Proximity now have complete native interaction-phase runtime and stored-code
bounds for both AGM branches. Their capacity invariants charge the growing
private cache and reply logs over arbitrary topic/slot types. Both native extractors
now have exact source/cache laws, complete stored-code bounds, and final-target-only
cache growth. Both complete native extractors now have derived runtime bounds,
including coefficient generation, evaluation, default construction, final arithmetic,
and retention of the full output and both transcripts. Caller conditions and
extractor input bounds now follow from the attacker's measured resources and
encoding contracts. The native interaction supplies the cached-transcript invariant.
Both complete native solvers now have exact source correspondence, runtime and
stored-code bounds, and executable certificates in the fixed backend. Setup,
output adaptation, cutoff handling, and extraction are all charged. Both schemes
now connect these certificates to the original concrete security bounds. Their
short public statements take the curve, security parameter, degree/dimension,
query allowances and algebraic adversary. OOPS retains its distinct-message
admissibility rule; Proximity retains its actual fresh-collision probability.
Both weighted routes now have derived polynomial time/code bounds and
nonuniform family corollaries in one fixed backend. Degree and dimension must
grow polynomially in the security parameter. OOPS concludes negligible forgery
under DLog hardness and negligible inverse field size. Proximity bounds forgery
by its original collision probability plus negligible error; a separate corollary
requires that collision probability to be negligible too.

Schnorr AGM now has a finite-list reduction with exact adaptive output/state
correspondence and the original probability bound. Its storage capacities are
`qS + qH + 1` cache entries, `qS + 2` affine basis entries, and `qS` signed
messages, with no finite message/group-domain assumption. Its native cache core,
complete read, representation flattening and all-shape hash dispatcher now
have exact encoded-state semantics and derived time/code bounds. Hash dispatch
charges both singleton scans and the malformed-request path. Chronological
history append and first-entry-preserving signing-cache programming now have
native implementations and derived time/code bounds. The accepted signing core
now composes both scalar draws, response arithmetic, both histories, cache
programming and state packing, with exact source semantics and derived complete
time/code bounds. Signing dispatch now scans incoming groups, constructs accepted
and rejected scalar/group-list replies, and derives all-path time/code bounds
including ignored coefficient-row encodings. The random handler now executes one
dynamic uniform query even for malformed requests, with exact source semantics,
preserved store capacities and derived conversion/scan/state/reply budgets.
The native dispatcher now installs all three handlers with request retention,
common-store adapters and dependent reply tagging. General quantitative callers
have exact adaptive source correspondence and complete stored-code bounds.
Shared request/store size bounds now cover every retained row and the public
configuration. All five compiled common-store adapters have derived local costs,
and each installed component has a complete primitive-derived runtime bound.
Hash dispatch preserves both actual histories for all request shapes, so its
shared state invariant grows only the cache capacity. Indexed routing/tagging,
including retention of the complete original request, now has a derived
primitive/port runtime bound. Capacity reservations support repeated adaptive
calls at one fixed maximum budget. Caller runtime now adds this proved handler
and routing overhead to the attacker's own local-work/query budget. Request and
return widths, every coefficient-row length, random arities, reachability and
termination now follow from measured attacker resources and explicit encoding
laws. The caller budget uses these derived conditions without a separate caller
invariant or supplied caller budget. The native final extractor now handles all
output shapes and exactly realizes the original solver's scalar/state projection.
Its stored-code and complete all-path runtime bounds are derived, including both
shape scans, retained response, rejection, one cache read and field extraction.
Its input bounds follow from the full encoded attacker return and the caller
state. Actual output conversion has derived runtime/stored-code bounds and
preserves all output rows and private state. The complete native solver now
assembles setup, caller execution, optional return/cutoff handling, extraction
and scalar projection. Its exact source correspondence follows from measured
attacker resources, and its complete stored-code bound is derived. Setup, cutoff
and final projection have derived runtime bounds. Complete terminal and solver
runtime certificates now combine those costs with measured caller work and query
overhead. A fixed-backend executable witness includes exact source semantics and
the entire stored program. The concrete security theorem applies DLog hardness
to this derived witness, retaining the original probability losses. The short
public statement now takes a single-group curve, security parameter, query
allowances and algebraic adversary. The displayed game equals the original game;
the DLog supremum uses the derived complete runtime and stored-code bounds.
Its proofs are separate from the statement. Polynomial closure of the actual
runtime/code formulas and a nonuniform family corollary are now proved. The
family theorem keeps one fixed backend and derives negligible forgery from
polynomial component resources, DLog hardness and negligible inverse field size.

General Schnorr ROM replay now has a lazy retained-tape component for arbitrary
oracle computations. The first run records exactly its chronological draws;
reset preserves both private families, including their post-challenge suffixes.
Single-run seeded semantics and query-dependent saved/remaining-cell bounds are
proved without enumerating possible sampling families. The complete finite-list
fork now has the same joint output distribution as the pregenerated reference,
including replacement sampling, unchanged-challenge rejection and second-run
selector agreement. The valid-slot premise follows from the existing intrinsic
selector-reachability property. Transport through the named Schnorr security
endpoint and native execution/encoding bounds remain unfinished.

Remaining: instantiate the fixed backend in a conventional machine if making that
stronger claim; complete Schnorr's general-caller ROM overhead/replay routes and
their public statements and family corollaries, then finish API/documentation retirement.

Establish security for general efficient attackers for the signature routes in
this repository. Keep the reduction wrappers in our abstract arithmetic machine,
prove their concrete overhead, and compose them with attackers whose internal
algorithms need not use that language. AGM routes retain the algebraic-output
requirement; ordinary ROM routes do not acquire it.

This is the current plan for the efficiency and attacker-coverage work. Earlier
Schnorr parity completion records concern their stated source-game and certified
machine results, not completion of this broader objective.

## Existing results and limits

| Route | Existing result | Work needed for this plan |
| --- | --- | --- |
| BLS co-CDH ROM | Public general-caller concrete and nonuniform asymptotic security endpoints over arbitrary message types, with derived native runtime/code certificates and canonical encoding recovery. | A conventional-machine instantiation if claiming conventional PPT coverage; the conditional backend route is complete. |
| BLS AGM | Complete lazy native runtime/code certificates, resource-indexed DLog security, short public concrete statements, and a nonuniform asymptotic corollary with derived polynomial solver bounds. General realized callers, arbitrary messages, and the original probability loss are preserved. | Conventional-machine instantiation only if claiming that stronger model; the conditional backend route is complete. |
| OOPS AGM | Complete native certificates, concrete security, short public statements and nonuniform family security with derived polynomial resources. General realized callers, arbitrary topics and the original admissibility rule are preserved. | Conventional-machine instantiation only if claiming that stronger model; the conditional backend route is complete. |
| Proximity AGM | Complete native certificates, concrete security, short public statements and derived polynomial family resources. The original optional-coordinate/function-vector game has forgery bounded by collision probability plus negligible error; negligible forgery additionally assumes negligible collisions. | Conventional-machine instantiation only if claiming that stronger model; the conditional backend route, including its collision qualification, is complete. |
| Schnorr ROM | Forking probability proof, costed replay, complete fixed-private-tape controller, and arithmetic/bit endpoints for certified source attackers. General finite-list lazy fork has exact joint correspondence with the pregenerated fork, including all controller checks; selector reachability supplies the valid-slot premise. | Transport to the named security endpoint; general caller composition and native replay costs; efficient randomness encoding and size bounds. |
| Schnorr AGM | Complete native runtime/code certificates, short concrete security statement and derived polynomial-family corollary from general-caller resources, with exact source correspondence, arbitrary messages and the original probability losses. Actual setup, conversions, optional-return/cutoff handling and extraction are charged. | Conventional-machine instantiation only if claiming that stronger model; the conditional backend route is complete. |
| Schnorr nonzero-nonce ROM | Separate probability reduction and nonce-simulation proof. | Instantiate the general replay/cost framework for this variant; full-field runtime certificates do not automatically cover it. |

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

The existing BLS source-machine endpoint now names its specialized certificate
`ArithmeticAttackerCertificate` and explains the separate DLog success bounds.
This removes generic identity-conversion clutter without changing its restricted
attacker class or eager implementation. The public replacement is now
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
Apply this simple interface consistently across the remaining routes.

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
probability obligation; the lazy native resource/composition obligations remain.

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

### Schnorr general ROM replay remaining work

Reuse the existing [fixed-private-tape probability theorem](../Signatures/Schnorr/Proofs/FixedTapeROM.lean)
and [costed controller](../Signatures/Runtime/SchnorrSeededMachineCorrectness.lean).
The existing fixed-tape proof is not invalidated by widening the caller interface.

- Derive private-randomness coverage from the general attacker resource contract,
  replacing the current dependence on inspecting arithmetic source syntax.
- Apply the proved complete lazy-fork law to the named Schnorr reduction and
  transport it through extraction and the key-averaged security experiment.
  The generic law already preserves private suffixes and covers families first
  seen on replay.
- Charge both runs, seed/tape creation, access, reset, cache operations, checking,
  extraction, and fallback. Restarting from the initial state is sufficient;
  do not assume free snapshots of an arbitrary attacker state.
- Use efficient encodings and samplers. The current codec's linear dependence on
  a finite sampling range is not a polynomial-in-bit-length result. If bounded
  sampling introduces error, prove and include its probability contribution.
- Prove the new runner realizes the fixed-tape reduction required by the security
  argument, rather than assuming all replay implementations have the same law.
- Separately adapt the ROM accounting to the
  [nonzero-nonce variant](../Signatures/Schnorr/Proofs/NonzeroSecurity.lean).
  Schnorr AGM's single-pass overhead and family theorem are already complete.

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
- [ ] Transport that fork equality to the named Schnorr security endpoint and
  derive native encoding, replay and general-caller execution costs.
- [ ] Complete general Schnorr ROM replay; cover the
  nonzero-nonce variant separately.
- [x] Add the short Schnorr AGM public statement with inspectable game, hardness
  and derived resources; keep proofs separate and preserve the original query losses.
- [x] Derive the Schnorr AGM polynomial solver resources and nonuniform family
  corollary in one fixed backend, preserving both original query losses.
- [ ] Complete the general Schnorr ROM concrete and family endpoints.
- [ ] Present the new ROM endpoints through the simple public scheme/parameter,
  qualified-adversary, query-allowance, game, and bound interface described above;
  keep execution/encoding certificates internal and hardness scope explicit.
- [ ] Update status documentation and retire superseded eager runtime endpoints
  once replacement proofs and callers pass their checks.

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
corollary. Continue with general Schnorr ROM replay and separate
nonzero-nonce work, then API/documentation retirement.
Preserve the distinction between the proved conditional native endpoint and
an instantiated conventional-machine claim. The broader plan remains open.
