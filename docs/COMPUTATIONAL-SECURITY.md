# Computational-security status

**Status: the general-attacker concrete and nonuniform family endpoints are
proved for BLS/co-CDH, BLS/OOPS/Proximity AGM, Schnorr AGM and both Schnorr ROM
nonce conventions, conditional on explicit fixed-backend contracts. Complete
reduction runtime and stored-code bounds are derived. Proximity retains its
collision term. Eager API retirement and targeted checks are complete; full
integration verification and the final audit remain in progress;
no conventional-machine PPT or hardware-timing theorem is claimed.**

BLS co-CDH additionally exposes
[`Coron.NativeSolver.security_of_resources`](../Proofs/Runtime/BackendCoronSecurity.lean),
imported by `Signatures`. It quantifies over general backend-realized attacker
code, uses its actual `RunsWithin` resource bound, and constructs the completed
native solver certificate before applying hardness. Request/result decoding has
an explicit size-recovery contract; canonical message encodings satisfy it from
the product/sum size laws. The attacker need not use the arithmetic language.
The co-CDH hardness class uses the same fixed backend, separate input/code/time
caps, and a bound covering every challenge in the experiment. The conclusion
retains the exact Coron factor and now allows arbitrary message types.
[`BackendCoronPolynomial`](../Proofs/Runtime/BackendCoronPolynomial.lean)
proves polynomial growth of the derived runtime and description budgets under
fixed polynomial resource contracts and jointly polynomial structural overhead.
[`BackendCoronFamilySecurity`](../Proofs/Runtime/BackendCoronFamilySecurity.lean)
now proves negligible BLS forgery success under co-CDH hardness against
polynomial-time, polynomial-description nonuniform families in the same fixed
backend. Scalar/group/message types may vary with the security parameter; each
parameter chooses one program for all inputs. All fixed code/advice is charged.
The solver's efficiency is derived from the general caller and primitive
contracts. Every generated challenge fits the fixed input cap, and the exact
Coron loss is bounded by `3*(qS+1)`, including zero signing queries.
This remains conditional on the backend and its encoding/cost contracts; no
uniform program generator or conventional-machine instantiation is claimed.
[`ArbitraryMessages`](../Proofs/BLS/CoCDH/ArbitraryMessages.lean)
removes the finite-message assumption by exact transport of the original lazy
game and solver. A finite cover of all adaptive requests and final outputs is
used only inside the proof; no executable code enumerates it. The cover ranges
over generated public keys, so the public-key type need not be finite either.
The arithmetic-source endpoint also uses this stronger probability result.
The general-attacker results and remaining integration verification and final audit are tracked in the
[current plan](GENERAL-ADVERSARY-REDUCTION-PLAN.md).

The new [lazy BLS AGM solvers](../Signatures/BLS/Spec/LazyAGMReduction.lean)
now preserve the established two-reduction probability bound on arbitrary message
types, with joint randomness correspondence and sparse transcript extraction.
Their [association-list cache refinement](../Proofs/BLS/LazyAGMList.lean)
works over arbitrary message types and bounds stored entries by `2*q+1` for
`q` attacker requests. The [probability transport](../Proofs/BLS/LazyAGMArbitraryMessages.lean)
uses a finite cover only inside the proof; the public-key type need not be finite.
Their [native private-cache implementations](../Proofs/Runtime/BackendLazyAGMCache.lean)
now have exact list-handler semantics and derived runtime/code bounds. Independent
pair sampling is implemented with two charged scalar samplers; hits execute no
sampler. The [native hash/sign replies](../Proofs/Runtime/BackendLazyAGMReply.lean)
now have exact adaptive correspondence, stored-code bounds, encoded-store
invariants, and [complete runtime bounds](../Proofs/Runtime/BackendLazyAGMReplyBudget.lean)
derived from primitive costs. These include argument/store copying, transcript
updates, arithmetic, and control. Native
[chronological coefficient matching](../Proofs/Runtime/BackendTokenRows.lean)
now has complete runtime/code and output-size bounds. These compose the actual
coefficient scans, both reversals, zero initialization, and retained-context costs.
[Coefficient lengths](../Proofs/Runtime/BackendLazyAGMOutputSize.lean) are
bounded by encoded output size under an explicit positive-cell encoding law.
The [native effectful evaluators](../Proofs/Runtime/BackendLazyAGMEvaluate.lean)
and [complete extractors](../Proofs/Runtime/BackendLazyAGMExtraction.lean)
now preserve the joint output/cache law, including final-target processing and
zero denominators. Their [reachable-cache bounds](../Proofs/Runtime/BackendLazyAGMExtractionGrowth.lean)
depend only on processed rows and the final target. Private extraction reads have
[complete runtime bounds](../Proofs/Runtime/BackendLazyAGMReadBudget.lean)
and [stored-code bounds](../Proofs/Runtime/BackendLazyAGMReadDescription.lean);
the [executed length fold](../Proofs/Runtime/BackendLengthCost.lean) is charged.
Whole-evaluator/extractor [stored-code bounds](../Proofs/Runtime/BackendLazyAGMExtractionDescription.lean)
are now proved. Complete [good evaluator](../Proofs/Runtime/BackendLazyAGMGoodEvaluate.lean)
and [bad evaluator](../Proofs/Runtime/BackendLazyAGMBadEvaluate.lean) runtime
bounds are derived from primitive, encoding, and loop-control contracts. They
charge length computation, row/cache scans, sampling, arithmetic, copying, and
retained contexts, with no message-universe enumeration. Complete chronological
[good](../Proofs/Runtime/BackendLazyAGMGoodTokens.lean) and
[bad](../Proofs/Runtime/BackendLazyAGMBadTokens.lean) preparation/evaluation
calls now compose these bounds, including coefficient processing and cache-state
invariants. Complete [good extractor](../Proofs/Runtime/BackendLazyAGMGoodExtractionBudget.lean)
and [bad extractor](../Proofs/Runtime/BackendLazyAGMBadExtractionBudget.lean)
runtime bounds now compose default creation, every chronological call, final
target access, and arithmetic, including retained output/transcript frames and
changing cache capacities. They follow from individual primitive and encoding
contracts, with no finished-extractor budget premise. The native general-request
[dispatchers](../Proofs/Runtime/BackendLazyAGMHandler.lean) now preserve
adaptive caller source semantics and have derived
[runtime](../Proofs/Runtime/BackendLazyAGMHandlerBudget.lean) and
[stored-code](../Proofs/Runtime/BackendLazyAGMHandlerDescription.lean) bounds.
Their invariants reserve cache and transcript space for remaining requests.
Both native [caller resource bounds](../Proofs/Runtime/BackendLazyAGMCallerResources.lean)
now derive additive runtime and final-store bounds from the attacker's own
execution resources and primitive contracts. Complete caller descriptions are
also bounded. Request sizes, reachability, return sizes, and termination are
derived, with no custom caller invariant or assumed whole-caller budget.
The [returned AGM representation](../Proofs/Runtime/BackendLazyAGMCallerOutput.lean)
also yields coefficient-length bounds under the canonical output encoding and
positive-cell list law. Both complete [native solver programs](../Proofs/Runtime/BackendLazyAGMSolver.lean)
are assembled, and their [source laws](../Proofs/Runtime/BackendLazyAGMSolverCorrectness.lean)
identify them with the named lazy list reductions at every challenge. Complete
[runtime](../Proofs/Runtime/BackendLazyAGMSolverBudget.lean) and
[stored-code](../Proofs/Runtime/BackendLazyAGMSolverDescription.lean) bounds
now compose setup, the caller, output adaptation, and extraction. Both actual
executables have [fixed-backend resource certificates](../Proofs/Runtime/BackendLazyAGMSolverWithin.lean),
which supply the DLog premises in the
[concrete security theorem](../Proofs/Runtime/BackendLazyAGMSecurity.lean).
The [public statement](../Signatures/BLS/Statement.lean) takes the curve,
security parameter, query allowances, and algebraic adversary. Its main bound is
twice the maximum DLog advantage at the larger derived reduction time plus `1/|F|`.
`BLS.Proofs.agm_security` keeps the sharper sum at the two separate times.
The common time bound changes neither the backend nor its input/code limits. The
execution/resource model, actual forgery experiment and explicit DLog-success
supremum are in [GeneralSecurityModel.lean](../Signatures/BLS/GeneralSecurityModel.lean).
The [separate proof file](../Proofs/BLS/GeneralSecurity.lean) displays
the probability bound, constructed resource witnesses and supremum inclusions.
`Statement.lean` distinguishes `agm_security` from `cocdh_security`; the latter
uses an unrestricted message/signature output and the co-CDH success supremum.
The [detailed records](../Signatures/BLS/GeneralAGMParameters.lean) expose per-kind
query limits, local resources, code/advice, encodings, and primitive contracts.
They do not assume completed-solver efficiency. Arbitrary message types and
noncanonical output encodings are supported via the charged output adapter and
its size contract. [Polynomial closure](../Proofs/Runtime/BackendLazyAGMPolynomial.lean)
now covers both complete AGM solver runtime formulas and their stored-code bound.
The [family resource theorem](../Signatures/BLS/GeneralAGMFamilyResources.lean)
constructs both nonuniform solver certificates from these component bounds and
the pointwise certificates. It fixes the backend, random-query costs and
description measure across all security parameters. The
[asymptotic statement](../Signatures/BLS/GeneralAGMFamilyStatement.lean), with its
[separate proof](../Proofs/BLS/GeneralAGMFamily.lean), concludes
negligible forgery probability from DLog hardness in that family class and
negligible `1/|F|`. Groups and messages may vary with the parameter; messages
need not be finite. No uniform program generator or conventional-machine
instantiation is claimed. The weighted and Schnorr AGM endpoints are described below.
The existing AGM machine certificates
below still concern the eager implementations.

OOPS and Proximity now have shared
[weighted lazy solver programs](../Proofs/LinearFunctional/Spec/LazyAGMReduction.lean),
[joint eager/lazy distribution correspondence](../Proofs/LinearFunctional/LazyAGMCoupling.lean),
and probability bounds using those solvers for arbitrary topic/slot types. Their
complete program caches have at most `qH + (qS + 1) * L` entries, where `L = d + 1`
or `ell + 1`; transcript extraction is proved to make no fresh draws. The
cache/program definitions and entry-count theorems permit infinite domains.
The [OOPS arbitrary-topic theorem](../Proofs/OOPS/LazyAGMArbitraryTopics.lean)
and [Proximity arbitrary-slot theorem](../Proofs/Proximity/LazyAGMArbitrarySlots.lean)
use finite covers only inside the proofs. Exact transport preserves all adaptive
requests, the source games, and the actual Proximity collision term, without
requiring a finite public-key type. The
[weighted term generators](../Proofs/Runtime/BackendWeightedTerms.lean) now
have actual native implementations and derived runtime, stored-code, and
encoded-output bounds. Their unrolling and retained frames are charged in the
numerical degree/dimension and input widths. The
[weighted request dispatcher](../Proofs/Runtime/BackendWeightedHandler.lean)
now has exact general-caller semantics and derived routing/runtime/stored-code
bounds with independent hash-index and signing-message types. Both actual
[weighted reply branches](../Proofs/Runtime/BackendWeightedReply.lean) are now
installed with exact adaptive source correspondence and complete stored-code
bounds. Complete [hash](../Proofs/Runtime/BackendWeightedHashBudget.lean) and
[signing](../Proofs/Runtime/BackendWeightedSignBudget.lean) runtime bounds now
derive every reply cost from primitive, sampling, encoding and loop-control
contracts, including term/fallback construction and retention of the original
request, cache and logs. Preserved [cache/log capacities](../Proofs/Runtime/BackendWeightedHandlerState.lean)
now support complete [native interaction bounds](../Proofs/Runtime/BackendWeightedOracleCallerBudget.lean)
and [stored-code bounds](../Proofs/Runtime/BackendWeightedOracleDescription.lean)
for both branches. These compose the attacker's own local-work/query budget with
derived reply/dispatch costs and charge caller control and retained state.
Both [native extractors](../Proofs/Runtime/BackendWeightedExtraction.lean) now
preserve the source's joint output/cache law. Their
[stored-code bounds](../Proofs/Runtime/BackendWeightedExtractionDescription.lean)
charge the full implemented syntax, and [cache growth](../Proofs/Runtime/BackendWeightedExtractionState.lean)
is confined to the final target when transcript bases are cached. Complete
[hash](../Proofs/Runtime/BackendWeightedHashExtraction.lean),
[signing-transcript](../Proofs/Runtime/BackendWeightedSigningExtraction.lean), and
[final-target](../Proofs/Runtime/BackendWeightedTargetExtraction.lean) call bounds
now charge actual preparation, evaluation and retained argument/cache frames from
primitive contracts. Complete
[good](../Proofs/Runtime/BackendWeightedGoodExtractionBudget.lean) and
[bad](../Proofs/Runtime/BackendWeightedBadExtractionBudget.lean) extractor bounds
now compose those calls, default construction, final arithmetic and the retained
full output/transcripts. Intermediate cache equality recovers each later call's
cache bounds from a cached-transcript invariant; no finished runtime is supplied.
[Caller resource recovery](../Proofs/Runtime/BackendWeightedOracleCallerResources.lean)
now derives reachability, request widths and local/query budgets from measured
attacker execution. [Returned-output recovery](../Proofs/Runtime/BackendWeightedExtractionOutput.lean)
and [entry bounds](../Proofs/Runtime/BackendWeightedExtractionEntry.lean) charge
all coefficients and retained logs under explicit encoding laws. The
[native interaction](../Proofs/Runtime/BackendWeightedOracleCache.lean) supplies
the cached-transcript condition from an empty store once fuel covers the attacker's
query bound. Both [complete native solvers](../Proofs/Runtime/BackendWeightedSolver.lean)
now have [exact source semantics](../Proofs/Runtime/BackendWeightedSolverCorrectness.lean),
[runtime bounds](../Proofs/Runtime/BackendWeightedSolverBudget.lean),
[stored-code bounds](../Proofs/Runtime/BackendWeightedSolverDescription.lean),
and [executable certificates](../Proofs/Runtime/BackendWeightedSolverWithin.lean)
in the fixed backend. These charge setup, samplers, output adaptation, cutoff,
retained frames, and extraction alongside the general caller. Their internal
cache/transcript conditions follow from execution. The shared
[resource contracts](../Proofs/Runtime/GeneralWeightedParameters.lean) and
[derived certificates](../Proofs/Runtime/GeneralWeightedCertificates.lean)
now connect them to concrete OOPS and Proximity security. The public
[OOPS](../Signatures/OOPS/Statement.lean) and
[Proximity](../Signatures/Proximity/Statement.lean) statements take the curve,
security parameter, degree/dimension, query allowances and algebraic adversary.
Their separate proofs preserve the exact source games, including OOPS's
distinct-message rule and Proximity's actual fresh-collision probability.
[Proximity transport](../Proofs/Proximity/GeneralAGMEncoding.lean)
preserves the original optional-coordinate/function-vector interface and each
query allowance. No finite topic/slot domain or completed solver budget is assumed.
[Polynomial closure](../Proofs/Runtime/BackendWeightedPolynomial.lean) now
derives both whole runtime bounds and stored-code bounds, including polynomial
degree/dimension. [Family resources](../Proofs/Runtime/GeneralWeightedFamilyResources.lean)
then construct both polynomial reduction families in one fixed backend. The
[OOPS corollary](../Signatures/OOPS/GeneralAGMFamilyStatement.lean) gives negligible
forgery under nonuniform DLog hardness and negligible inverse field size. The
[Proximity corollaries](../Signatures/Proximity/GeneralAGMFamilyStatement.lean)
give collision probability plus negligible error, and negligible forgery only
with an explicit negligible-collision hypothesis. Types may vary with the
security parameter; no uniform program generator or conventional-machine
instantiation is claimed.
Proximity's tuple width is derived
from coordinate encodings, and the structured topic/degree and slot/coordinate
comparisons have native runtime/code bounds too.

Synchronized Pointcheval–Sanders has the same general route. The attacker's caller, realized in
the fixed backend at the single-signer interface, is
[wrapped](../Proofs/Runtime/GeneralSyncWrapMachine.lean) for the two weighted schemes `x•H(t)` and
`y•(m•H(t))` with the other key known; the wrapper's
[execution](../Proofs/Runtime/GeneralSyncWrapRuns.lean) and
[stored-code](../Proofs/Runtime/GeneralSyncWrapDescription.lean) bounds are derived from the
attacker's, so at every known key both weighted solvers are pipeline certificates
([parameters](../Proofs/Runtime/GeneralSyncWrapParameters.lean),
[adversary](../Proofs/Runtime/GeneralSyncWrapAdversary.lean)). The four synchronized solvers sample
the key, so their advantages are averages of in-budget solvers:
[concrete security](../Proofs/SynchronizedPS/GeneralAGM.lean) is `4·εDL + 2/p` at the curve, and
the [family corollary](../Signatures/SynchronizedPS/GeneralAGMFamilyStatement.lean) picks the best
key per security parameter, a solver family of the same class, to conclude negligible forgery under
nonuniform DLog hardness and negligible inverse field size.

Both [native private-cache branches](../Proofs/Runtime/BackendWeightedCache.lean)
now have derived runtime and stored-code bounds, including their implemented
comparisons and independent pair sampling. The bounds depend on encountered
entries and encoding widths. Exact laws preserve the answer, cache, and ambient
state; hits execute no sampler, and Proximity's source-to-native index encoding
preserves the whole cache behavior. Native private-read adapters also have full
runtime/code bounds, including executed fallback construction and state routing.
The [native weighted evaluator](../Proofs/Runtime/BackendWeightedEvaluate.lean)
preserves the source's ordered queries and joint value/cache law, with proved
stored-code bounds. Complete scalar/pair runtime and encoded-result/cache bounds
are now proved in `BackendWeightedGoodEvaluate.lean` and
`BackendWeightedBadEvaluate.lean`. They charge count/init/loop code, row scans,
private reads, arithmetic and cache growth under individual component contracts.
Injective index transport now connects both complete native evaluators to the
original source indices and preserves the entire cache. Native
[signing-coefficient expansion](../Proofs/Runtime/BackendWeightedCoefficients.lean)
has exact source laws, stored-code and encoded-output bounds. Its
[complete native runtime bounds](../Proofs/Runtime/BackendWeightedCoefficientBudget.lean)
now compose chronological matching, retained-context term generation, scaling,
both expansion folds and final reversal. The final OOPS/Proximity theorems derive
every generator and fold bound from individual primitive contracts; they do not
assume a completed expansion budget. These bounds now compose into the complete
solver certificates and concrete general-attacker endpoints described above.

Schnorr AGM now has a [short general-attacker theorem](../Signatures/Schnorr/Statement.lean)
with complete native runtime/code certificates and the original losses
`(qH+1)/|F| + qS*(qS+qH)/|F|`. The displayed game is exactly the source game.
[Polynomial closure](../Proofs/Runtime/BackendSchnorrAGMPolynomial.lean)
covers the actual complete solver formulas; [family resources](../Signatures/Schnorr/GeneralAGMFamilyResources.lean)
derive its nonuniform executable family in one fixed backend. The
[asymptotic corollary](../Signatures/Schnorr/GeneralAGMFamilyStatement.lean)
concludes negligible forgery under DLog hardness and negligible inverse field
size. Messages may be arbitrary, and numerical random ranges need not be
polynomial. The full-field ROM route now also has a
[short unrestricted-attacker statement](../Signatures/Schnorr/Statement.lean),
complete replaying native solver certificates and a
[nonuniform family corollary](../Signatures/Schnorr/GeneralROMFamilyStatement.lean)
derived from original polynomial resources. The nonzero-nonce route now has a
[lazy probability reduction](../Proofs/Schnorr/NonzeroLazyROM.lean)
preserving its original losses. Its compiled signing kernel now has complete
source/runtime/code and polynomial bounds. The
[finite-cache replay solver](../Proofs/Runtime/SchnorrNonzeroListReduction.lean)
has exact computation correspondence and query-dependent cache capacities.
The [installed private samplers and common-store signer](../Proofs/Runtime/BackendSchnorrNonzeroComponentsBudget.lean)
now have complete runtime/code bounds and polynomial closure from separate
original sampler profiles, with every private-tape transition charged.
The [actual nonzero dispatcher and caller](../Proofs/Runtime/BackendSchnorrNonzeroCallerResources.lean)
now have derived runtime bounds and adaptive capacity reservations from original
resources. The [complete native pass](../Proofs/Runtime/BackendSchnorrNonzeroPass.lean)
has exact source correspondence, [full runtime/output bounds](../Proofs/Runtime/BackendSchnorrNonzeroPassBudget.lean),
[code accounting](../Proofs/Runtime/BackendSchnorrNonzeroPassDescription.lean)
and [polynomial runtime closure](../Proofs/Runtime/BackendSchnorrNonzeroPassPolynomial.lean).
Both actual nonzero passes now run in the [complete replaying solver](../Proofs/Runtime/BackendSchnorrNonzeroSolver.lean).
Exact source correspondence, complete runtime/code bounds and their polynomial
closure construct its [fixed-backend executable certificate](../Proofs/Runtime/BackendSchnorrNonzeroSolverWithin.lean).
The [concrete hardness endpoint](../Proofs/Runtime/BackendSchnorrNonzeroSecurity.lean)
applies DLog hardness to that derived certificate, preserving the original
`|F|-1` signing denominator. The [short public statement](../Signatures/Schnorr/Statement.lean),
`Schnorr.NonzeroNonce.rom_security`, and [nonuniform family theorem](../Signatures/Schnorr/GeneralNonzeroROMFamilyStatement.lean)
now follow from that certificate. [Family resources](../Signatures/Schnorr/GeneralNonzeroROMFamilyResources.lean)
derive polynomial complete solver time/code, and the family proof derives
negligible inverse nonzero-field size from the same inverse-field growth assumption.
These results do not claim a conventional-machine instantiation.

Full certification uses a first-order executable runtime, rather than extending the ledgers
with assumed total costs. See the [runtime bounds and checked components](RUNTIME-CERTIFICATION.md).
`BLS.Statement.bls_eufcma_of_cocdh_machine_hardness` derives the exact named Coron solver's
budget from source code, a uniform source budget, and fixed data. Its closed-machine program
includes adaptive simulation, lazy caches, final hashing, extraction, data loading, and input
setup. `hbudget` is discharged by the compiler theorem, not supplied by the caller. Primitive
arithmetic and sampling prices remain explicit model contracts. The weaker public wrappers
have been deleted. The eager-table AGM wrappers are now retired too; their
[replacements](API-MIGRATION.md) accept general implemented attackers and derive
lazy solver budgets with stored-code accounting. The retained arithmetic-source
BLS co-CDH and Schnorr endpoints still infer their source/resource indices from
`cert`; those parameters remain part of their distinct implementation scope.

AGM component certificates now cover full-domain sampling, ordered keyed-table construction,
structured-key lookup, all three weight families, scalar/group sums, affine bases, and both
compiled adaptive simulators and final extractors, with exact native representation theorems. Their bounds and
tests are in the [runtime work plan](RUNTIME-CERTIFICATION.md#agm-adaptive-simulator-bounds).
Proximity now has a fixed-size structural vector encoding with a uniform weight bound for
every typed message. Both extractors charge chronological reversal and coefficient attachment,
including missing coefficients and repeated queries. AGM source certificates now require
all-key semantic equality and all-path coefficient sizes. Both complete packages have exact
named-solver erasure and proved `Machine.Within` budgets, including setup and data loading.
The bad package preserves kappa/a/b sampling order, constructs every masked group base,
and computes the source public key `kappa*g2`. No finished-solver runtime bound is assumed.

## Both sides of the argument

[`Model.HardWithin`](../Proofs/Model/Hardness.lean) states:

```text
for every solver B:
  within budget B -> advantage B <= epsilon
```

`within` must be instantiated by an implementation-backed resource predicate and any target-model
restrictions. It is not defined as oracle-query count, and no arbitrary runtime number is assigned
to an extensional Lean function. The public statements derive certificates for the exact named
solvers from the supplied source certificate, rather than taking solver-budget premises.
The hardness assertion is a theorem hypothesis, not a custom axiom or a proved property of DLog.

| Route | Conditional theorem | Numerical bound |
| --- | --- | --- |
| BLS co-CDH | [`bls_eufcma_of_cocdh_machine_hardness`](../Signatures/BLS/ArithmeticStatement.lean) | `coronFactor qS * epsilon` |
| BLS AGM | [`BLS.agm_security`](../Signatures/BLS/Statement.lean) (two budgets: `BLS.Proofs.agm_security`) | `goodEpsilon + badEpsilon + 1 / Nat.card F` |
| OOPS AGM | [`OOPS.agm_security`](../Signatures/OOPS/Statement.lean) (two budgets: `OOPS.Proofs.agm_security`) | same two-branch bound |
| Proximity AGM | [`Proximity.agm_security`](../Signatures/Proximity/Statement.lean) (two budgets: `Proximity.Proofs.agm_security`) | two-branch bound plus actual fresh-collision probability |
| Schnorr ROM | [`schnorr_eufcma_of_dlog_machine_hardness`](../Signatures/Schnorr/Statement.lean) | `delta * (delta/(qH+1) - 1/card F) <= epsilon`, where `delta = Adv - qS*(qS+qH)/card F` |
| Schnorr ROM, bit heap | [`schnorr_eufcma_of_dlog_bit_hardness`](../Signatures/Schnorr/BitStatement.lean) | same left side, bounded by `epsilon + targetBudget * 2^(-k)` at proved bit budget `(targetBudget+4)*bitFactor` |

Schnorr has a complete first-order two-pass controller, not a presumed constant-cost
continuation snapshot. Its source-derived budget includes cache/tape storage and scans,
re-execution, verification, extraction, fallback sampling, and fixed-data loading.
The erased machine equals the upstream `Schnorr.dlogReduction` exactly. See the
[Schnorr runtime review](SCHNORR.md).
The older arithmetic-source replay codec charges linearly in the range parameter of a finite
random request, not its bit length; see [the efficiency qualification](SCHNORR.md#what-efficiency-is-certified).

The existing reduction supplies the lower bound on solver success. `HardWithin`, applied with
the solver's certificate, supplies the upper bound. For AGM, the two solvers may have different
budgets and different hardness bounds; using one shared bound gives `2 * epsilon + 1/|F|`.
There is no separate lower bound on each AGM solver: the source bound involves their sum.
For Proximity, the inequality also includes the actual probability of a fresh linear collision
in the source execution. No source-wide noncollision hypothesis is required, but the theorem
does not prove this extra probability small. The term is not a random-hash collision bound.

## Concrete operation bounds

[`Signatures.OperationBounds`](../Proofs/OperationBounds.lean) exports the new bounds.
These are pathwise upper bounds, not averages. Hash/sign query bounds hold on every adaptive
continuation; repeated queries count again. AGM also requires bounds `Lh`, `Ls` on the lengths
of the adversary's returned coefficient lists. The hypotheses concern the source adversary,
not an assumed cost bound for the completed solver.

The annotated solvers erase to the **exact existing reductions** (`good_erase`, `bad_erase`,
and `reduction_erase`). Erasure preserves their probability results; it does not establish
the cost of a machine implementation. The counters describe the selected operations below,
not the runtime of evaluating the counters themselves.

### BLS co-CDH

[`BLS.CoCDH.Cost.reduction_bound`](../Proofs/BLS/CoCDH/OperationCost.lean) proves:

```text
group-operation allowance <= 2*(qH + 1) + qS + 2
```

One group scalar multiplication, addition, or subtraction is one unit. A hash is charged two
units, a signing reply at most one, and extraction two. `qH + 1` includes the hash inserted
by `cacheForgeryPK`, even for a forger making no queries. Signing on an aborting branch is
conservatively charged the same allowance. The API additionally takes a source-random-query
bound `qR`; its tariff is zero **in this group-operation ledger only**.

This is not the paper's total simulation-time formula: scalar/coin sampling, cache access,
equality, dispatch, and the adversary's local work are not counted here.

### Both AGM branches

The common [scalar ledger](../Proofs/Model/ScalarWork.lean) charges a unit for each field
operation (including division), indexed table read, equality/branch, and list-cell lookup.
Folds charge addition and iteration. The [reply ledger](../Proofs/Model/SimulationWork.lean)
also charges atomic group operations, dispatch for each hash/sign query, and transcript appends.
The last costs are quadratic because the current handler appends singleton lists.
Indexed reads assume random-access storage; equality is atomic, not a claim about message
encoding sizes. OOPS powers use repeated multiplication, with an explicit degree-dependent cost.

Write `n` for the number of private bases, `c` for the cost of a weight, `h = qH`, `s = qS`.
The extraction allowances and total **counted** overheads are:

```text
Egood = n*(h*(Lh + 4) + 4)
      + s*(Ls + n*(c + 4) + 4) + n*(c + 4) + 3
Ebad  = 2*n*(c + s*(Ls + c + 4) + 5) + 2

Good = Egood + h*(h + 4) + s*(n*(c + 4) + s + 3)
Bad  = Ebad  + h*(h + 7) + s*(n*(c + 8) + s + 3) + 1
```

The final `+1` in `Bad` is the scalar multiplication generating its fresh public key.
The bounds are deliberately conservative, including full coefficient-list scan allowances.

| Theorem in `Model.LazyAGM.Cost` | `n` | `c` |
| --- | --- | --- |
| `bls_bounds` | `Fintype.card M` | `1` |
| `oops_bounds` | `Fintype.card T * (d + 1)` | `2*d + 1` |
| `proximity_bounds` | `(ell + 1) * Fintype.card S` | `2` |

Each theorem bounds both branches. Its query and output-size hypotheses cover every generated
key, including the bad branch's fresh key. These work bounds hold even on unsuccessful forgeries
and require no noncollision hypothesis. The **security theorem** retains the scheme's
admissibility/algebraic requirements and accounts for Proximity collisions as an additive
source-game probability rather than an all-path assumption.

The full-domain `n` factor cannot be replaced by `qH`: signing and extraction in these exact
reductions sum over every private base. Good also samples one entire private table; bad samples
two and a scalar. **Those sampling costs and the adversary's local work are not included.**
Consequently these ledgers alone do not prove `T_reduction <= T_adversary + Good/Bad` or discharge
runtime certificates. The separate closed-machine proofs now charge and certify those missing
operations; their total formulas are in the [runtime audit](RUNTIME-CERTIFICATION.md#complete-agm-certificates).

[OperationBounds tests](../SignaturesTest/OperationBounds.lean) check all six AGM erasures,
adaptive/repeated queries, the inserted forgery hash, coefficient scans, degree/coordinate costs,
and the standard axiom footprints of all four bound endpoints and their erasure lemmas.

## What the papers say

The [BLS full paper, Theorem 3.2](https://www.cs.utexas.edu/~hovav/dist/sigs.pdf#page=5)
includes both probability loss and simulation time:

```text
epsilon >= e * (qS + 1) * epsilon'
t <= t' - c_G1 * (qH + 2*qS)
```

Thus `qH` affects its time bound, not its multiplicative probability loss. This is not a proved
runtime formula for our concrete Lean implementation, which also needs an implementation of
caching, sampling, arithmetic, and adversary computation. Our challenge also uses the explicit
G1 co-hint, rather than the paper's efficiently computable G2-to-G1 isomorphism.

For [OOPS (2025/2340)](https://eprint.iacr.org/2025/2340), the locally supplied December 2025
PDF was checked (SHA-256 `f488cb804cae922894930ccaecf327782e3fee287604f0b304475cb6dfe7a421`).
Section 3 defines hardness against polynomial-time algebraic adversaries. Section 5.1.1
introduces `qH` and `qS`; Section 5.1.2 gives the oracle simulator and extraction formulas.
That section does **not** give a concrete simulator runtime inequality like BLS's.
The current online PDF could not be fetched, so this is a claim about the local revision only.

Reading its simulator as efficient requires accounting for queried bases, signed messages,
degrees, coefficient representations, and encodings. In particular, work linear in a supplied
degree is not necessarily polynomial in its binary encoding length. This is a cost audit, not
a fresh certification of all the paper's extraction/probability arguments.

## Why query bounds are insufficient

VCVio's `IsQueryBoundP` counts selected oracle interactions. Its `CostModel` charges oracle
queries. An arbitrary pure function still has zero queries, even if implementing it takes
exponential time. A regression in [Hardness.lean](../SignaturesTest/Hardness.lean) records this
boundary. Query counts alone cannot justify computational DLog/co-CDH hardness.

The pinned VCVio also provides backend-relative `IsOraclePPTBy`, with executable realization,
input/output sizes, and pathwise resource bounds. Instantiating that API requires additional
implementation evidence; importing it is not itself an efficiency proof.

## Scope Beyond These Bounds

- The arithmetic-machine endpoints use atomic field/group/equality cost contracts.
  Schnorr's additional [bit-machine endpoint](../Signatures/Schnorr/BitStatement.lean)
  connects the concrete instruction backend, full program, heap, and fair-bit
  sampling implementation to the security inequality. Its cost model is explicit
  bit-cell execution, not a proved correspondence to Lean VM or hardware time.
- The bit endpoint also restricts stored code/data to the actual compiled
  artifact's size. The arithmetic-machine endpoints restrict online work only,
  not static code size. An enormous lookup tree can have short execution paths;
  their hardness assumptions are stronger than bounded-size circuit hardness.
- Applying a retained arithmetic-source corollary requires a source-code certificate for the adversary. Arbitrary
  extensional Lean functions are not automatically efficient; source local work and all-path
  coefficient sizes remain explicit. Proximity message dimension is enforced by its tuple type.
- The original eager reference implementations retain domain-size costs. The public
  general-caller routes use the proved equivalent lazy reductions and their derived budgets.
- The general asymptotic results use parameterized group families, polynomial original
  resources, nonuniform hardness in one fixed backend and the stated field-growth/collision
  assumptions. Fixed finite types alone do not supply these conditions.

The eager-table BLS/OOPS/Proximity AGM security wrappers are retired; see the
[API migration guide](API-MIGRATION.md). Their supporting probability and resource
lemmas remain. The retained arithmetic-source BLS co-CDH and Schnorr statements
have their separate implementation scopes. The public general-attacker endpoints
use measured backend realizations, derive complete runtime/code bounds, and
preserve the original source games. No standard-model OOPS or concrete-hash claim
is added.
