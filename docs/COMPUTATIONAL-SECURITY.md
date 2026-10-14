# Computational-security status

**Status: internal probability reductions, concrete operation ledgers,
and public arithmetic-machine security statements for all five routes are proved,
including both AGM branches and Schnorr's full replay reduction.
Schnorr additionally has a precompiled bit-cell security theorem with explicit
sampling error. No conventional-machine PPT or hardware-timing theorem is claimed.**

BLS co-CDH additionally exposes
[`Coron.NativeSolver.security_of_resources`](../Signatures/Runtime/BackendCoronSecurity.lean),
imported by `Signatures`. It quantifies over general backend-realized attacker
code, uses its actual `RunsWithin` resource bound, and constructs the completed
native solver certificate before applying hardness. Request/result decoding has
an explicit size-recovery contract; canonical message encodings satisfy it from
the product/sum size laws. The attacker need not use the arithmetic language.
The co-CDH hardness class uses the same fixed backend, separate input/code/time
caps, and a bound covering every challenge in the experiment. The conclusion
retains the exact Coron factor and now allows arbitrary message types.
[`BackendCoronPolynomial`](../Signatures/Runtime/BackendCoronPolynomial.lean)
proves polynomial growth of the derived runtime and description budgets under
fixed polynomial resource contracts and jointly polynomial structural overhead.
[`BackendCoronFamilySecurity`](../Signatures/Runtime/BackendCoronFamilySecurity.lean)
now proves negligible BLS forgery success under co-CDH hardness against
polynomial-time, polynomial-description nonuniform families in the same fixed
backend. Scalar/group/message types may vary with the security parameter; each
parameter chooses one program for all inputs. All fixed code/advice is charged.
The solver's efficiency is derived from the general caller and primitive
contracts. Every generated challenge fits the fixed input cap, and the exact
Coron loss is bounded by `3*(qS+1)`, including zero signing queries.
This remains conditional on the backend and its encoding/cost contracts; no
uniform program generator or conventional-machine instantiation is claimed.
[`ArbitraryMessages`](../Signatures/BLS/CoCDH/Proofs/ArbitraryMessages.lean)
removes the finite-message assumption by exact transport of the original lazy
game and solver. A finite cover of all adaptive requests and final outputs is
used only inside the proof; no executable code enumerates it. The cover ranges
over generated public keys, so the public-key type need not be finite either.
The arithmetic-source endpoint also uses this stronger probability result.
The other general-attacker routes remain open in the
[current plan](GENERAL-ADVERSARY-REDUCTION-PLAN.md).

The new [lazy BLS AGM solvers](../Signatures/BLS/Spec/LazyAGMReduction.lean)
now preserve the established two-reduction probability bound on arbitrary message
types, with joint randomness correspondence and sparse transcript extraction.
Their [association-list cache refinement](../Signatures/BLS/Proofs/LazyAGMList.lean)
works over arbitrary message types and bounds stored entries by `2*q+1` for
`q` attacker requests. The [probability transport](../Signatures/BLS/Proofs/LazyAGMArbitraryMessages.lean)
uses a finite cover only inside the proof; the public-key type need not be finite.
Their [native private-cache implementations](../Signatures/Runtime/BackendLazyAGMCache.lean)
now have exact list-handler semantics and derived runtime/code bounds. Independent
pair sampling is implemented with two charged scalar samplers; hits execute no
sampler. The [native hash/sign replies](../Signatures/Runtime/BackendLazyAGMReply.lean)
now have exact adaptive correspondence, stored-code bounds, encoded-store
invariants, and [complete runtime bounds](../Signatures/Runtime/BackendLazyAGMReplyBudget.lean)
derived from primitive costs. These include argument/store copying, transcript
updates, arithmetic, and control. Native
[chronological coefficient matching](../Signatures/Runtime/BackendTokenRows.lean)
now has complete runtime/code and output-size bounds. These compose the actual
coefficient scans, both reversals, zero initialization, and retained-context costs.
[Coefficient lengths](../Signatures/Runtime/BackendLazyAGMOutputSize.lean) are
bounded by encoded output size under an explicit positive-cell encoding law.
The [native effectful evaluators](../Signatures/Runtime/BackendLazyAGMEvaluate.lean)
and [complete extractors](../Signatures/Runtime/BackendLazyAGMExtraction.lean)
now preserve the joint output/cache law, including final-target processing and
zero denominators. Their [reachable-cache bounds](../Signatures/Runtime/BackendLazyAGMExtractionGrowth.lean)
depend only on processed rows and the final target. Private extraction reads have
[complete runtime bounds](../Signatures/Runtime/BackendLazyAGMReadBudget.lean)
and [stored-code bounds](../Signatures/Runtime/BackendLazyAGMReadDescription.lean);
the [executed length fold](../Signatures/Runtime/BackendLengthCost.lean) is charged.
Whole-evaluator/extractor [stored-code bounds](../Signatures/Runtime/BackendLazyAGMExtractionDescription.lean)
are now proved. Complete [good evaluator](../Signatures/Runtime/BackendLazyAGMGoodEvaluate.lean)
and [bad evaluator](../Signatures/Runtime/BackendLazyAGMBadEvaluate.lean) runtime
bounds are derived from primitive, encoding, and loop-control contracts. They
charge length computation, row/cache scans, sampling, arithmetic, copying, and
retained contexts, with no message-universe enumeration. Complete chronological
[good](../Signatures/Runtime/BackendLazyAGMGoodTokens.lean) and
[bad](../Signatures/Runtime/BackendLazyAGMBadTokens.lean) preparation/evaluation
calls now compose these bounds, including coefficient processing and cache-state
invariants. Complete [good extractor](../Signatures/Runtime/BackendLazyAGMGoodExtractionBudget.lean)
and [bad extractor](../Signatures/Runtime/BackendLazyAGMBadExtractionBudget.lean)
runtime bounds now compose default creation, every chronological call, final
target access, and arithmetic, including retained output/transcript frames and
changing cache capacities. They follow from individual primitive and encoding
contracts, with no finished-extractor budget premise. The native general-request
[dispatchers](../Signatures/Runtime/BackendLazyAGMHandler.lean) now preserve
adaptive caller source semantics and have derived
[runtime](../Signatures/Runtime/BackendLazyAGMHandlerBudget.lean) and
[stored-code](../Signatures/Runtime/BackendLazyAGMHandlerDescription.lean) bounds.
Their invariants reserve cache and transcript space for remaining requests.
Both native [caller resource bounds](../Signatures/Runtime/BackendLazyAGMCallerResources.lean)
now derive additive runtime and final-store bounds from the attacker's own
execution resources and primitive contracts. Complete caller descriptions are
also bounded. Request sizes, reachability, return sizes, and termination are
derived, with no custom caller invariant or assumed whole-caller budget.
The [returned AGM representation](../Signatures/Runtime/BackendLazyAGMCallerOutput.lean)
also yields coefficient-length bounds under the canonical output encoding and
positive-cell list law. Both complete [native solver programs](../Signatures/Runtime/BackendLazyAGMSolver.lean)
are assembled, and their [source laws](../Signatures/Runtime/BackendLazyAGMSolverCorrectness.lean)
identify them with the named lazy list reductions at every challenge. Complete
[runtime](../Signatures/Runtime/BackendLazyAGMSolverBudget.lean) and
[stored-code](../Signatures/Runtime/BackendLazyAGMSolverDescription.lean) bounds
now compose setup, the caller, output adaptation, and extraction. Both actual
executables have [fixed-backend resource certificates](../Signatures/Runtime/BackendLazyAGMSolverWithin.lean),
which supply the DLog premises in the
[concrete security theorem](../Signatures/Runtime/BackendLazyAGMSecurity.lean).
The [public statement](../Signatures/BLS/Security.lean) takes the curve,
security parameter, query allowances, and algebraic adversary. Its bound is the
sum of maximum DLog advantages at the two derived budgets plus `1/|F|`. The
[separate execution model](../Signatures/BLS/SecurityModel.lean) and
[detailed records](../Signatures/BLS/GeneralAGMParameters.lean) expose per-kind
query limits, local resources, code/advice, encodings, and primitive contracts.
They do not assume completed-solver efficiency. Arbitrary message types and
noncanonical output encodings are supported via the charged output adapter and
its size contract. Polynomial-family closure for AGM and the other schemes'
general-attacker endpoints remain open.
The existing AGM machine certificates
below still concern the eager implementations.

OOPS and Proximity now have shared
[weighted lazy solver programs](../Signatures/LinearFunctional/Spec/LazyAGMReduction.lean),
[joint eager/lazy distribution correspondence](../Signatures/LinearFunctional/Proofs/LazyAGMCoupling.lean),
and probability bounds using those solvers for arbitrary topic/slot types. Their
complete program caches have at most `qH + (qS + 1) * L` entries, where `L = d + 1`
or `ell + 1`; transcript extraction is proved to make no fresh draws. The
cache/program definitions and entry-count theorems permit infinite domains.
The [OOPS arbitrary-topic theorem](../Signatures/OOPS/Proofs/LazyAGMArbitraryTopics.lean)
and [Proximity arbitrary-slot theorem](../Signatures/Proximity/Proofs/LazyAGMArbitrarySlots.lean)
use finite covers only inside the proofs. Exact transport preserves all adaptive
requests, the source games, and the actual Proximity collision term, without
requiring a finite public-key type. Complete native weighted runtime/code bounds
remain open; these results do not replace local-computation and encoding accounting.

Full certification uses a first-order executable runtime, rather than extending the ledgers
with assumed total costs. See the [runtime bounds and checked components](RUNTIME-CERTIFICATION.md).
`BLS.Statement.bls_eufcma_of_cocdh_machine_hardness` derives the exact named Coron solver's
budget from source code, a uniform source budget, and fixed data. Its closed-machine program
includes adaptive simulation, lazy caches, final hashing, extraction, data loading, and input
setup. `hbudget` is discharged by the compiler theorem, not supplied by the caller. Primitive
arithmetic and sampling prices remain explicit model contracts. The weaker public wrappers
have been deleted. The AGM statements in
[BLS](../Signatures/BLS/Statement.lean), [OOPS](../Signatures/OOPS/Statement.lean), and
[Proximity](../Signatures/Proximity/Statement.lean) also derive both solver budgets from source
certificates and concrete primitive prices.

In all five concrete corollaries, Lean infers the adversary, primitive-cost model, local time,
query budgets, and random-arity bound from `cert`; the AGM coefficient-length bounds are inferred
as well. These remain parameters of the claim, not removed assumptions. Sampling costs and the
hardness hypotheses remain explicit; no runtime or security premise is silently discharged by inference.

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

[`Model.HardWithin`](../Signatures/Model/Hardness.lean) states:

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
| BLS co-CDH | [`bls_eufcma_of_cocdh_machine_hardness`](../Signatures/BLS/Statement.lean) | `coronFactor qS * epsilon` |
| BLS AGM | [`bls_lazy_agm_of_dlog_machine_hardness`](../Signatures/BLS/Statement.lean) | `goodEpsilon + badEpsilon + 1 / Nat.card F` |
| OOPS AGM | [`oops_lazy_agm_of_dlog_machine_hardness`](../Signatures/OOPS/Statement.lean) | same two-branch bound |
| Proximity AGM | [`proximity_lazy_agm_of_dlog_machine_hardness`](../Signatures/Proximity/Statement.lean) | two-branch bound plus actual fresh-collision probability |
| Schnorr ROM | [`schnorr_eufcma_of_dlog_machine_hardness`](../Signatures/Schnorr/Statement.lean) | `delta * (delta/(qH+1) - 1/card F) <= epsilon`, where `delta = Adv - qS*(qS+qH)/card F` |
| Schnorr ROM, bit heap | [`schnorr_eufcma_of_dlog_bit_hardness`](../Signatures/Schnorr/BitStatement.lean) | same left side, bounded by `epsilon + targetBudget * 2^(-k)` at proved bit budget `(targetBudget+4)*bitFactor` |

Schnorr has a complete first-order two-pass controller, not a presumed constant-cost
continuation snapshot. Its source-derived budget includes cache/tape storage and scans,
re-execution, verification, extraction, fallback sampling, and fixed-data loading.
The erased machine equals the upstream `Schnorr.dlogReduction` exactly. See the
[Schnorr runtime review](SCHNORR.md).
The current replay codec charges linearly in the range parameter of a finite
random request, not its bit length; see [the efficiency qualification](SCHNORR.md#what-efficiency-is-certified).

The existing reduction supplies the lower bound on solver success. `HardWithin`, applied with
the solver's certificate, supplies the upper bound. For AGM, the two solvers may have different
budgets and different hardness bounds; using one shared bound gives `2 * epsilon + 1/|F|`.
There is no separate lower bound on each AGM solver: the source bound involves their sum.
For Proximity, the inequality also includes the actual probability of a fresh linear collision
in the source execution. No source-wide noncollision hypothesis is required, but the theorem
does not prove this extra probability small. The term is not a random-hash collision bound.

## Concrete operation bounds

[`Signatures.OperationBounds`](../Signatures/OperationBounds.lean) exports the new bounds.
These are pathwise upper bounds, not averages. Hash/sign query bounds hold on every adaptive
continuation; repeated queries count again. AGM also requires bounds `Lh`, `Ls` on the lengths
of the adversary's returned coefficient lists. The hypotheses concern the source adversary,
not an assumed cost bound for the completed solver.

The annotated solvers erase to the **exact existing reductions** (`good_erase`, `bad_erase`,
and `reduction_erase`). Erasure preserves their probability results; it does not establish
the cost of a machine implementation. The counters describe the selected operations below,
not the runtime of evaluating the counters themselves.

### BLS co-CDH

[`BLS.CoCDH.Cost.reduction_bound`](../Signatures/BLS/CoCDH/Proofs/OperationCost.lean) proves:

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

The common [scalar ledger](../Signatures/Model/ScalarWork.lean) charges a unit for each field
operation (including division), indexed table read, equality/branch, and list-cell lookup.
Folds charge addition and iteration. The [reply ledger](../Signatures/Model/SimulationWork.lean)
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
- Applying a concrete corollary requires a source-code certificate for the adversary. Arbitrary
  extensional Lean functions are not automatically efficient; source local work and all-path
  coefficient sizes remain explicit. Proximity message dimension is enforced by its tuple type.
- Either retain those domain-size costs with explicit polynomial-size assumptions, or construct
  sparse lazy reductions and prove their equality to the existing probability reductions.
- For asymptotic security also supply a uniform parameterized group family, polynomial resource
  bounds, and negligible target advantage/collision terms. Fixed finite types do not supply these.

Only the concrete-machine security endpoints remain. They derive the solver budgets from source
certificates; no `hbudget`, `hgood`, or `hbad` is assumed. The original games and underlying
reduction proofs are unchanged. No standard-model OOPS or concrete-hash claim is added.
