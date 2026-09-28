# Computational-security status

**Status: internal probability reductions, concrete operation ledgers,
and public arithmetic-machine security statements for all four routes are proved,
including both AGM branches. This is not a bit-complexity or asymptotic PPT theorem.**

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

In all four concrete corollaries, Lean infers the adversary, primitive-cost model, local time,
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

- A bit-level backend needs encodings and implementations of the priced primitives. Atomic
  field/group operations and key equality are model contracts, not proved bit costs.
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
