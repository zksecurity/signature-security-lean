# Signature security review

Five lazy random-oracle security routes for BLS, OOPS, Proximity, and Schnorr.

For Schnorr, follow the separate [game, rewinding, and cost review](SCHNORR.md).
Its [bit-machine endpoint](../Signatures/Schnorr/BitStatement.lean) uses the same
source game and a fully costed compiled solver, with explicit rejection-sampling
error and a separate static code/data budget. Follow
[the implementation evidence](BIT-COMPLEXITY.md) for its memory,
arithmetic, randomness, and probability refinements.
It includes the source certificate, exact reduction bridge, public costed theorem,
and a separate test review. The pairing-based routes are detailed below.
Kernel checking proves each implication from its hypotheses; it does not establish paper/model alignment.

For the new general-attacker BLS AGM endpoint, start at
[`BLS.agm_security`](../Signatures/BLS/Statement.lean): curve, security parameter,
query allowances, and algebraic adversary, followed by the named game's probability
bound. The [declared execution model](../Signatures/BLS/GeneralSecurityModel.lean) and
[detailed resource records](../Signatures/BLS/GeneralAGMParameters.lean) remain inspectable. The full
[resource-indexed theorem](../Signatures/Runtime/BackendLazyAGMSecurity.lean)
constructs both native solver certificates before applying DLog hardness.
The same public file also contains `BLS.cocdh_security`, with an unrestricted
attacker and the co-CDH success bound. Its resources are in
[`GeneralCoCDHParameters.lean`](../Signatures/BLS/GeneralCoCDHParameters.lean).
The public proof bodies are in
[`Proofs/GeneralSecurity.lean`](../Signatures/BLS/Proofs/GeneralSecurity.lean).
The [plan](GENERAL-ADVERSARY-REDUCTION-PLAN.md) distinguishes this completed
concrete route from the remaining scheme and family work.

[Game ledger](SECURITY-GAMES.md) · [Source tree](../Signatures) ·
[Regression tests](../SignaturesTest) ·
[Start a review issue](https://github.com/zksecurity/signature-security-lean/issues/new?template=security-review.md)

This guide is plain GitHub Markdown: no JavaScript, browser storage, or separate site is required.
Record the commit under review and findings in an issue or pull-request review. The task list
below is a review template, not a claim that a paper audit has been completed.

## Game and oracle definitions

The three AGM scheme files specialize a shared signature game; they are not the entire game.
Read the implementation in this order:

1. [Oracle interface](../Signatures/Model/SignatureInterface.lean): `advSpec` allows private
   randomness, base/hash queries, and signing queries. `Adversary.main` receives the public key
   and may choose later queries using earlier replies.
2. [Oracle dispatcher](../Signatures/Model/SignatureInteraction.lean): `Interactive.impl`
   handles those three query variants. Randomness returns plain data; hash and signing each
   return one tracked signature-group point. `compile` connects this interface to the
   certified AGM adversary, and `initialInput` supplies the generator and public key.
3. [Signing and winning check](../Signatures/Model/LazyAGM.lean): `signing` computes the
   secret-key multiple of the message's weighted hash sum. `experiment` samples the key,
   runs the adversary through `interactiveRun`, and checks the pairing equation, freshness,
   and the scheme's additional condition, if any.
4. [Lazy oracle and probability](../Signatures/Model/LazyAGM.lean): `lazyImpl` supplies the
   persistent random-oracle cache. `game` starts that cache empty; `advantage` measures the
   probability that the resulting experiment returns `true`.

The scheme-specific hash inputs and signing rules are:

| Scheme | Hash query | Signing query and reply |
| --- | --- | --- |
| [BLS](../Signatures/BLS/Spec/LazyAGM.lean) | Message `m` | `m` returns `alpha * H(m)` |
| [OOPS](../Signatures/OOPS/Spec/LazyAGM.lean) | `(topic, j)`, with `0 <= j <= d` | `(m, topic)` returns `alpha * sum_j m^j * H(topic, j)` |
| [Proximity](../Signatures/Proximity/Spec/LazyAGM.lean) | `(coordinate, slot)`, where `none` selects the constant base | `(m, slot)` returns `alpha * (H(none, slot) + sum_k m[k] * H(some k, slot))` |

Here `alpha` is the secret scalar and multiplication by a group point means scalar action.
All three share the same cache across explicit hash queries, internal signing lookups,
and final verification. A cache entry is not itself an AGM input: only group points
actually returned to the adversary join its tracked basis, alongside the initial inputs.
OOPS fixes `d` for the entire game and checks its target-topic distinct-message limit at
the end. Proximity measures fresh linear collisions separately; the game does not reject them.

The **non-AGM BLS co-CDH route** has its own
[fully annotated game](../Signatures/BLS/CoCDH/Spec/LazyGame.lean): `realOracle` handles
randomness, hashing, and signing; `getDlogS` maintains the private lazy hash-exponent cache;
`blsEufLazyPK` arranges the final hash lookup and calls `blsEufTightPK` for key generation,
execution, and the winning check. This adversary returns a raw candidate signature and
does not supply an algebraic explanation.

## Results

The short BLS statements are [`BLS.agm_security` and `BLS.cocdh_security`](../Signatures/BLS/Statement.lean).
Their model and adversary definitions expose the distinct execution and resource assumptions.
The detailed arithmetic-source security statements are annotated line by line in
[BLS/ArithmeticStatement.lean](../Signatures/BLS/ArithmeticStatement.lean),
[OOPS/Statement.lean](../Signatures/OOPS/Statement.lean), and
[Proximity/Statement.lean](../Signatures/Proximity/Statement.lean).
Use those supporting files for the source-certified adversaries and detailed bounds; use the
game/oracle reading map above to unfold what their winning events mean. Only the concrete
machine-bounded endpoints are exposed: source certificates include hash/sign/random query
budgets and local work. The earlier weaker wrappers are deleted, not retained as private endpoints.

### BLS: lazy ROM to co-CDH

- [Statement](../Signatures/BLS/ArithmeticStatement.lean): `BLS.Statement.bls_eufcma_of_cocdh_machine_hardness`.
- [Source game](../Signatures/BLS/CoCDH/Spec/LazyGame.lean): `blsEufLazyPK`.
- [Coron reduction](../Signatures/BLS/CoCDH/Spec/Coron.lean) and
  [query-budget proof](../Signatures/BLS/CoCDH/Proofs/QueryBound.lean).
- Bound: `Adv_ROM <= coronFactor(qS) * epsilon`, assuming co-CDH hardness at the derived solver budget.
- Finite messages, without a caller-supplied enumeration. The budget counts all signing calls,
  including repeats, on every generated key. The source certificate additionally bounds all
  hash (`queries 1`), random (`queries 0`), and signing (`queries 2`) calls and local computation.

### BLS: query-only lazy AGM

- [Statement](../Signatures/BLS/ArithmeticStatement.lean): `BLS.Statement.bls_lazy_agm_of_dlog_machine_hardness`.
- [Source game](../Signatures/BLS/Spec/LazyAGM.lean) and [proof](../Signatures/BLS/Proofs/LazyAGM.lean).
- Bound: `Adv_source <= goodEpsilon + badEpsilon + 1/|F|`, with hardness at each derived solver budget.
- Finite message indices; certified all-path query/local-work and coefficient-size bounds.
  Only explicit base and signing replies supply representation tokens.
- Freshness proves a nonzero symbolic coefficient. Unlike Proximity, the corresponding
  fresh symbolic-collision event has probability zero, with no noncollision assumption.
  Evaluation can still give zero; the independent hidden-slope collision costs `1/|F|`.

### OOPS: query-only lazy AGM

- [Statement](../Signatures/OOPS/Statement.lean): `OOPS.Statement.oops_lazy_agm_of_dlog_machine_hardness`.
- [Source game and degree rule](../Signatures/OOPS/Spec/LazyAGM.lean) and
  [proof](../Signatures/OOPS/Proofs/LazyAGM.lean).
- Same two-reduction bound. Oracle-derived topic bases, finite topic type.
- At most `d` distinct signed scalar messages on the eventual forgery topic. Repetitions and
  other topics do not consume this cap. Freshness concerns the entire message/topic pair.
- Freshness and this winning degree rule imply a nonzero symbolic coefficient by Vandermonde.
  Symbolic collisions within the winning rule have probability zero, not an assumed small bound.
  Neither this fact nor BLS's rules out sampled hash collisions; both retain the independent
  hidden-slope collision bound `1/|F|`, not a bound on every collision in the hash transcript.

### Proximity: query-only lazy AGM, with collisions

- [Statement](../Signatures/Proximity/Statement.lean): `Proximity.Statement.proximity_lazy_agm_of_dlog_machine_hardness`.
- [Source game and collision event](../Signatures/Proximity/Spec/LazyAGM.lean) and
  [proof](../Signatures/Proximity/Proofs/LazyAGM.lean).
- Bound: `Adv_source <= goodEpsilon + badEpsilon + 1/|F| + Pr[fresh collision]`.
  Oracle-derived coordinate bases, finite slot/topic type.
- `Collision out signed` means the full vector/slot output is fresh and its vector equals
  the sum of signed vectors weighted by the output's signing coefficients. Repeats and other
  slots contribute; missing coefficients are zero. Signature validity is not required by this event.
- `collisionGame` measures that event under the original key sampling and lazy adaptive oracles.
  The proof establishes equality with an observer of certified execution, then lazy/table equality.
  There is no all-path noncollision premise and no change to the forgery winning check.
  No small upper bound on this extra probability is proved; it can be one.

## Conditional hardness bounds

Each route's sole public endpoint combines its existing reduction and proved machine budget with
[`Model.HardWithin`](../Signatures/Model/Hardness.lean): every solver in an explicitly supplied
budget-bounded class has success at most `epsilon`.

The caller certifies the **source adversary**; the compiler proves resource bounds for the exact
named target solvers. AGM needs two hardness bounds at those derived budgets, giving
`Adv_source <= goodEpsilon + badEpsilon + 1/|F|`, plus the fresh-collision probability for Proximity.
Co-CDH gives `Adv_source <= coronFactor(qS) * epsilon`.

**Concrete operation bounds now cover all four routes**, including both AGM branches; see
[`OperationBounds.lean`](../Signatures/OperationBounds.lean). Erasing the ledgers gives the
original solvers. Review the `qH`/`qS`, coefficient-size, finite-domain, and weight-cost factors.
**The arithmetic-source BLS co-CDH endpoint** in [BLS/ArithmeticStatement.lean](../Signatures/BLS/ArithmeticStatement.lean) uses
the [Coron source certificate](../Signatures/Runtime/CoronCertificate.lean).
Review its source certificate, all-key trace equality,
adaptive source budget, and charged fixed data. The compiler proves the exact named solver's
budget; no `hbudget` premise is required. Primitive operation/sampling prices are explicit
contracts, not bit-runtime proofs.

**The three arithmetic-source AGM endpoints** live in BLS's `ArithmeticStatement.lean`
and the OOPS and Proximity `Statement.lean` files linked above.
The caller supplies an
[AGM source certificate](../Signatures/Runtime/AGMSource.lean), not `hgood`/`hbad`.
The [good package](../Signatures/Runtime/AGMGoodMachine.lean) and
[bad package](../Signatures/Runtime/AGMBadMachine.lean) prove both exact named solvers'
`Machine.Within` budgets. Check full-domain table sampling, canonical-enumeration loading,
source data, simulation, and extraction. The bad package samples kappa, all a-values, then all
b-values, constructs masked bases, and gives the source `kappa*g2`. Proximity uses structural
vectors with charged coordinate reads. Its bound also accounts for fresh linear collisions.
All four concrete corollaries infer the adversary, primitive costs, and source resource indices
from `cert`. Review those indices in the certificate; they have not been dropped from the bounds.
Read the [runtime audit](COMPUTATIONAL-SECURITY.md) before interpreting a resource predicate
as machine time or PPT.

## Paper-facing statements

[BLS.Statement](../Signatures/BLS/ArithmeticStatement.lean) intentionally retains the **type-3**
formulation, not the original paper's map-based setting. The co-CDH solver receives
`(g1, g2, x*g1, x*g2, h)` and must output `x*h`. The explicit `x*g1` co-hint is part of
the hardness challenge, not a map or a value supplied to the signature adversary.
Neither the reduction proof nor the concrete-machine statement assumes or uses a
G2-to-G1 map. The map-based adapter has been removed.

[PaperStatements.lean](../Signatures/PaperStatements.lean) supplies an OOPS
game comparison without adding another security endpoint:

- `OOPS.LazyAGM.callGame` keeps **one degree `d` fixed for the whole
  game** and requires at most `d` signing calls on the final target topic. Repeated
  calls count again; other topics do not consume that limit. The original theorem
  allows up to `d` distinct messages instead. `OOPS.LazyAGM.callGame_le_game` proves
  the call-count game has no greater success probability, so the same named solvers
  and their resource bounds remain applicable by transitivity. The weaker call-count security
  wrapper has been removed. This game comparison needs no finite
  topic type; the actual DLog reduction still requires finite topics.

Scalar equality in the DLog and OOPS winning checks is classical, as in the other lazy
source games' winning checks. The probability statements therefore need no caller-supplied
`DecidableEq F`. Exact experiment-equality proofs preserve the former checks with any
supplied decider. This removes no instruction or cost from a solver: executable machine
certificates retain their equality instances and costs. The computable OOPS `admissible`
helper still accepts a decider; the game supplies one internally.

BLS also uses classical target-group equality for final signature verification. Its
co-CDH machine-bounded statement requires no `DecidableEq Gₜ`.
The lazy game is proved identical to the former version with a supplied decider,
including the final hash lookup and freshness check. Solver operations and costs
are unchanged; this check is performed by the security experiment, not the solver.

The co-CDH experiment likewise judges its answer using classical G1 equality. BLS's
experiment with any supplied decider is proved exactly equal. The public machine-bounded
statement retains G1 equality for executable operations and their costs, not for adjudication.

**Which OOPS degree convention?** The local December 2025 revision of
[OOPS, Section 5.1.1](https://eprint.iacr.org/2025/2340) says each signing query contains
a message, topic, and degree; Section 5's `Setup` supplies group/hash parameters,
while `GenerateTopic` accepts `d`. Thus the current Lean statements are a fixed-degree
specialization of that revision, not a mixed-degree game. A deployment can fix its
degree in advance, and the formalization retains that convention. This comparison
is against the local PDF, not a claim about an unverified newer revision.

Remaining differences are intentional and visible: finite topic/slot domains in
the current OOPS/Proximity endpoints;
the exact Coron factor instead of the paper's `e*(qS+1)` relaxation; arithmetic-machine
costs instead of a proved translation to the paper's time units; and the explicit
fresh-collision probability term for Proximity. The legacy AGM reductions initialize private
full-domain tables; the general BLS AGM endpoint uses the proved lazy implementation
over arbitrary message types. Our DLog challenge samples from all of `F`, including zero;
the local OOPS paper defines its hardness challenge over nonzero scalars. These
adapters do not change that distribution or prove an equivalence between them.
No conventional-machine PPT coverage or small Proximity forgery bound without
controlling collisions is asserted.

## Read the co-CDH runtime statement

Read `bls_eufcma_of_cocdh_machine_hardness` as an implication: **if the hypotheses above
the final colon hold, then the highlighted forgery-probability bound follows.**

1. **Setting and signing limit.** `g₁` and `g₂` are the public group generators;
   `hgen` says scalar multiples of `g₁` cover G1, and `hpair` excludes a zero pairing.
   `hqs` bounds signing calls by `qS` for every generated key. `(·.isRight)` abbreviates
   the predicate `fun i => Sum.isRight i = true`: it selects signing queries in the
   source oracle interface, not hash queries.
2. **Query budgets.** `queries : Fin 3 → Nat` is a three-entry vector of upper bounds:
   `queries 0` counts private-random calls, `queries 1` counts hash calls (`qH`), and
   `queries 2` counts signing calls. Repeats count again. The source certificate covers
   every allowed adaptive reply path. Its signing budget need not equal the separate `qS`.
3. **Counts versus costs.** `cost` prices arithmetic/equality primitives; `sampling` prices
   primitive random draws, not query counts. `localTime` bounds the adversary's local work.
   `randomBound` limits each private-random request's arity, not how many requests it makes.
4. **Implementation evidence.** `cert` ties actual source code to `adv` and certifies its
   resource bounds. Lean infers `{adv}`, `{cost}`, and the resource indices from its type.
   `cert.targetBudget sampling qS` uses those indices, including `qH`, plus simulation,
   caching, setup, final hashing, extraction, and data-loading costs. `queries` does not
   become part of `sampling`; the budget calculation uses both.
5. **Hardness hypothesis.** `hhard` says every co-CDH solver in the specified machine class,
   within that target budget, succeeds with probability at most `epsilon`.
   This is assumed hardness, not a proof that co-CDH is hard.
6. **Conclusion.** `𝒟[game] {true}` is the probability the game returns `true`, meaning a
   winning forgery. It is at most `Model.coronFactor qS * epsilon`. Hash-query counts affect
   the runtime budget at which hardness is required, not the multiplicative Coron factor.
   `ENNReal` means nonnegative extended reals. This is a programmable-random-oracle result
   with arithmetic-machine costs, not a standard-model or bit-complexity theorem.

The image omits the surrounding section's typeclass assumptions and the proof body;
the [source file](../Signatures/BLS/ArithmeticStatement.lean) contains the full context.

### The machine and local time

The **machine** is a small abstract computer defined in Lean, not the computer running
Lean. Its [programming language](../Signatures/Runtime/Program.lean) has variables,
branches, bounded loops, and oracle requests; its
[arithmetic instructions](../Signatures/Runtime/Arithmetic.lean) include field and group
operations and comparisons. The interpreter records both the result and its cost,
charging for control flow and data handling as well as the priced primitive operations.

**`localTime` is a worst-case bound on the adversary's own work in that model.** It
excludes the cost of servicing randomness, hash, and signing requests, but includes
preparing their arguments and processing their replies. For example, 100 local cost
units before a hash request and 50 afterward use 150 local units; the hash handler's
work is charged separately. `cert` must establish the bound on every allowed execution
path, not just on average. Formally, [SourceBudget](../Signatures/Runtime/SourceBudget.lean)
isolates local work by setting all request-service prices to zero. The reduction's
total bound then adds query-service costs and setup, cache, and extraction overhead.

A computational model is needed to prove runtime bounds, but this particular machine
is our formalization choice, not a requirement for the probability-only reduction.
The [BLS paper, page 3](https://www.cs.utexas.edu/~hovav/dist/sigs.pdf#page=3) explicitly
measures time in a fixed computational model, suggesting a probabilistic oracle Turing
machine. Our costs are arithmetic-machine units, not seconds or automatically Turing
machine steps; relating them to bit-level runtime would require a separate proof.

## Read the proof

1. Read the selected statement above and its source game before reading proof tactics.
2. Distinguish [generic indexed interaction](https://github.com/zksecurity/agm-lean/blob/c207f29d1bba8b36fd6c09a0a3a6b4e82148b402/AlgebraicGroupModel/Interaction.lean)
   from [the signature-specific interface](../Signatures/Model/SignatureInterface.lean). The generic
   layer accepts arbitrary oracles; only the signature layer mandates base/signing channels.
   Check adaptive continuations, the shared cache, exact reply transcripts, and materialization
   before final verification lookups. The [interactive adapter](../Signatures/Model/SignatureInteraction.lean)
   certifies every outgoing message; `Adversary.toInteractive_run` and `experiment_eq` relate actual
   execution to the grouped-transcript proof view. `materialize_eq_weightedReplies` checks its algebra.
3. Check [the lazy-to-private-table bridge](../Signatures/LinearFunctional/Proofs/LazyAGM.lean).
   Distribution equality and transcript correspondence are proved, not assumptions.
4. Follow [both adaptive DLog branches](../Signatures/LinearFunctional/Proofs/Adaptive.lean).
   The zero-denominator branch is essential; its remaining independent-slope collision costs `1/|F|`.
5. Check scheme-specific nondegeneracy:
   [BLS freshness](../Signatures/BLS/Proofs/Nondegeneracy.lean),
   [OOPS Vandermonde](../Signatures/OOPS/Proofs/SignatureHandle.lean), and
   [Proximity's conditional extraction](../Signatures/Proximity/Proofs/Adaptive.lean).
6. For co-CDH, inspect [lazy cache coupling](../Signatures/BLS/CoCDH/Proofs/LazyCoin.lean),
   [Coron counting and extraction](../Signatures/BLS/CoCDH/Proofs/Coron.lean), and
   [signing-call accounting](../Signatures/BLS/CoCDH/Proofs/QueryBound.lean).

The former public-table source variants are removed, not relabeled as lazy.
Private tables remain proof/simulator machinery and are never supplied to the source adversary.

## Assumptions and limits

- Scalar multiplication by `g1` is surjective and `pairing(g1,g2) != 0`.
  These imply generator bijectivity and the scalar injectivity needed for extraction.
- `SampleableType F` already implies a finite, nonempty scalar field.
  `Nat.card F` denotes the same cardinality as the proof's internal `Fintype.card F`.
- The DLog challenge supplies both `alpha*g1` and `alpha*g2`. See the
  [hardness experiments](../Signatures/Model/CoCDH.lean).
- The lazy source definitions allow infinite base-index types; the current reductions and bounds do not.
- No standard-model OOPS theorem, concrete-hash instantiation, unrestricted Proximity theorem,
  PPT preservation, or equivalence to ArkLib's experimental runner is established here.
- Retiring the old public-table schemes also retires their three completeness checks.
  This guide does not present those as completeness theorems for the lazy games.

## Verification evidence

```sh
lake build Signatures SignaturesTest
```

The generic AGM library is the pinned, public `zksecurity/agm-lean` dependency.
Its standalone tests run with
`lake build AlgebraicGroupModel AGMTest` in that repository. Token/output utilities and
signature integration tests live here; the library has one indexed interaction module.

The [four public axiom guards](../SignaturesTest/Upstream.lean) require exactly
`[propext, Classical.choice, Quot.sound]`. The
[signature guards](../SignaturesTest/StatementAssumptions.lean) check simplified premises
and reject the removed public-table interface.
The [hardness boundary tests](../SignaturesTest/Hardness.lean) distinguish query counts from
runtime bounds and check the unchanged games. The signature guards reject removed weaker
endpoints, check all four machine statements' exact axiom footprints and source-certificate
premises, and test applications using only their explicit arguments.

- [Cache reuse and visible tokens](../SignaturesTest/LazyAGM.lean).
- [Signature token representations](../SignaturesTest/AlgebraicRepresentation.lean) and
  [exact signature-adapter preservation](../SignaturesTest/AlgebraicSignatureAdapter.lean): actual
  certified execution, interleaved/repeated replies, chronological vectors, malformed replies,
  tracked public keys, malformed initial lists, and distinct signature/verification group types.
- [Interactive algebraicity](https://github.com/zksecurity/agm-lean/blob/c207f29d1bba8b36fd6c09a0a3a6b4e82148b402/AGMTest/Interaction.lean): adaptive group arguments,
  exact-length witnesses, fresh replies without explanations, and no use of future inputs.
- [Multi-group interaction](https://github.com/zksecurity/agm-lean/blob/c207f29d1bba8b36fd6c09a0a3a6b4e82148b402/AGMTest/MultiGroup.lean):
  one adaptive stream with separate group bases, cross-sort dependencies, and rejection
  of explanations from the wrong sort. The signature games use the same indexed interface
  with separate `signature` and `verification` sorts. Their public keys are tracked inputs;
  their source adversaries still output only signature-group representations. The security
  statements gain no new assumptions.
- [Whole-library axiom guard](https://github.com/zksecurity/agm-lean/blob/c207f29d1bba8b36fd6c09a0a3a6b4e82148b402/AGMTest/Axioms.lean)
  for all declarations in the generic AGM namespace.
- [Signature execution bridge](../Signatures/Model/SignatureInteraction.lean): `compile_algebraic`
  certifies all paths and `Adversary.toInteractive_run` proves exact equality with the proof-side
  runner. The [source experiment](../Signatures/Model/LazyAGM.lean) calls `interactiveRun`;
  `experiment_eq` preserves the complete winning computation for all three AGM schemes.
- [Reply-dependent queries and stopping](../SignaturesTest/AdaptiveQueries.lean).
- [Freshness, topic counting, and collision probabilities](../SignaturesTest/GameBoundaries.lean).
- [Coron signing budgets](../SignaturesTest/CoronBudget.lean).
- [Adaptive denominator and collision boundaries](../SignaturesTest/AdaptiveDenominator.lean).

These are checked source assertions, not a live CI badge. A reviewer should record the revision
and build evidence. Existing probability-API deprecation warnings and an upstream experimental
runner's admission are outside the four public axiom footprints.

## Review checklist

- [ ] Record the commit, endpoint, paper version, and claimed model.
- [ ] Match the adversary interface and winning event to the intended claim.
- [ ] Check adaptive queries, stopping, targets, and coefficients.
- [ ] Check shared-cache behavior and exact token/freshness accounting.
- [ ] Account for both DLog branches and the collision term.
- [ ] Check the OOPS degree rule or Proximity fresh-collision event and probability bridge.
- [ ] Confirm finite-domain, random-oracle, and computational-cost limits.
- [ ] For generic hardness, check all named solver certificates; for concrete-machine hardness,
  check the source certificate and the derived target budgets (both branches for AGM).
- [ ] Record a reproduced build and the public axiom footprints.
- [ ] Link findings to source lines and the corresponding paper statements.

Use the [review issue template](../.github/ISSUE_TEMPLATE/security-review.md) to keep the
checklist, evidence, and discussion in GitHub rather than local browser storage.
