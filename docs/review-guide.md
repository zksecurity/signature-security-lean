# Signature security review

Lazy random-oracle security for BLS, OOPS, Proximity, and Schnorr, including
both Schnorr nonce conventions and its separate AGM route.

Start with the mathematical game and the public statement:

| Scheme | Game, independent of the execution model | Security statement |
| --- | --- | --- |
| BLS | [Game.lean](../Signatures/BLS/Game.lean) | [Statement.lean](../Signatures/BLS/Statement.lean) |
| Schnorr | [Game.lean](../Signatures/Schnorr/Game.lean) | [Statement.lean](../Signatures/Schnorr/Statement.lean) |
| OOPS | [Game.lean](../Signatures/OOPS/Game.lean) | [Statement.lean](../Signatures/OOPS/Statement.lean) |
| Proximity | [Game.lean](../Signatures/Proximity/Game.lean) | [Statement.lean](../Signatures/Proximity/Statement.lean) |

The common EUF-CMA game is:

```text
Generate a secret key and give its public key to the attacker.
Answer adaptive hash and signing queries using one shared random oracle.
Receive the attacker's proposed message and signature.
Accept exactly when the signature verifies and the message was never signed.
```

OOPS additionally limits distinct signed scalar messages on the forged topic to
its degree. Proximity uses the full vector/slot pair for freshness and measures
its collision event separately. Schnorr keeps full-field and nonzero signing
nonces as distinct variants. AGM routes require algebraic group explanations;
BLS co-CDH and Schnorr ROM do not. Internal computation is unrestricted within
the declared resource class.

Pairing is shared mathematical data: [`BilinearGroup.pairing`](../Signatures/Model/BilinearGroup.lean)
and its bilinearity laws are independent of the AGM restriction. Both the BLS co-CDH
and AGM games use this interface; nondegeneracy at the chosen generators is supplied
separately by [`PairingCurve`](../Signatures/Model/PairingCurve.lean).

Fix the curve, security parameter, query allowances and execution model once.
The main BLS AGM theorem then reads:

```lean
theorem agm_security
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    𝒟[EUFCMA adversary] {true} ≤ 2 * εDL + 1 / p :=
  Proofs.agm_security_common_budget curve securityParameter queries adversary
```

Here `p` is the group order. `εDL` is the DLog success bound at the **derived
complete reduction budget**, in the same execution model as the attacker.
For pairing-based AGM routes this is `(1,1)`-DLog; for Schnorr it is ordinary
DLog. The short names are local notation: Lean still sees the original game,
hardness supremum and derived time bound. No hypothesis or loss is removed.

Writing `h` and `s` for hash and signing allowances, the concrete bounds are:

| Route | Forgery probability at most |
| --- | --- |
| BLS AGM, OOPS AGM | `2 εDL + 1/p` |
| BLS co-CDH ROM | `coronFactor(s) εcoCDH` |
| Schnorr AGM | `εDL + (h+1)/p + s(s+h)/p` |
| Schnorr ROM, full-field nonces | `s(s+h)/p + (h+1)/p + sqrt((h+1) εDL)` |
| Schnorr ROM, nonzero nonces | `s(s+h)/(p−1) + (h+1)/p + sqrt((h+1) εDL)` |
| Proximity AGM | `2 εDL + 1/p + Pr[fresh collision]` |

Each hardness quantity uses its own route's proved budget. It becomes a useful
numerical bound under the corresponding hardness assumption. The Coron factor
is `((s+1)⁻¹ (s/(s+1))^s)⁻¹`, including factor one at `s = 0`.
The separate-budget AGM refinements remain available below the main theorems.

The asymptotic reading is: under the relevant nonuniform hardness and parameter
growth assumptions, polynomial-resource attacker families have negligible forgery
probability. Proximity gives collision probability plus negligible error, and
requires negligible collisions for negligible forgery. These family results
retain one fixed execution model and account for polynomial stored code/advice;
see the [completed plan and family endpoints](GENERAL-ADVERSARY-REDUCTION-PLAN.md).

Only the supporting layer needs execution contracts, primitive and encoding
costs, sampler profiles, native solver certificates, and the expanded resource
formulas. They remain inspectable in each `General*SecurityModel.lean` and
`General*Parameters.lean`; proof bodies stay in `Proofs/`. The mathematical games
import no runtime modules. The future Caliper/conventional-machine instantiation
is separate from this public presentation.

For a deeper Schnorr review, follow [the game, rewinding, and cost review](SCHNORR.md).
Its separately scoped [bit-machine endpoint](../Signatures/Schnorr/BitStatement.lean)
and [implementation evidence](BIT-COMPLEXITY.md) retain their sampling-error and
static code/data conventions. Kernel checking proves each implication from its
hypotheses; it does not establish paper/model alignment.

[Game ledger](SECURITY-GAMES.md) · [Source tree](../Signatures) ·
[Regression tests](../SignaturesTest) ·
[Start a review issue](https://github.com/zksecurity/signature-security-lean/issues/new?template=security-review.md)

This guide is plain GitHub Markdown: no JavaScript, browser storage, or separate site is required.
Record the commit under review and findings in an issue or pull-request review. The task list
below is a review template, not a claim that a paper audit has been completed.

## Game and oracle definitions

The BLS, OOPS, and Proximity AGM games share a readable oracle interface:

1. [Named requests and state](../Signatures/Model/AlgebraicOracle.lean): `Request.random`,
   `Request.hash`, and `Request.sign` dispatch the three operations. The `State` record has
   `hashReplies` and `signingReplies` fields. Only replies actually delivered to the attacker
   enter these lists, including repeated requests.
2. [Attacker execution](../Signatures/Model/AlgebraicOracle.lean): `run` evaluates the attacker's
   algebraic explanation over its received points. Its `Result` names the candidate `message`,
   `signature`, `signedMessages`, and `signingCoefficients`. `hashMessage` and `sign` implement
   the scheme's finite weighted base sum and secret-key multiplication.
3. [Shared random oracle](../Signatures/Model/RandomOracle.lean): `RandomOracle.run` supplies
   one initially empty lazy oracle for the complete experiment. The public `Game.lean` files
   show key generation, attacker execution, final hashing, the verification equation, and
   freshness. OOPS also shows its distinct-message condition; Proximity exposes its collision
   event separately.
4. [Exact correspondence](../Signatures/Model/Proofs/AlgebraicOracle.lean): the record state
   preserves the original grouped transcript and the complete source game. The existing
   [certified interaction bridge](../Signatures/Model/SignatureInteraction.lean) connects that
   transcript to the generic AGM execution. These are proved equalities for adaptive attackers.

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

The **non-AGM BLS game** uses the scheme-level
[ordinary ROM interface](../Signatures/BLS/Spec/ROM.lean): `BLS.ROM.oracle` handles
the named requests `Request.random`, `Request.hash`, and `Request.sign`.
Its `State` structure has `hashExponents` and `signedMessages` fields; `hashScalar`
maintains the private lazy hash-exponent cache. In
[`BLS.Game.rom`](../Signatures/BLS/Game.lean), the attacker returns a message and signature,
then the verifier explicitly calls `ROM.hash message` and checks the pairing equation.
This query is needed even when the attacker never hashed its proposed message.
`simulateQ` uses the same handler for the attacker and verification, and `.run` supplies
`State.empty`. The public game reads no cached exponent and uses no cache wrapper.
This adversary returns a raw candidate signature without an algebraic explanation.
An [exact state-encoding proof](../Signatures/BLS/Proofs/ROM.lean) connects this readable
handler to the tuple representation used internally by the co-CDH reduction proofs.

The [Schnorr interfaces](../Signatures/Schnorr/Spec/Oracle.lean) use named requests and
results with `message`, `commitment`, and `response` fields. The ordinary interface retains
the signing log; the AGM interface also retains the signed-message state and malformed-request
flag. Both ROM nonce conventions and the AGM game display the equation
`response • generator = commitment + challenge • publicKey` in
[`Schnorr.Game`](../Signatures/Schnorr/Game.lean). Their
[exact game equalities](../Signatures/Schnorr/Proofs/Game.lean) preserve the existing source games.

## Results

The short BLS statements are [`BLS.agm_security` and `BLS.cocdh_security`](../Signatures/BLS/Statement.lean).
Their model and adversary definitions expose the distinct execution and resource assumptions.
The short [OOPS](../Signatures/OOPS/Statement.lean) and
[Proximity](../Signatures/Proximity/Statement.lean) statements additionally take
the degree or dimension. They preserve their original source games and derive
both native reduction budgets from general caller resources. Their mathematical
games are in `Game.lean`; execution contracts and hardness budgets are in
`GeneralSecurityModel.lean`; their proof bodies are in
`Proofs/GeneralSecurity.lean`.
The [OOPS](../Signatures/OOPS/GeneralAGMFamilyStatement.lean) and
[Proximity](../Signatures/Proximity/GeneralAGMFamilyStatement.lean) family statements
derive polynomial solver time/code under one fixed backend and polynomial
component/degree/dimension bounds. Proximity's collision-relative statement
does not assume negligible collisions; its negligible-forgery corollary does.
The eager-table AGM wrappers are retired. The [migration guide](API-MIGRATION.md)
explains the replacement models and hardness classes. Original eager probability
and runtime lemmas remain supporting references. Arithmetic-source BLS co-CDH and
Schnorr endpoints retain their distinct implementation scopes.

### BLS: lazy ROM to co-CDH

- [Statement](../Signatures/BLS/ArithmeticStatement.lean): `BLS.Statement.bls_eufcma_of_cocdh_machine_hardness`.
- [Source game](../Signatures/BLS/CoCDH/Spec/LazyGame.lean): `blsEufLazyPK`.
- [Coron reduction](../Signatures/BLS/CoCDH/Spec/Coron.lean) and
  [query-budget proof](../Signatures/BLS/CoCDH/Proofs/QueryBound.lean).
- Bound: `Adv_ROM <= coronFactor(qS) * epsilon`, assuming co-CDH hardness at the derived solver budget.
- Arbitrary message types. The budget counts all signing calls,
  including repeats, on every generated key. The source certificate additionally bounds all
  hash (`queries 1`), random (`queries 0`), and signing (`queries 2`) calls and local computation.

### BLS: query-only lazy AGM

- [Statement](../Signatures/BLS/Statement.lean): `BLS.agm_security_two_budgets`.
- [Source game](../Signatures/BLS/Spec/LazyAGM.lean) and [proof](../Signatures/BLS/Proofs/LazyAGM.lean).
- Bound: `Adv_source <= goodEpsilon + badEpsilon + 1/|F|`, with hardness at each derived solver budget.
- Arbitrary message types; measured all-path execution, encoding and coefficient-size bounds.
  Only explicit base and signing replies supply representation tokens.
- Freshness proves a nonzero symbolic coefficient. Unlike Proximity, the corresponding
  fresh symbolic-collision event has probability zero, with no noncollision assumption.
  Evaluation can still give zero; the independent hidden-slope collision costs `1/|F|`.

### OOPS: query-only lazy AGM

- [General-caller statement](../Signatures/OOPS/Statement.lean): `OOPS.agm_security`, with arbitrary topics and complete lazy solver budgets.
- [Source game and degree rule](../Signatures/OOPS/Spec/LazyAGM.lean) and
  [proof](../Signatures/OOPS/Proofs/LazyAGM.lean).
- Same two-reduction bound and oracle-derived topic bases. The retired eager implementation required a finite topic type.
- At most `d` distinct signed scalar messages on the eventual forgery topic. Repetitions and
  other topics do not consume this cap. Freshness concerns the entire message/topic pair.
- Freshness and this winning degree rule imply a nonzero symbolic coefficient by Vandermonde.
  Symbolic collisions within the winning rule have probability zero, not an assumed small bound.
  Neither this fact nor BLS's rules out sampled hash collisions; both retain the independent
  hidden-slope collision bound `1/|F|`, not a bound on every collision in the hash transcript.

### Proximity: query-only lazy AGM, with collisions

- [General-caller statement](../Signatures/Proximity/Statement.lean): `Proximity.agm_security`, with arbitrary slots and complete lazy solver budgets.
- [Source game and collision event](../Signatures/Proximity/Spec/LazyAGM.lean) and
  [proof](../Signatures/Proximity/Proofs/LazyAGM.lean).
- Bound: `Adv_source <= goodEpsilon + badEpsilon + 1/|F| + Pr[fresh collision]`.
  Oracle-derived coordinate bases; the retired eager implementation required a finite slot type.
- `Collision out signed` means the full vector/slot output is fresh and its vector equals
  the sum of signed vectors weighted by the output's signing coefficients. Repeats and other
  slots contribute; missing coefficients are zero. Signature validity is not required by this event.
- `collisionGame` measures that event under the original key sampling and lazy adaptive oracles.
  The proof establishes equality with an observer of certified execution, then lazy/table equality.
  There is no all-path noncollision premise and no change to the forgery winning check.
  No small upper bound on this extra probability is proved; it can be one.

## Conditional hardness bounds

Public endpoints bound forgery using resource-indexed DLog/co-CDH success
suprema. Their supporting theorems apply [`Model.HardWithin`](../Signatures/Model/Hardness.lean)
to actual solver witnesses constructed from the original contracts and attacker
resources. AGM retains both reduction branches and `1/|F|`; Proximity additionally
retains collision probability. Co-CDH preserves the Coron factor.

**Concrete operation bounds now cover all four routes**, including both AGM branches; see
[`OperationBounds.lean`](../Signatures/OperationBounds.lean). Erasing the ledgers gives the
original solvers. Review the `qH`/`qS`, coefficient-size, finite-domain, and weight-cost factors.
**The arithmetic-source BLS co-CDH endpoint** in [BLS/ArithmeticStatement.lean](../Signatures/BLS/ArithmeticStatement.lean) uses
the [Coron source certificate](../Signatures/Runtime/CoronCertificate.lean).
Review its source certificate, all-key trace equality,
adaptive source budget, and charged fixed data. The compiler proves the exact named solver's
budget; no `hbudget` premise is required. Primitive operation/sampling prices are explicit
contracts, not bit-runtime proofs.

**The eager AGM resource lemmas** remain in the
[good package](../Signatures/Runtime/AGMGoodMachine.lean) and
[bad package](../Signatures/Runtime/AGMBadMachine.lean). They charge full-domain
tables, canonical-enumeration loading, simulation and extraction. These are
reference implementations with explicit domain-size costs; their superseded
public security wrappers have been removed. The current public AGM statements
use lazy general-caller reductions with derived runtime and stored-code budgets.
Read the [runtime audit](COMPUTATIONAL-SECURITY.md) for their conditional backend scope.

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
  runner. The [original source experiment](../Signatures/Model/LazyAGM.lean) calls `interactiveRun`;
  `experiment_eq` preserves its complete winning computation. The readable record-state games
  are connected to that experiment by
  [`AlgebraicOracle.game_eq`](../Signatures/Model/Proofs/AlgebraicOracle.lean).
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
