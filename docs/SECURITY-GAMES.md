# Current security games

Five supported security endpoints, all with lazy random-oracle source games.
Each bound names explicit reduction algorithms. Their axiom footprints are exactly
`[propext, Classical.choice, Quot.sound]`.

Start with the [GitHub review guide](review-guide.md).

The [paper-facing OOPS corollary](review-guide.md#paper-facing-statements) uses a
fixed-degree signing-call limit. BLS intentionally retains the type-3 co-CDH formulation
with an explicit co-hint and no G2-to-G1 map. The core games and runtime endpoints are unchanged.

The legacy machine statements use source-code certificates to derive solver
budgets. The general BLS co-CDH and AGM statements instead accept general
backend-realized callers and derive the complete native solver budgets.
Hardness always ranges over the specified implementation/resource class.
The numerical bounds are `coronFactor(qS) * epsilon` for co-CDH and
`goodEpsilon + badEpsilon + 1/|F|` for AGM, plus the fresh-collision probability for Proximity.
Both AGM solver budgets are derived, not assumed.
See the [computational-security audit](COMPUTATIONAL-SECURITY.md).

## Entry points

| Route | Statement | Source |
| --- | --- | --- |
| BLS to co-CDH | [`bls_eufcma_of_cocdh_machine_hardness`](../Signatures/BLS/Statement.lean) | [`blsEufLazyPK`](../Signatures/BLS/CoCDH/Spec/LazyGame.lean) |
| BLS lazy AGM | [`bls_lazy_agm_of_dlog_machine_hardness`](../Signatures/BLS/Statement.lean) | [BLS game](../Signatures/BLS/Spec/LazyAGM.lean) |
| BLS AGM, general caller | [`BLS.security`](../Signatures/BLS/Security.lean) | Curve, security parameter, query allowances, algebraic adversary; same lazy game and complete solver budgets, arbitrary messages |
| BLS co-CDH, general caller | [`Coron.NativeSolver.security_of_resources`](../Signatures/Runtime/BackendCoronSecurity.lean) | Same lazy game; complete native solver budget, arbitrary messages |
| OOPS lazy AGM | [`oops_lazy_agm_of_dlog_machine_hardness`](../Signatures/OOPS/Statement.lean) | [OOPS game](../Signatures/OOPS/Spec/LazyAGM.lean) |
| Proximity lazy AGM | [`proximity_lazy_agm_of_dlog_machine_hardness`](../Signatures/Proximity/Statement.lean) | [Proximity game](../Signatures/Proximity/Spec/LazyAGM.lean) |
| Schnorr ROM | [`schnorr_eufcma_of_dlog_machine_hardness`](../Signatures/Schnorr/Statement.lean) | [Schnorr game](../Signatures/Schnorr/Spec/ROM.lean) |
| Schnorr ROM, bit heap | [`schnorr_eufcma_of_dlog_bit_hardness`](../Signatures/Schnorr/BitStatement.lean) | Same game, compiled solver with explicit accumulated sampling error |

Schnorr uses no algebraicity restriction. Its programmable-ROM reduction simulates
signatures, then replays a recorded prefix with a new challenge. The theorem bounds
`delta * (delta/(qH+1) - 1/|F|)` by budget-bounded DLog hardness, where
`delta = Adv - qS*(qS+qH)/|F|` uses truncated subtraction. Both full runs are charged;
see [Schnorr's game and runtime review](SCHNORR.md).

The old public-table schemes, adversary interface, security wrappers, and source-game bridges
are removed. This is an interface retirement, not an assertion that public-table and query-only
adversaries were the same model.

## BLS to co-CDH

The adversary receives the verification key and adaptively queries private randomness, hashes,
and signatures. Hashes are sampled and cached on demand, including the final verification hash.
A winning forgery verifies and its message has never been signed.

`IsQueryBoundP` counts signing calls, including repeats, for every generated key `x*g2`;
the source certificate additionally supplies all-path hash/sign/random budgets and local work.
In particular, `queries 1` is the hash-query bound `qH`.
The signing-call bound's implication for the distinct-message count
is proved. Both the reduction's scalar cache and its Coron-coin cache are lazy.

The message type may be infinite. The probability proof restricts the attacker's
adaptive tree to a finite proof domain and transports the original lazy game and
solver exactly. That cover includes final forgeries and all generated public keys;
it is never enumerated by the executable reduction.

The bound is `Adv_ROM <= C(qS) * epsilon`, assuming co-CDH hardness up to the derived
`cert.targetBudget`. The loss is
`C(qS) = ((qS+1)^(-1) * (qS/(qS+1))^qS)^(-1)` in nonnegative extended reals.
For `qS = 0`, the factor is one. This is programmable-ROM security, not standard-model security.

## Algebraic interaction

[Interaction.lean](https://github.com/zksecurity/agm-lean/blob/c207f29d1bba8b36fd6c09a0a3a6b4e82148b402/AlgebraicGroupModel/Interaction.lean)
is the sole generic adversary interface. It supports an indexed family of group types:
one adaptive program, with a separate chronological input list and same-sort explanations
for each group. One-group protocols use `Tag := Unit`, not a separate implementation.

`Message` separates ordinary data and group elements; `Explained` pairs each outgoing
element with a vector over its sort's received inputs. `IsAlgebraic` requires exact lengths
and reconstruction on every reply path, checking requests before their replies arrive.
`Adversary` bundles this proof; its runner starts from the actual input and proves final
representation validity. `Adversary.run` is the only execution API; there is no separate
raw runner. The interpreter is not a runtime validator.

Replies need **no** explanations. Only received group elements extend the input lists;
outgoing elements do not. Games must supply generators explicitly and must not conceal
unlisted group inputs in ordinary data or advice. The generic layer establishes neither
efficiency nor pairing-product representations in a target group. It prescribes no hash,
signing, pairing, or sampling interface.

The BLS, OOPS, and Proximity AGM games execute through this runner with separate `signature`
and `verification` sorts. [SignatureInteraction.lean](../Signatures/Model/SignatureInteraction.lean)
puts the signature-group generator and verification-group public key in their respective
input lists; the initial ordinary payload is `Unit`. The compiler reads the key from its
tracked list and rejects malformed initial lists. Requests have no group arguments;
hash/signing replies each add one signature-group input, and private randomness adds none.
Final vectors follow chronological reply order, even when hash and signing queries interleave.
The compiler rejects replies with the wrong number of signature-group inputs. It tracks,
but does not use, any verification-group inputs supplied on hypothetical reply paths.

Messages, query labels, and sampled numbers remain ordinary data. The winning experiment
reads the candidate signature from `groups .signature`, never from an unchecked group value
in `data`. The source adversaries still output only signature-group representations; tracking
the key does not claim security against a broader interface with verification-group outputs.
Games instantiating arbitrary message or query types must still ensure those ordinary
payloads do not introduce hidden group inputs.

The signature-side `Output.explain` adapter supplies exact-length vectors.
`Adversary.toInteractive_run` proves equality with the grouped-transcript runner;
`experiment_eq` transfers it to the complete winning experiment. Those equivalence proofs
remain here; optional generic `erase`/`run_erase` helpers were removed from the library.
The separate runtime-erasure proofs used by the concrete cost certificates are unchanged.
Security statements, named reductions, and machine certificates are unchanged; no cost theorem
for the generic interpreter is claimed. The non-AGM BLS co-CDH game is unaffected.

The minimal generic interface and its tests live in the pinned, public
`agm-lean` dependency. Token/output utilities and signature adapters live here.

## Query-only lazy AGM

[Token-indexed outputs](../Signatures/AlgebraicGroupModel/Spec/Representation.lean)
define coefficients, their evaluation on a finite list of supplied inputs, and output
materialization. These signature-adapter utilities import no oracle computations and are
not part of the generic AGM library. The enclosing game chooses the available inputs;
the utilities do not implement a group-operation machine or certify coefficient costs.

[SignatureInterface.lean](../Signatures/Model/SignatureInterface.lean) defines the signature adversary;
[Model/LazyAGM.lean](../Signatures/Model/LazyAGM.lean) defines the source experiment and named reductions.
The adversary receives only the verification key and makes adaptive
private-randomness, base, and signing queries.

`Output.toAlgebraic` and `Transcript.inputs` retain the signature interface's token-indexed output interpretation.
The generator and the two reply channels have disjoint positional tokens. `materialize` uses
the token evaluator; `materialize_eq_weightedReplies` proves exact agreement with the original
signature expression. The adapter preserves missing/extra coefficient handling and does not
change any queries, freshness conditions, security assumptions, or reduction budgets.

One persistent cache serves explicit base queries, internal signing lookups, and final
verification. Repeated queries reuse answers, including bases first initialized by signing.
Queries are continuations, not a predetermined list; replies may change later queries,
stopping, the target, and representation coefficients.

The output has coefficient lists over actual base/signature replies, indexed by query order.
Internal lookups create no visible tokens. Materialization happens before final verification
lookups. Extra coefficients are ignored; missing coefficients are zero. Freshness uses the
complete actual signing transcript.

[The lazy bridge](../Signatures/LinearFunctional/Proofs/LazyAGM.lean) proves exact probability
and transcript correspondence with a hidden-table simulator. These private finite tables are
still needed by the proof and the explicit AGM solvers; they are never given to the source
adversary. Lazy source games do not establish efficient lazy reductions.

## Bounds and premises

The BLS/OOPS AGM bound is `Adv_source <= goodEpsilon + badEpsilon + 1/|F|`, with hardness
assumed at the two derived machine budgets. Proximity adds `Pr[fresh collision]` to this bound.
The extraction proof bounds noncolliding forgeries by the two solvers' success rates and `1/|F|`.
The good reduction extracts when the denominator is nonzero; the bad reduction uses a known
signing key and independently masked affine bases for the adaptive zero-denominator branch.
The division-only bound is insufficient.

All four endpoints require surjective scalar generation by `g1` and
`pairing(g1,g2) != 0`. VCVio's uniform sampler already implies finite, nonempty scalars;
no separate `Fintype F` requirement is needed. The public collision term uses `Nat.card F`,
equal to `Fintype.card F` inside the proof.

- **BLS:** finite message indices; freshness supplies a nonzero target coefficient.
  The source certificate bounds every query kind, local computation, and coefficient-list sizes.
- **OOPS:** messages are scalar/topic pairs. The final target topic alone determines the
  degree cap: at most `d` distinct signed scalars, allowing equality with `d`.
  Repetitions and other topics do not consume this degree cap, but still count against the
  source certificate's total signing budget. Freshness concerns the full pair.
- **Proximity:** messages are vector/slot pairs. The collision term measures fresh outputs whose
  vector equals the signing-coefficient-weighted sum of all signed vectors, including repeats
  and other slots. Missing coefficients are zero. It is measured under actual key sampling and
  lazy-oracle execution, not over arbitrary replies. It includes invalid signatures and does not
  alter the original winning event. In dimension zero every fresh output is a collision.
  The theorem does not assume noncollision or prove that this extra probability is small.

BLS and OOPS need no analogous extra term: the probability of a fresh symbolic collision
is **zero** for BLS, and **zero within the winning degree rule** for OOPS. Here a symbolic
collision means all coefficients of the target weight vector minus the signing-weighted
sum vanish. BLS's fresh-message coefficient is one; OOPS's Vandermonde proof guarantees
at least one nonzero coefficient. These facts are proved, not assumptions on the adversary.
They do not assert that sampled hash values never collide. A nonzero linear expression can
still evaluate to zero; the proof bounds the relevant independent hidden-slope collision by
`1/|F|`. This is not a bound on finding any collision among all adaptive hash queries.
[Regression proofs](../SignaturesTest/GameBoundaries.lean) check these
zero probabilities for any distribution of transcripts. The BLS co-CDH endpoint likewise
has no noncollision premise; its separate Coron reduction is unchanged.

OOPS and Proximity use oracle-derived bases here, not standard-model public setup parameters.

## Limits and checks

The source definitions allow infinite base-index types; the current security bounds and
reductions require finite ones. There is no PPT cost theorem, efficient lazy AGM reduction,
concrete-hash instantiation, standard-model OOPS theorem, small Proximity bound independent of collisions,
or proof of equivalence to ArkLib's experimental adversary runner.

`lake build Signatures SignaturesTest` checks the four public axiom footprints, the adaptive
extraction core, the lazy bridge, and regressions for query counting, freshness, degree rules,
adaptive hash/sign interleaving, cache reuse, token visibility, and zero-denominator behavior.
The removed public-table schemes' completeness theorems are no longer part of this inventory.
No hardness axiom is added to Lean. Guards reject the removed weaker public wrappers.
The four machine-bounded statements have exact axiom and signature guards, including
application tests for certificate-inferred adversaries, primitive costs, and resource indices.
