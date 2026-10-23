# Security API migration

The BLS, OOPS and Proximity AGM games now take the shared
`AlgebraicGroupModel.Interaction.Adversary` directly, specialized by
[`Model.DirectAGM.Adversary`](../Signatures/Model/DirectAGM.lean). The same type is
the `source` field of their general concrete and family attacker records.
Supply actual outgoing group points with exact chronological explanation vectors;
the shared certificate covers every input and reply path. Hash/signing requests
have no group arguments, and a final forgery has one signature-group point and no
verification-group points. The game rejects malformed protocol shapes.

Callers no longer supply the old `β/γ/ξ` attacker or call `toInteractive`. The
proof derives that coefficient view internally for every shared attacker. Backend
realizations implement its encoded program and charge producing the encoding,
including regrouping, in the caller budget. Query allowances refer to the native
source requests' `value.data`. See the [direct attacker regression](../SignaturesTest/DirectSharedAGM.lean)
and [preservation proofs](../Signatures/Model/Proofs/DirectAGM.lean).

The public security statements now use general implemented attackers and lazy
reductions with proved runtime and stored-code bounds. The three eager-table AGM
security wrappers and BLS's `ArithmeticAttackerCertificate` alias are retired.

| Retired declaration | Public replacement |
| --- | --- |
| `BLS.Statement.bls_lazy_agm_of_dlog_machine_hardness` | [`BLS.agm_security`](../Signatures/BLS/Statement.lean) (two separate DLog budgets: `BLS.Proofs.agm_security`) |
| `OOPS.Statement.oops_lazy_agm_of_dlog_machine_hardness` | [`OOPS.agm_security`](../Signatures/OOPS/Statement.lean) (two separate DLog budgets: `OOPS.Proofs.agm_security`) |
| `Proximity.Statement.proximity_lazy_agm_of_dlog_machine_hardness` | [`Proximity.agm_security`](../Signatures/Proximity/Statement.lean) (two separate DLog budgets: `Proximity.Proofs.agm_security`) |

The replacement is not a textual rename. Choose a curve and an execution model
with the original primitive, sampler and encoding contracts, then provide the
attacker's implementation, measured execution resources, code/advice bound and
query allowances. The reduction's complete resource certificate is derived.
The hardness supremum ranges over solvers in that same fixed backend at the
derived input/code/time budgets. An old arithmetic-only hardness hypothesis does
not automatically establish hardness against this broader implementation class.

The main theorem takes the curve, security parameter, query allowances and
algebraic adversary; OOPS adds degree and Proximity adds dimension. Each scheme's
`Proofs.agm_security` keeps separate success bounds for the two reduction runtimes.
OOPS retains its target-topic admissibility rule. Proximity
retains the actual collision probability; it is not silently assumed negligible.

Original eager probability definitions and resource lemmas remain as supporting
references and for exact lazy/eager correspondence. Their costs still charge the
full finite domain; they are not the current efficient implementation. Their
source/compiler regressions remain. The OOPS and Proximity `ArithmeticStatement`
module paths now import their current statements without restoring retired names.

The arithmetic-source BLS co-CDH theorem remains in
[`BLS/ArithmeticStatement.lean`](../Signatures/BLS/ArithmeticStatement.lean), and
Schnorr's arithmetic and bit endpoints retain their separately stated scopes.
General unrestricted attackers use `BLS.cocdh_security`, `Schnorr.rom_security`,
or `Schnorr.NonzeroNonce.rom_security`; Schnorr AGM uses `Schnorr.agm_security`.

All general routes also have nonuniform family results derived from polynomial
original resources in one fixed backend. A conventional-machine instantiation
is a separate claim. See the [current plan](GENERAL-ADVERSARY-REDUCTION-PLAN.md)
and [computational-security scope](COMPUTATIONAL-SECURITY.md).
