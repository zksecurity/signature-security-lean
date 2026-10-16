# Security API migration

The public security statements now use general implemented attackers and lazy
reductions with proved runtime and stored-code bounds. The three eager-table AGM
security wrappers and BLS's `ArithmeticAttackerCertificate` alias are retired.

| Retired declaration | Public replacement |
| --- | --- |
| `BLS.Statement.bls_lazy_agm_of_dlog_machine_hardness` | [`BLS.agm_security`](../Signatures/BLS/Statement.lean), or `BLS.agm_security_two_budgets` |
| `OOPS.Statement.oops_lazy_agm_of_dlog_machine_hardness` | [`OOPS.agm_security`](../Signatures/OOPS/Statement.lean), or `OOPS.agm_security_two_budgets` |
| `Proximity.Statement.proximity_lazy_agm_of_dlog_machine_hardness` | [`Proximity.agm_security`](../Signatures/Proximity/Statement.lean), or `Proximity.agm_security_two_budgets` |

The replacement is not a textual rename. Choose a curve and an execution model
with the original primitive, sampler and encoding contracts, then provide the
attacker's implementation, measured execution resources, code/advice bound and
query allowances. The reduction's complete resource certificate is derived.
The hardness supremum ranges over solvers in that same fixed backend at the
derived input/code/time budgets. An old arithmetic-only hardness hypothesis does
not automatically establish hardness against this broader implementation class.

The main theorem takes the curve, security parameter, query allowances and
algebraic adversary; OOPS adds degree and Proximity adds dimension. The sharper
`agm_security_two_budgets` statements keep separate success bounds for the two
reduction runtimes. OOPS retains its target-topic admissibility rule. Proximity
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
