import Signatures.Runtime.Caliper.CoCDH
import Signatures.Runtime.Caliper.Family

/-! Nonuniform co-CDH hardness for polynomial-resource Caliper families.
The word widths, layouts and ideal sampling ports are fixed before the solver.
Every sampled challenge is represented. CPU adequacy remains separate. -/
namespace Signatures.Runtime.CaliperBackend
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat → Nat} {F G K : Nat → Type}
    [∀ n, Field (F n)] [∀ n, SampleableType (F n)]
    [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
    [∀ n, AddCommGroup (K n)] [∀ n, Module (F n) (K n)]
    (port : ∀ n, Interactive.Port (w n) unifSpec)
    (input : ∀ n, Layout (w n) (K n × (G n × (G n × G n))))
    (output : ∀ n, Layout (w n) (G n)) (generator : ∀ n, G n) (keyGenerator : ∀ n, K n)

def coCDHNonuniformWithin (solver : ∀ n, BLS.CoCDH.CoCDHAdversary (F n) (G n) (K n)) : Prop :=
  (∀ n (scalar : F n) (point : G n), (input n).valid (scalar • keyGenerator n, generator n, scalar • generator n, point)) ∧
  Interactive.NonuniformWithin port input output
    (fun n value => solver n value.val.2.1 (keyGenerator n) value.val.2.2.1 value.val.1 value.val.2.2.2)

omit [∀ n, SampleableType (F n)] in
theorem coCDHNonuniformWithin.of_pointwise
    (solver : ∀ n, BLS.CoCDH.CoCDHAdversary (F n) (G n) (K n))
    (words memory time : Nat → Nat)
    (width : PolynomiallyBounded w) (stored : PolynomiallyBounded words)
    (space : PolynomiallyBounded memory) (elapsed : PolynomiallyBounded time)
    (implemented : ∀ n, coCDHWithin (F := F n) (port n) (input n) (output n) (generator n) (keyGenerator n)
      (words n) (memory n) (time n) (solver n)) :
    coCDHNonuniformWithin (F := F) port input output generator keyGenerator solver :=
  ⟨fun n => (implemented n).1, width, words, memory, time, stored, space, elapsed,
    fun n => (implemented n).2⟩

/-- Hardness against every polynomial-code, polynomial-memory, polynomial-time
nonuniform solver family in this fixed Caliper model. -/
def coCDHNonuniformHardness [∀ n, SampleableType (G n)] : Prop :=
  ∀ solver, coCDHNonuniformWithin (F := F) port input output generator keyGenerator solver →
    negligible (fun n => Model.coCDHAdvantage (F := F n) (generator n) (keyGenerator n) (solver n))

end Signatures.Runtime.CaliperBackend
