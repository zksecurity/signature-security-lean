import Signatures.Runtime.Caliper.DLog
import Signatures.Runtime.Caliper.Family

/-! Nonuniform DLog hardness for polynomial-resource Caliper programs. This
fixes the entire word-width, port and layout family before quantifying over
solvers. Every sampled challenge must be represented. Sampling is relative to
the fixed ideal uniform port; no fair-bit sampler or CPU adequacy is claimed. -/
namespace Signatures.Runtime.CaliperBackend
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat → Nat} {F G K : Nat → Type}
    [∀ n, Field (F n)] [∀ n, SampleableType (F n)]
    [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
    [∀ n, AddCommGroup (K n)] [∀ n, Module (F n) (K n)]
    (port : ∀ n, Interactive.Port (w n) unifSpec)
    (input : ∀ n, Layout (w n) ((G n × G n) × (K n × K n)))
    (output : ∀ n, Layout (w n) (F n)) (generator : ∀ n, G n) (keyGenerator : ∀ n, K n)

def dlogNonuniformWithin (solver : ∀ n, AlgebraicGroupModel.DLog11Adversary (F n) (G n) (K n)) : Prop :=
  (∀ n (scalar : F n), (input n).valid ((generator n, scalar • generator n), (keyGenerator n, scalar • keyGenerator n))) ∧
  Interactive.NonuniformWithin port input output
    (fun n value => solver n value.val.1.1 value.val.1.2 value.val.2.1 value.val.2.2)

omit [∀ n, SampleableType (F n)] in
theorem dlogNonuniformWithin.of_pointwise
    (solver : ∀ n, AlgebraicGroupModel.DLog11Adversary (F n) (G n) (K n))
    (words memory time : Nat → Nat)
    (width : PolynomiallyBounded w) (stored : PolynomiallyBounded words)
    (space : PolynomiallyBounded memory) (elapsed : PolynomiallyBounded time)
    (implemented : ∀ n, dlogWithin (port n) (input n) (output n) (generator n) (keyGenerator n)
      (words n) (memory n) (time n) (solver n)) :
    dlogNonuniformWithin port input output generator keyGenerator solver :=
  ⟨fun n => (implemented n).1, width, words, memory, time, stored, space, elapsed,
    fun n => (implemented n).2⟩

/-- Hardness against all polynomial-code, polynomial-memory, polynomial-time
nonuniform solver families in this fixed Caliper model. -/
def dlogNonuniformHardness : Prop :=
  ∀ solver, dlogNonuniformWithin port input output generator keyGenerator solver →
    negligible (fun n => Model.dlog11Advantage (generator n) (keyGenerator n) (solver n))

end Signatures.Runtime.CaliperBackend
