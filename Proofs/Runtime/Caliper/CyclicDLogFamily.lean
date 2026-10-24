import Proofs.Runtime.Caliper.CyclicDLog
import Proofs.Runtime.Caliper.Family

/-! Ordinary DLog hardness against polynomial-resource Caliper families.
The word-width, port and layout families are fixed before choosing the solver.
This is nonuniform word-machine security with ideal uniform sampling. -/
namespace Signatures.Runtime.CaliperBackend
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat → Nat} {F G : Nat → Type}
    [∀ n, Field (F n)] [∀ n, SampleableType (F n)] [∀ n, DecidableEq (F n)]
    [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
    (port : ∀ n, Interactive.Port (w n) unifSpec)
    (input : ∀ n, Layout (w n) (G n × G n)) (output : ∀ n, Layout (w n) (F n))
    (generator : ∀ n, G n)

def cyclicDLogNonuniformWithin (solver : ∀ n, DiffieHellman.DLogAdversary (F n) (G n)) : Prop :=
  (∀ n (scalar : F n), (input n).valid (generator n, scalar • generator n)) ∧
    Interactive.NonuniformWithin port input output (fun n value => solver n value.val.1 value.val.2)

omit [∀ n, SampleableType (F n)] [∀ n, DecidableEq (F n)] in
theorem cyclicDLogNonuniformWithin.of_pointwise
    (solver : ∀ n, DiffieHellman.DLogAdversary (F n) (G n))
    (words memory time : Nat → Nat)
    (width : PolynomiallyBounded w) (stored : PolynomiallyBounded words)
    (space : PolynomiallyBounded memory) (elapsed : PolynomiallyBounded time)
    (implemented : ∀ n, cyclicDLogWithin (port n) (input n) (output n) (generator n)
      (words n) (memory n) (time n) (solver n)) :
    cyclicDLogNonuniformWithin port input output generator solver :=
  ⟨fun n => (implemented n).1, width, words, memory, time, stored, space, elapsed,
    fun n => (implemented n).2⟩

def cyclicDLogNonuniformHardness : Prop :=
  ∀ solver, cyclicDLogNonuniformWithin port input output generator solver →
    negligible (fun n => 𝒟[DiffieHellman.dlogExperiment (generator n) (solver n)] {true})

end Signatures.Runtime.CaliperBackend
