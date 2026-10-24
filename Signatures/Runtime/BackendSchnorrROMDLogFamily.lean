import Proofs.Runtime.BackendSchnorrROMDLog
import Proofs.Runtime.BackendConfiguration

/-! Nonuniform DLog hardness in one fixed backend for ordinary-ROM Schnorr.
One executable per security parameter handles every challenge; stored code/advice,
input size and runtime all have polynomial bounds across the family. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeSolver.Family

open BackendProgram

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G M : Nat → Type}
  [∀ n, Field (F n)] [∀ n, SampleableType (F n)] [∀ n, DecidableEq (F n)]
  [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
  (config : Configuration.{v, w, x} Q unifSpec)
  (rep : ∀ n, LanguageRepresentation C (cryptoBase (F n) (G n) (G n) (M n) (M n)))
  (g : ∀ n, G n) (inputWidth : Nat → Nat)

def dlogNonuniformWithin (solver : ∀ n, G n → G n → ProbComp (F n)) : Prop :=
  (∀ n (r : F n), Q.size ((rep n).env inputTypes) (g n, r • g n, ()) ≤ inputWidth n) ∧
  config.nonuniformWithin (fun n => (rep n).env inputTypes) (fun n => (rep n).ty scalar) inputWidth
    (fun n input => solver n input.1 input.2.1)

/-- Hardness covers general local code and polynomial stored advice in the same
execution model; it is not restricted to the reduction's arithmetic syntax. -/
def dlogNonuniformHardness : Prop :=
  ∀ solver, dlogNonuniformWithin config rep g inputWidth solver →
    negligible (fun n => 𝒟[DiffieHellman.dlogExperiment (g n) (solver n)] {true})

end Signatures.Runtime.Schnorr.ListROM.NativeSolver.Family
