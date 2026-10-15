import Signatures.Runtime.BackendSchnorrAGMDLog
import Signatures.Runtime.BackendConfiguration

/-! Nonuniform DLog hardness in one fixed backend. Each parameter selects one
program for every challenge. Stored code/advice, input size and runtime have
fixed polynomial bounds across the family; a uniform program generator is not assumed. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Solver.Family

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

/-- Hardness against every polynomial-time, polynomial-code solver family in
the same backend, including general local code and nonuniform advice. -/
def dlogNonuniformHardness : Prop :=
  ∀ solver, dlogNonuniformWithin config rep g inputWidth solver →
    negligible (fun n => 𝒟[DiffieHellman.dlogExperiment (g n) (solver n)] {true})

end Signatures.Runtime.SchnorrAGM.Native.Solver.Family
