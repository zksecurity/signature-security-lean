import Signatures.Runtime.BackendLazyAGMDLog
import Signatures.Runtime.BackendConfiguration

/-! Nonuniform `(1,1)`-DLog hardness in one fixed backend. A single polynomial
bounds code/advice and time over the security parameter. Encodings and a
polynomial challenge-input cap are fixed before solver families are quantified. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.LazyAGM.NativeSolver.Family

open BackendProgram

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Nat → Type}
  [∀ n, Field (F n)] [∀ n, SampleableType (F n)]
  [∀ n, AddCommGroup (G₁ n)] [∀ n, Module (F n) (G₁ n)]
  [∀ n, AddCommGroup (G₂ n)] [∀ n, Module (F n) (G₂ n)]
  (config : Configuration.{v, w, x} Q unifSpec)
  (rep : ∀ n, LanguageRepresentation C (cryptoBase (F n) (G₁ n) (G₂ n) (M n) (M n)))
  (g : ∀ n, G₁ n) (g₂ : ∀ n, G₂ n) (inputWidth : Nat → Nat)

def dlogNonuniformWithin (solver : ∀ n, AlgebraicGroupModel.DLog11Adversary (F n) (G₁ n) (G₂ n)) : Prop :=
  (∀ n (r : F n), Q.size ((rep n).env inputTypes) (g n, r • g n, g₂ n, r • g₂ n, ()) ≤ inputWidth n) ∧
  config.nonuniformWithin (fun n => (rep n).env inputTypes) (fun n => (rep n).ty scalar) inputWidth
    (fun n input => solver n input.1 input.2.1 input.2.2.1 input.2.2.2.1)

/-- Hardness against every polynomial-time, polynomial-code family realized in
this backend, including general local code and polynomial nonuniform advice. -/
def dlogNonuniformHardness : Prop :=
  ∀ solver, dlogNonuniformWithin config rep g g₂ inputWidth solver →
    negligible (fun n => Model.dlog11Advantage (g n) (g₂ n) (solver n))

end Signatures.Runtime.LazyAGM.NativeSolver.Family
