import Proofs.Runtime.BackendCoCDH
import Proofs.Runtime.BackendFamily

/-! co-CDH hardness for polynomial-time, polynomial-description nonuniform
families in a fixed backend. Input caps cover every generated challenge, and
are fixed with the encodings before the solver family is quantified. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Coron.NativeSolver.Family

open BackendProgram

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Nat → Type}
  [∀ n, Field (F n)] [∀ n, SampleableType (F n)] [∀ n, SampleableType (G₁ n)]
  [∀ n, AddCommGroup (G₁ n)] [∀ n, Module (F n) (G₁ n)]
  [∀ n, AddCommGroup (G₂ n)] [∀ n, Module (F n) (G₂ n)]
  {iface : Interface (C := C) unifSpec}
  (rep : ∀ n, LanguageRepresentation C (cryptoBase (F n) (G₁ n) (G₂ n) (M n) (M n)))
  {control : ControlCosts} {queryCost : (i : Nat) → unifSpec.Range i → Nat}
  (backend : Backend.{v, w, x} Q unifSpec iface control queryCost)
  (descriptionSizes : DescriptionSize Q) (factor : Nat)
  (description : backend.DescriptionBound descriptionSizes factor)
  (g : ∀ n, G₁ n) (g₂ : ∀ n, G₂ n) (inputWidth : Nat → Nat)

/-- The same fixed polynomial-code/time class, restricted to input caps that
cover the entire co-CDH challenge distribution. -/
def coCDHNonuniformWithin
    (solver : ∀ n, Env (cryptoBase (F n) (G₁ n) (G₂ n) (M n) (M n)) inputTypes → ProbComp (G₁ n)) : Prop :=
  (∀ n (r : F n) (h : G₁ n),
    Q.size ((rep n).env inputTypes) (g n, g₂ n, r • g n, r • g₂ n, h, ()) ≤ inputWidth n) ∧
  NonuniformWithin backend descriptionSizes factor description
    (fun n => (rep n).env inputTypes) (fun n => (rep n).ty point₁) inputWidth solver

/-- The assumption quantifies over all realizable solver families in this fixed
backend, allowing polynomial nonuniform advice and security-dependent groups. -/
def coCDHNonuniformHardness : Prop :=
  ∀ solver, coCDHNonuniformWithin rep backend descriptionSizes factor description g g₂ inputWidth solver →
    negligible (fun n => Model.coCDHAdvantage (F := F n) (g n) (g₂ n)
      (fun base key challenge publicKey target => solver n (base, key, challenge, publicKey, target, ())))

end Signatures.Runtime.Coron.NativeSolver.Family
