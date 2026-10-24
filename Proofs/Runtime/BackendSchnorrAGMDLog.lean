import Proofs.Runtime.BackendSchnorrAGMSolverWithin

/-! DLog hardness for the fixed backend shared by caller and reduction. Every
challenge fits the input cap; stored program and online runtime are separate. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Solver

open BackendProgram

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type} [Field F] [AddCommGroup G₁] [Module F G₁]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  {control : ControlCosts} {queryCost : (i : Nat) → unifSpec.Range i → Nat}
  (backend : Backend.{v, w, x} Q unifSpec iface control queryCost)
  (descriptionSizes : DescriptionSize Q) (factor : Nat)
  (description : backend.DescriptionBound descriptionSizes factor)

def dlogWithin (g : G₁) (inputWidth codeSize time : Nat) (solver : G₁ → G₁ → ProbComp F) : Prop :=
  (∀ x : F, Q.size (rep.env inputTypes) (g, x • g, ()) ≤ inputWidth) ∧
  Within backend descriptionSizes factor description (rep.env inputTypes) (rep.ty scalar) inputWidth codeSize time
    (fun input => solver input.1 input.2.1)

variable [C.HasOption] {header : Nat} (sizes : SizeLaws Q header)

include sizes

theorem challenge_size (groupWidth unitWidth : Nat)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ groupWidth)
    (hu : Q.size rep.data.unit () ≤ unitWidth) (g : G₁) (x : F) :
    Q.size (rep.env inputTypes) (g, x • g, ()) ≤ 2 * groupWidth + unitWidth + 2 * header := by
  have hprod := @sizes.prod_le
  dsimp only [inputTypes, LanguageRepresentation.env] at *
  grind only

end Signatures.Runtime.SchnorrAGM.Native.Solver
