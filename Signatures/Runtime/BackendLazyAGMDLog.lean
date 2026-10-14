import Signatures.Runtime.BackendLazyAGMSolverWithin

/-! DLog hardness in the fixed native backend used by the general caller and
the AGM reductions. Every challenge must fit the input cap. Stored description
size and online execution time are distinct resource bounds. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.LazyAGM.NativeSolver

open BackendProgram

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  {control : ControlCosts} {queryCost : (i : Nat) → unifSpec.Range i → Nat}
  (backend : Backend.{v, w, x} Q unifSpec iface control queryCost)
  (descriptionSizes : DescriptionSize Q) (factor : Nat)
  (description : backend.DescriptionBound descriptionSizes factor)

def dlogWithin (g : G₁) (g₂ : G₂) (inputWidth codeSize time : Nat)
    (solver : AlgebraicGroupModel.DLog11Adversary F G₁ G₂) : Prop :=
  (∀ x : F, Q.size (rep.env inputTypes) (g, x • g, g₂, x • g₂, ()) ≤ inputWidth) ∧
  Within backend descriptionSizes factor description (rep.env inputTypes) (rep.ty scalar) inputWidth codeSize time
    (fun input => solver input.1 input.2.1 input.2.2.1 input.2.2.2.1)

variable [C.HasOption] {header : Nat} (sizes : SizeLaws Q header)

include sizes

theorem challenge_size (groupWidth keyWidth unitWidth : Nat)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ groupWidth)
    (hk : ∀ pk : G₂, Q.size (rep.ty point₂) pk ≤ keyWidth)
    (hu : Q.size rep.data.unit () ≤ unitWidth) (g : G₁) (g₂ : G₂) (x : F) :
    Q.size (rep.env inputTypes) (g, x • g, g₂, x • g₂, ()) ≤
      2 * groupWidth + 2 * keyWidth + unitWidth + 4 * header := by
  have hprod := @sizes.prod_le
  dsimp only [inputTypes, LanguageRepresentation.env] at *
  grind only

end Signatures.Runtime.LazyAGM.NativeSolver
