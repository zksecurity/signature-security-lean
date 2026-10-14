import Signatures.Runtime.BackendCoronSolverWithin
import Signatures.Model.CoCDH

/-! co-CDH hardness in the common native backend. The same fixed executable
class contains arbitrary realized callers and the reduction wrapper. Every
challenge in the experiment must fit the declared input cap; runtime and stored
code remain separate budgets. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Coron.NativeSolver

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

def coCDHWithin (g : G₁) (g₂ : G₂) (inputWidth codeSize time : Nat)
    (solver : BLS.CoCDH.CoCDHAdversary F G₁ G₂) : Prop :=
  (∀ x : F, ∀ h : G₁, Q.size (rep.env inputTypes) (g, g₂, x • g, x • g₂, h, ()) ≤ inputWidth) ∧
  Within backend descriptionSizes factor description (rep.env inputTypes) (rep.ty point₁) inputWidth codeSize time
    (fun input => solver input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2.1)

variable [C.HasOption] {header : Nat} (sizes : SizeLaws Q header)

include sizes

theorem challenge_size (groupWidth keyWidth unitWidth : Nat)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ groupWidth)
    (hk : ∀ pk : G₂, Q.size (rep.ty point₂) pk ≤ keyWidth)
    (hu : Q.size rep.data.unit () ≤ unitWidth) (g : G₁) (g₂ : G₂) (x : F) (h : G₁) :
    Q.size (rep.env inputTypes) (g, g₂, x • g, x • g₂, h, ()) ≤
      3 * groupWidth + 2 * keyWidth + unitWidth + 5 * header := by
  have hprod := @sizes.prod_le
  dsimp only [inputTypes, LanguageRepresentation.env] at *
  grind only

end Signatures.Runtime.Coron.NativeSolver
