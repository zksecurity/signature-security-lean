import Signatures.Runtime.BackendSchnorrROMLiveIndexCost

/-! Stored description of the actual native selector. The scan body is stored
once, and the public query-limit literal is included in the bound. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeSelection

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

theorem selector_description (qH : Nat) (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance) :
    sizes.localSize (selector rep data cost primitive qH) ≤
      2 * sizes.localSize (primitive .scale₁) + sizes.localSize (primitive .add₁) +
        2 * sizes.localSize (primitive .point₁Eq) + sizes.localSize (primitive .messageEq) +
        sizes.localSize (primitive .natAdd) + sizes.localSize (primitive .natLt) +
        qH + 4096 * allowance + 16 := by
  have h := NativeComponents.localCode_description rep data cost primitive (expression qH)
    sizes allowance laws dataLaws
  rw [selector, DescriptionSize.castFunction]
  apply h.trans
  have hbody : liveIndexBody = indexBodyWith (Γ := [])
      (hashEq.weakenTail [.pair hashKey scalar, indexResult, hashKey, hashCache]) := rfl
  simp only [expression, oneExpression, verifyExpression, indexExpression, guardExpression,
    liveIndex, liveIndexFold, hbody, indexBodyWith, hashEq, reverseList, Expr.weakenTail, Var.weakenTail,
    Expression.descriptionBound, Expression.variableDescription]
  omega

end Signatures.Runtime.Schnorr.ListROM.NativeSelection
