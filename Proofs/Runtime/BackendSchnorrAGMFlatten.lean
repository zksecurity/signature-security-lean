import Proofs.Runtime.BackendSchnorrAGMFlattenSum

/-! Native realization and full stored-code bound for Schnorr affine flattening.
The surrounding context remains explicit runtime input to the compiled program. -/

open PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Flatten

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def code {Γ : List (Ty CryptoAtom)} :
    Q.Realizer (rep.env ([.list affineTy, .list scalar] ++ Γ)) (rep.ty affineTy)
      (fun env : List (F × F) × List F × Env (cryptoBase F G₁ G₂ K M) Γ =>
        value env.1 env.2.1) :=
  (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (expression (Γ := Γ))).castFunction (by
    funext env
    exact expression_denote cost env.1 env.2.1 env.2.2)

theorem description {Γ : List (Ty CryptoAtom)} (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (hp : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ primitiveSize instr) :
    sizes.localSize (code rep data cost primitive (Γ := Γ)) ≤
      primitiveSize .zero + primitiveSize .natEq + primitiveSize .natSub + primitiveSize .natAdd +
        2 * primitiveSize .mul + 2 * primitiveSize .add + 1400 * allowance + 16 := by
  rw [code, DescriptionSize.castFunction]
  have h := Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance
    laws dataLaws primitiveSize hp (expression (Γ := Γ))
  refine h.trans ?_
  simp only [expression, sumRows, body, Expression.descriptionBound, Expression.descriptionBound_weakenTail,
    AGM.attachTable, AGM.attachFold, AGM.attachBody, index, indexBody, reverseList, Expression.variableDescription]
  omega

end Signatures.Runtime.SchnorrAGM.Native.Flatten
