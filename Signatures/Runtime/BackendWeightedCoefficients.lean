import Signatures.Runtime.WeightedCoefficientsDescription
import Signatures.Runtime.WeightedCoefficientsSize

/-! Native signing-coefficient expansion with exact source representations and
stored-code and output-size bounds. Complete runtime bounds are derived in
`BackendWeightedCoefficientBudget.lean`; these definitions do not assume a
completed expansion budget. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM.Coefficients

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

def oopsCode (d : Nat) :
    Q.Realizer (rep.env [.list (AGM.tokenTy Weights.oopsMessage), .list scalar])
      (rep.ty (.list (Terms.termTy (Weights.oopsKey d))))
      (fun env => Model.LazyAGM.WeightedReduction.signedTerms (OOPS.LazyAGM.terms d) env.2.1 env.1.reverse) :=
  (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (signedTerms (Terms.oops d))).castFunction (by
    funext env
    exact oops_signedTerms_denote cost d env.1 env.2.1)

def proximityCode (ell : Nat) :
    Q.Realizer (rep.env [.list (AGM.tokenTy (Weights.proximityTupleMessage ell)), .list scalar])
      (rep.ty (.list (Terms.termTy (Weights.proximityKey ell))))
      (fun env => (Model.LazyAGM.WeightedReduction.signedTerms Proximity.LazyAGM.terms env.2.1
        (env.1.reverse.map (Prod.map (Weights.proximityMessageEquiv ell) id))).map
          (Prod.map Weights.encodeProximityKey id)) :=
  (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
    (signedTerms (Terms.proximity ell))).castFunction (by
      funext env
      exact proximity_signedTerms_denote cost ell env.1 env.2.1)

variable (sizes : DescriptionSize Q) (allowance : Nat)
  (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
  (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
  (hp : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ primitiveSize instr)

include laws dataLaws hp

theorem oopsCode_description (d : Nat) :
    sizes.localSize (oopsCode rep data cost primitive d) ≤
      description allowance primitiveSize (Terms.oopsDescription allowance primitiveSize d) := by
  rw [oopsCode, DescriptionSize.castFunction]
  exact (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes
    allowance laws dataLaws primitiveSize hp (signedTerms (Terms.oops d))).trans
      (oops_description allowance primitiveSize d)

theorem proximityCode_description (ell : Nat) :
    sizes.localSize (proximityCode rep data cost primitive ell) ≤
      description allowance primitiveSize (Terms.proximityDescription allowance primitiveSize ell) := by
  rw [proximityCode, DescriptionSize.castFunction]
  exact (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes
    allowance laws dataLaws primitiveSize hp (signedTerms (Terms.proximity ell))).trans
      (proximity_description allowance primitiveSize ell)

end Signatures.Runtime.WeightedAGM.Coefficients
