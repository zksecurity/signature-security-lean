import Proofs.Runtime.BackendWeightedSignInputs
import Proofs.Runtime.BackendWeightedCoefficientBudget

/-! Actual extraction coefficient preparation for either weighted scheme.
Chronological expansion has one row per signature term, with all coefficients
counted, including zero weights. The cost is derived from primitive contracts;
the encoded bounds concern only encountered message and index values. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (mono : Monotone overhead)

def Index.coefficientTime (index : Index) (overhead : Nat → Nat)
    (width tokenCap coeffCap indexTime finZeroTime oneTime mulTime natEqTime natSubTime natAddTime zeroTime : Nat) : Nat :=
  match index with
  | .oops d => Coefficients.oopsCoefficientTime overhead width tokenCap coeffCap d indexTime mulTime oneTime
      natEqTime natSubTime natAddTime zeroTime
  | .proximity ell => Coefficients.proximityCoefficientTime overhead width tokenCap coeffCap ell indexTime finZeroTime
      oneTime mulTime natEqTime natSubTime natAddTime zeroTime

include laws dataLaws primitiveBound sizes lists mono in
theorem Index.coefficients_cost (index : Index)
    (tr : List (index.messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F)
    (width tokenCap coeffCap indexTime finZeroTime oneTime mulTime natEqTime natSubTime natAddTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ max (tokenCap + 1) (index.bound + 1), Q.size rep.data.nat n ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hk : ∀ p ∈ tr, Q.size (rep.ty (AGM.tokenTy index.messageTy)) p ≤ width)
    (hj : ∀ j : Fin (index.bound + 1), Q.size (rep.ty (boundedNat index.bound)) j ≤ width)
    (htc : tr.length ≤ tokenCap) (hcc : coeff.length ≤ coeffCap)
    (hi : ∀ k ≤ index.bound + 1, (primitiveBound (.finOfNat index.bound)).time k ≤ indexTime)
    (h0 : (primitiveBound (.finZero index.bound)).time () ≤ finZeroTime)
    (h1 : (primitiveBound .one).time () ≤ oneTime)
    (hm : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (hEq : ∀ n ≤ tokenCap, (primitiveBound .natEq).time (n, 0) ≤ natEqTime)
    (hSub : ∀ n ≤ tokenCap, (primitiveBound .natSub).time (n, 1) ≤ natSubTime)
    (hAdd : ∀ n ≤ tokenCap, (primitiveBound .natAdd).time (n, 1) ≤ natAddTime)
    (hZero : (primitiveBound .zero).time () ≤ zeroTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (Coefficients.signedTerms index.terms)) (tr, coeff, ()) ≤
      index.coefficientTime overhead width tokenCap coeffCap indexTime finZeroTime oneTime mulTime natEqTime natSubTime
        natAddTime zeroTime := by
  cases index with
  | oops d =>
    have h := Coefficients.oopsCode_cost rep data cost primitive laws dataLaws primitiveBound sizes lists mono
      d tr coeff width tokenCap coeffCap indexTime mulTime oneTime natEqTime natSubTime natAddTime zeroTime
      hh hu hb hn hf hk hj htc hcc hi hm h1 hEq hSub hAdd hZero
    simpa only [Coefficients.oopsCode, QuantitativeStepClass.Realizer.cost_castFunction,
      Index.terms, Index.coefficientTime] using h
  | proximity ell =>
    have h := Coefficients.proximityCode_cost rep data cost primitive laws dataLaws primitiveBound sizes lists mono
      ell tr coeff width tokenCap coeffCap indexTime finZeroTime oneTime mulTime natEqTime natSubTime natAddTime zeroTime
      hh hu hb hn hf hk hj htc hcc hi h0 h1 hm hEq hSub hAdd hZero
    simpa only [Coefficients.proximityCode, QuantitativeStepClass.Realizer.cost_castFunction,
      Index.terms, Index.coefficientTime] using h

theorem Index.coefficients_length (index : Index)
    (tr : List (index.messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F) :
    ((Coefficients.signedTerms index.terms).denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, ())).length =
      tr.length * (index.bound + 1) := by
  rw [Coefficients.signedTerms_denote]
  change (Model.LazyAGM.WeightedReduction.signedTerms (index.sourceTerms cost) coeff tr.reverse).length = _
  rw [Coefficients.source_signedTerms_length _ _ _ (index.bound + 1)
    (fun m => index.terms_length cost m), List.length_reverse]

include sizes in
omit [Q.HasCategory] QP QS in
theorem Index.coefficients_rows_size (index : Index)
    (tr : List (index.messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F) (width : Nat)
    (hh : header ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hk : ∀ p ∈ tr, Q.size (rep.ty (AGM.tokenTy index.messageTy)) p ≤ width)
    (hj : ∀ j : Fin (index.bound + 1), Q.size (rep.ty (boundedNat index.bound)) j ≤ width) :
    ∀ row ∈ (Coefficients.signedTerms index.terms).denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, ()),
      Q.size (rep.ty (Terms.termTy index.ty)) row ≤ 7 * width := by
  intro row hr
  rw [Coefficients.signedTerms_denote] at hr
  obtain ⟨ts, hts, hr⟩ := List.mem_flatten.mp hr
  obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hts
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
  have hp := List.mem_reverse.mp (List.getElem_mem hn)
  have hm := (sizes.fst_le (rep.ty index.messageTy) (rep.ty point₁) _).trans (hk _ hp)
  have hrow := index.terms_rows_size rep cost sizes _ width hh hm hf hj t ht
  have hkey := (sizes.fst_le (rep.ty index.ty) (rep.ty scalar) t).trans hrow
  have hs := hf (Model.LazyAGM.tokenCoeff coeff n * t.2)
  have hprod := sizes.prod_le (rep.ty index.ty) (rep.ty scalar)
    (t.1, Model.LazyAGM.tokenCoeff coeff n * t.2)
  exact hprod.trans (by dsimp only at *; omega)

include sizes lists in
omit [Q.HasCategory] QP QS in
theorem Index.coefficients_size (index : Index)
    (tr : List (index.messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F)
    (width tokenCap : Nat) (hh : header ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hk : ∀ p ∈ tr, Q.size (rep.ty (AGM.tokenTy index.messageTy)) p ≤ width)
    (hj : ∀ j : Fin (index.bound + 1), Q.size (rep.ty (boundedNat index.bound)) j ≤ width)
    (ht : tr.length ≤ tokenCap) :
    Q.size (rep.ty (.list (Terms.termTy index.ty)))
      ((Coefficients.signedTerms index.terms).denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, ())) ≤
        (8 * (tokenCap * (index.bound + 1)) + 1) * width := by
  have hlen : ((Coefficients.signedTerms index.terms).denote
      (arithmetic F G₁ G₂ K M cost) (tr, coeff, ())).length ≤ tokenCap * (index.bound + 1) := by
    rw [index.coefficients_length cost]
    exact Nat.mul_le_mul_right _ ht
  have h := lists.size_le_cap (rep.ty (Terms.termTy index.ty)) _ (7 * width) (tokenCap * (index.bound + 1))
    (index.coefficients_rows_size rep cost sizes tr coeff width hh hf hk hj) hlen
  have hm := Nat.mul_le_mul_left (tokenCap * (index.bound + 1)) hh
  exact h.trans (by nlinarith)

end Signatures.Runtime.WeightedAGM
