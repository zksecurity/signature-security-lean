import Proofs.Runtime.BackendWeightedReplySemantics
import Proofs.Runtime.BackendWeightedTerms

/-! Native generation bounds for the actual signing inputs. The source row
count is degree/dimension plus one. Only the supplied topic/slot encoding is
bounded; the key domain can be infinite. The fallback is executed and charged. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM

open BackendProgram LazyAGM.ReplySyntax

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

theorem Index.terms_length (index : Index)
    (m : index.messageTy.Value (cryptoBase F G₁ G₂ K M)) :
    (index.sourceTerms cost m).length = index.bound + 1 := by
  cases index with
  | oops d => rw [Index.oops_sourceTerms, OOPS.LazyAGM.terms_length]; rfl
  | proximity ell => rw [Index.proximity_sourceTerms, List.length_map, Proximity.LazyAGM.terms_length]; rfl

include sizes

omit [Q.HasCategory] QP QS in
theorem Index.terms_rows_size (index : Index)
    (m : index.messageTy.Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hm : Q.size (rep.ty index.messageTy) m ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hj : ∀ j : Fin (index.bound + 1), Q.size (rep.ty (boundedNat index.bound)) j ≤ width) :
    ∀ row ∈ index.sourceTerms cost m, Q.size (rep.ty (Terms.termTy index.ty)) row ≤ 5 * width := by
  cases index with
  | oops d =>
    have hk := (sizes.snd_le (rep.ty scalar) (rep.ty key) m).trans hm
    rw [Index.oops_sourceTerms]
    intro row hr
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
    have hscalar := hf (m.1 ^ j.val)
    have hindex := hj j
    have hprod := @sizes.prod_le
    dsimp only [Index.ty, Index.bound, Terms.termTy, Weights.oopsKey, LanguageRepresentation.ty] at *
    grind only
  | proximity ell =>
    have hk := (sizes.snd_le (rep.ty (tupleTy scalar ell)) (rep.ty key) m).trans hm
    rw [Index.proximity_sourceTerms]
    intro row hr
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hr
    have hkey : original.1.2 = m.2 := by
      simp only [Proximity.LazyAGM.terms, List.mem_cons] at horiginal
      rcases horiginal with rfl | horiginal
      · rfl
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp horiginal
        rfl
    have hscalar := hf original.2
    have hindex := hj (Weights.encodeProximityKey original.1).1
    have hprod := @sizes.prod_le
    have hslot : (Weights.encodeProximityKey original.1).2 = m.2 := by
      cases h : original.1.1 <;> simpa only [Weights.encodeProximityKey, h] using hkey
    dsimp only [Index.ty, Index.bound, Terms.termTy, Weights.proximityKey,
      Prod.map, id_eq, LanguageRepresentation.ty] at *
    grind only

include lists in
omit [Q.HasCategory] QP QS in
theorem Index.terms_size (index : Index)
    (m : index.messageTy.Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hm : Q.size (rep.ty index.messageTy) m ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hj : ∀ j : Fin (index.bound + 1), Q.size (rep.ty (boundedNat index.bound)) j ≤ width) :
    Q.size (rep.ty (.list (Terms.termTy index.ty))) (index.sourceTerms cost m) ≤
      Terms.termSpace width (index.bound + 1) := by
  have h := lists.size_le_length (rep.ty (Terms.termTy index.ty)) (index.sourceTerms cost m)
    (5 * width) (index.terms_rows_size rep cost sizes m width hh hm hf hj)
  rw [index.terms_length cost] at h
  dsimp [Terms.termSpace]
  nlinarith

omit [Q.HasCategory] QP QS in
theorem Index.default_size (index : Index)
    (m : index.messageTy.Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hm : Q.size (rep.ty index.messageTy) m ≤ width)
    (hf : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hj : Q.size (rep.ty (boundedNat index.bound)) (0 : Fin (index.bound + 1)) ≤ width) :
    Q.size (rep.ty (Terms.termTy index.ty))
      (index.defaultTerm.denote (arithmetic F G₁ G₂ K M cost) (m, ())) ≤ 5 * width := by
  have hprod := @sizes.prod_le
  have hsnd := @sizes.snd_le
  cases index <;>
    dsimp only [Index.defaultTerm, Index.messageTy, Index.ty, Index.bound, Reply.oopsDefault,
      Reply.proximityDefault, Expr.denote, v0, Var.get, arithmetic, Terms.termTy,
      Weights.oopsKey, Weights.oopsMessage, Weights.proximityKey, Weights.proximityTupleMessage,
      LanguageRepresentation.ty] at * <;>
    grind only

include laws dataLaws primitiveBound mono in
theorem Index.default_cost (index : Index)
    (m : index.messageTy.Value (cryptoBase F G₁ G₂ K M)) (width finZeroTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hm : Q.size (rep.ty index.messageTy) m ≤ width)
    (hf : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hj : Q.size (rep.ty (boundedNat index.bound)) (0 : Fin (index.bound + 1)) ≤ width)
    (hfin : (primitiveBound (.finZero index.bound)).time () ≤ finZeroTime)
    (hzero : (primitiveBound .zero).time () ≤ zeroTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive index.defaultTerm) (m, ()) ≤
      finZeroTime + zeroTime + 24 * overhead (64 * width) := by
  apply (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
    dataLaws primitiveBound index.defaultTerm (m, ())).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 64 * width, overhead k ≤ overhead (64 * width) := fun _ hk => mono hk
  cases index <;>
    dsimp only [Index.defaultTerm, Index.messageTy, Index.ty, Index.bound, Reply.oopsDefault,
      Reply.proximityDefault, Expression.compileBound, Expression.variableBound,
      LocalBound.pair, LocalBound.compose, LocalBound.fst, LocalBound.snd, DataCostLaws.unitBound,
      Expr.denote, v0, Var.get, arithmetic, Terms.termTy, Weights.oopsKey, Weights.oopsMessage,
      Weights.proximityKey, Weights.proximityTupleMessage, LanguageRepresentation.ty,
      LanguageRepresentation.env] at * <;>
    grind only

def Index.termsTime (index : Index) (overhead : Nat → Nat)
    (width indexTime mulTime finZeroTime oneTime : Nat) : Nat :=
  match index with
  | .oops d => Terms.oopsNativeTime overhead width d indexTime mulTime oneTime
  | .proximity ell => Terms.proximityNativeTime overhead width ell indexTime finZeroTime oneTime

include laws dataLaws primitiveBound lists mono in
theorem Index.terms_cost (index : Index)
    (m : index.messageTy.Value (cryptoBase F G₁ G₂ K M)) (width indexTime mulTime finZeroTime oneTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hm : Q.size (rep.ty index.messageTy) m ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hj : ∀ j : Fin (index.bound + 1), Q.size (rep.ty (boundedNat index.bound)) j ≤ width)
    (hn : ∀ k ≤ index.bound + 1, Q.size rep.data.nat k ≤ width)
    (hi : ∀ k ≤ index.bound + 1, (primitiveBound (.finOfNat index.bound)).time k ≤ indexTime)
    (hmul : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (hfin : (primitiveBound (.finZero index.bound)).time () ≤ finZeroTime)
    (hone : (primitiveBound .one).time () ≤ oneTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive index.terms) (m, ()) ≤
      index.termsTime overhead width indexTime mulTime finZeroTime oneTime := by
  cases index with
  | oops d =>
    have hk := (sizes.snd_le (rep.ty scalar) (rep.ty key) m).trans hm
    have h := Terms.oopsCode_cost rep data cost primitive laws dataLaws primitiveBound sizes lists mono
      d m width indexTime mulTime oneTime hh hu hf hk hj hn hi hmul hone
    simpa only [Terms.oopsCode, QuantitativeStepClass.Realizer.cost_castFunction,
      Index.terms, Index.termsTime] using h
  | proximity ell =>
    have hk := (sizes.snd_le (rep.ty (tupleTy scalar ell)) (rep.ty key) m).trans hm
    have hv := (sizes.fst_le (rep.ty (tupleTy scalar ell)) (rep.ty key) m).trans hm
    have h := Terms.proximityCode_cost rep data cost primitive laws dataLaws primitiveBound sizes lists mono
      ell m width indexTime finZeroTime oneTime hh hu hf hv hk hj hn hi hfin hone
    simpa only [Terms.proximityCode, QuantitativeStepClass.Realizer.cost_castFunction,
      Index.terms, Index.termsTime] using h

end Signatures.Runtime.WeightedAGM
