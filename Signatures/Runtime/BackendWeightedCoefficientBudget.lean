import Signatures.Runtime.BackendWeightedCoefficientTime
import Signatures.Runtime.BackendWeightedTermsContext
import Signatures.Runtime.BackendWeightedCoefficients

/-! Complete native signing-coefficient expansion budgets for OOPS and Proximity.
Only individual primitive/structural contracts and input encoding bounds are
premises. Chronological matching, term generation, scaling, both expansion folds,
reversal and retained frames are all included. No message universe is enumerated. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM.Coefficients

open Terms Weights BackendProgram

def coefficientGeneratorWidth (width tokenCap coeffCap termCap : Nat) : Nat :=
  expandRowsWidth (coefficientWidth (5 * width) tokenCap coeffCap termCap) tokenCap termCap

theorem coefficientGeneratorWidth_ge (width tokenCap coeffCap termCap : Nat) :
    width ≤ coefficientGeneratorWidth width tokenCap coeffCap termCap := by
  have hc : 5 * width ≤ coefficientWidth (5 * width) tokenCap coeffCap termCap := by
    calc
      5 * width = 1 * (5 * width) := by omega
      _ ≤ coefficientWidth (5 * width) tokenCap coeffCap termCap := Nat.mul_le_mul_right _ (by omega)
  have he : coefficientWidth (5 * width) tokenCap coeffCap termCap ≤
      coefficientGeneratorWidth width tokenCap coeffCap termCap := by
    calc
      coefficientWidth (5 * width) tokenCap coeffCap termCap =
          1 * coefficientWidth (5 * width) tokenCap coeffCap termCap := by omega
      _ ≤ coefficientGeneratorWidth width tokenCap coeffCap termCap := Nat.mul_le_mul_right _ (by omega)
  exact (show width ≤ 5 * width by omega).trans (hc.trans he)

def oopsCoefficientTime (overhead : Nat → Nat)
    (width tokenCap coeffCap d indexTime mulTime oneTime comparisonTime subtractTime addTime zeroTime : Nat) : Nat :=
  coefficientTime overhead (5 * width) tokenCap coeffCap (d + 1)
    (oopsNativeTime overhead (coefficientGeneratorWidth width tokenCap coeffCap (d + 1)) d
      indexTime mulTime oneTime) mulTime comparisonTime subtractTime addTime zeroTime

def proximityCoefficientTime (overhead : Nat → Nat)
    (width tokenCap coeffCap ell indexTime indexZeroTime oneTime mulTime comparisonTime subtractTime addTime zeroTime : Nat) : Nat :=
  coefficientTime overhead (5 * width) tokenCap coeffCap (ell + 1)
    (proximityNativeTime overhead (coefficientGeneratorWidth width tokenCap coeffCap (ell + 1)) ell
      indexTime indexZeroTime oneTime) mulTime comparisonTime subtractTime addTime zeroTime

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (mono : Monotone overhead)

include laws dataLaws sizes lists mono

theorem oopsCode_cost (d : Nat) (tr : List ((F × K) × G₁)) (coeff : List F)
    (width tokenCap coeffCap indexTime mulTime oneTime comparisonTime subtractTime addTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ max (tokenCap + 1) (d + 1), Q.size rep.data.nat n ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hk : ∀ p ∈ tr, Q.size (rep.ty (AGM.tokenTy oopsMessage)) p ≤ width)
    (hj : ∀ j : Fin (d + 1), Q.size (rep.ty (boundedNat d)) j ≤ width)
    (htc : tr.length ≤ tokenCap) (hcc : coeff.length ≤ coeffCap)
    (hi : ∀ k ≤ d + 1, (primitiveBound (.finOfNat d)).time k ≤ indexTime)
    (hm : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (h1 : (primitiveBound .one).time () ≤ oneTime)
    (hEq : ∀ n ≤ tokenCap, (primitiveBound .natEq).time (n, 0) ≤ comparisonTime)
    (hSub : ∀ n ≤ tokenCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime)
    (hAdd : ∀ n ≤ tokenCap, (primitiveBound .natAdd).time (n, 1) ≤ addTime)
    (hZero : (primitiveBound .zero).time () ≤ zeroTime) :
    Q.cost (oopsCode rep data cost primitive d) (tr, coeff, ()) ≤
      oopsCoefficientTime overhead width tokenCap coeffCap d indexTime mulTime oneTime
        comparisonTime subtractTime addTime zeroTime := by
  rw [oopsCode, QuantitativeStepClass.Realizer.cost_castFunction]
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
    primitiveBound (signedTerms (Terms.oops d)) (tr, coeff, ())).trans ?_
  have hw : width ≤ 5 * width := by omega
  have htopic p (hp : p ∈ tr) : Q.size (rep.ty key) p.1.2 ≤ width :=
    (sizes.snd_le (rep.ty scalar) (rep.ty key) p.1).trans
      ((sizes.fst_le (rep.ty oopsMessage) (rep.ty point₁) p).trans (hk p hp))
  have hterms p (hp : p ∈ tr) t
      (ht : t ∈ (Terms.oops d).denote (arithmetic F G₁ G₂ K M cost) (p.1, ())) :
      Q.size (rep.ty (termTy (oopsKey d))) t ≤ 5 * width := by
    rw [← Expr.run_value, Terms.oops_value] at ht
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ht
    have hprod := @sizes.prod_le
    have hs := hf (p.1.1 ^ j.val)
    have hkey := htopic p hp
    have hindex := hj j
    dsimp only [termTy, oopsKey, LanguageRepresentation.ty] at *
    grind only
  have hW := coefficientGeneratorWidth_ge width tokenCap coeffCap (d + 1)
  exact signedTerms_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    (Terms.oops d) tr coeff (5 * width) tokenCap coeffCap (d + 1)
    (oopsNativeTime overhead (coefficientGeneratorWidth width tokenCap coeffCap (d + 1)) d indexTime mulTime oneTime)
    mulTime comparisonTime subtractTime addTime zeroTime (hh.trans hw) (hu.trans hw)
    (fun b => (hb b).trans hw) (fun n hn' => (hn n (hn'.trans (Nat.le_max_left _ _))).trans hw)
    (fun f => (hf f).trans hw) (fun p hp => (hk p hp).trans hw) htc hcc hterms
    (by intro m; rw [← Expr.run_value, Terms.oops_value]; exact OOPS.LazyAGM.terms_length d m)
    (by
      intro p hp Δ tail hs
      exact Terms.oops_weakenTail_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
        d p.1 tail (coefficientGeneratorWidth width tokenCap coeffCap (d + 1)) indexTime mulTime oneTime
        (hh.trans hW) (hu.trans hW) hs (fun f => (hf f).trans hW) ((htopic p hp).trans hW)
        (fun j => (hj j).trans hW) (fun n hn' => (hn n (hn'.trans (Nat.le_max_right _ _))).trans hW)
        hi hm h1) hm hEq hSub hAdd hZero

theorem proximityCode_cost (ell : Nat)
    (tr : List ((proximityTupleMessage ell).Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F)
    (width tokenCap coeffCap indexTime indexZeroTime oneTime mulTime comparisonTime subtractTime addTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ max (tokenCap + 1) (ell + 1), Q.size rep.data.nat n ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hk : ∀ p ∈ tr, Q.size (rep.ty (AGM.tokenTy (proximityTupleMessage ell))) p ≤ width)
    (hj : ∀ j : Fin (ell + 1), Q.size (rep.ty (boundedNat ell)) j ≤ width)
    (htc : tr.length ≤ tokenCap) (hcc : coeff.length ≤ coeffCap)
    (hi : ∀ k ≤ ell + 1, (primitiveBound (.finOfNat ell)).time k ≤ indexTime)
    (h0 : (primitiveBound (.finZero ell)).time () ≤ indexZeroTime)
    (h1 : (primitiveBound .one).time () ≤ oneTime)
    (hm : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (hEq : ∀ n ≤ tokenCap, (primitiveBound .natEq).time (n, 0) ≤ comparisonTime)
    (hSub : ∀ n ≤ tokenCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime)
    (hAdd : ∀ n ≤ tokenCap, (primitiveBound .natAdd).time (n, 1) ≤ addTime)
    (hZero : (primitiveBound .zero).time () ≤ zeroTime) :
    Q.cost (proximityCode rep data cost primitive ell) (tr, coeff, ()) ≤
      proximityCoefficientTime overhead width tokenCap coeffCap ell indexTime indexZeroTime oneTime mulTime
        comparisonTime subtractTime addTime zeroTime := by
  rw [proximityCode, QuantitativeStepClass.Realizer.cost_castFunction]
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
    primitiveBound (signedTerms (Terms.proximity ell)) (tr, coeff, ())).trans ?_
  have hw : width ≤ 5 * width := by omega
  have hmessage p (hp : p ∈ tr) : Q.size (rep.ty (proximityTupleMessage ell)) p.1 ≤ width :=
    (sizes.fst_le (rep.ty (proximityTupleMessage ell)) (rep.ty point₁) p).trans (hk p hp)
  have hslot p (hp : p ∈ tr) : Q.size (rep.ty key) p.1.2 ≤ width :=
    (sizes.snd_le (rep.ty (tupleTy scalar ell)) (rep.ty key) p.1).trans (hmessage p hp)
  have hterms p (hp : p ∈ tr) t
      (ht : t ∈ (Terms.proximity ell).denote (arithmetic F G₁ G₂ K M cost) (p.1, ())) :
      Q.size (rep.ty (termTy (proximityKey ell))) t ≤ 5 * width := by
    rw [← Expr.run_value, Terms.proximity_value] at ht
    obtain ⟨sourceTerm, hsource, rfl⟩ := List.mem_map.mp ht
    have hrow (j : Fin (ell + 1)) (f : F) :
        Q.size (rep.ty (termTy (proximityKey ell))) ((j, p.1.2), f) ≤ 5 * width := by
      have hprod := @sizes.prod_le
      have hs := hf f
      have hkey := hslot p hp
      have hindex := hj j
      dsimp only [termTy, proximityKey, LanguageRepresentation.ty] at *
      grind only
    simp only [Proximity.LazyAGM.terms, List.mem_cons, List.mem_ofFn] at hsource
    rcases hsource with rfl | ⟨j, rfl⟩
    · exact hrow 0 1
    · exact hrow j.succ _
  have hW := coefficientGeneratorWidth_ge width tokenCap coeffCap (ell + 1)
  exact signedTerms_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    (Terms.proximity ell) tr coeff (5 * width) tokenCap coeffCap (ell + 1)
    (proximityNativeTime overhead (coefficientGeneratorWidth width tokenCap coeffCap (ell + 1)) ell
      indexTime indexZeroTime oneTime) mulTime comparisonTime subtractTime addTime zeroTime
    (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw)
    (fun n hn' => (hn n (hn'.trans (Nat.le_max_left _ _))).trans hw)
    (fun f => (hf f).trans hw) (fun p hp => (hk p hp).trans hw) htc hcc hterms
    (by intro m; rw [← Expr.run_value, Terms.proximity_value]; simp)
    (by
      intro p hp Δ tail hs
      have hv := (sizes.fst_le (rep.ty (tupleTy scalar ell)) (rep.ty key) p.1).trans (hmessage p hp)
      exact Terms.proximity_weakenTail_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
        ell p.1 tail (coefficientGeneratorWidth width tokenCap coeffCap (ell + 1)) indexTime indexZeroTime oneTime
        (hh.trans hW) (hu.trans hW) hs (fun f => (hf f).trans hW) (hv.trans hW) ((hslot p hp).trans hW)
        (fun j => (hj j).trans hW) (fun n hn' => (hn n (hn'.trans (Nat.le_max_right _ _))).trans hW)
        hi h0 h1) hm hEq hSub hAdd hZero

end Signatures.Runtime.WeightedAGM.Coefficients
