import Proofs.Runtime.WeightedCoefficients
import Proofs.Runtime.BackendWeightedTermsSize

/-! Output accounting for the actual signing-coefficient expansion. The number
of rows depends on signing replies and the numerical degree/dimension, including
zero and missing coefficients. Only encountered topic/slot encodings are bounded.
These bounds do not assume a finite message or base-index domain. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM.Coefficients

open Terms BackendProgram

/-- Multiplication changes weights, never the number of generated terms. -/
theorem source_signedTerms_length {F I M G : Type} [MulZeroOneClass F]
    (terms : M → List (I × F)) (coeff : List F) (tr : List (M × G))
    (termCount : Nat) (hlen : ∀ m, (terms m).length = termCount) :
    (Model.LazyAGM.WeightedReduction.signedTerms terms coeff tr).length =
      tr.length * termCount := by
  simp [Model.LazyAGM.WeightedReduction.signedTerms, List.mapIdx_eq_zipIdx_map,
    List.length_flatten, List.map_map, Function.comp_def, hlen]

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes lists

theorem signedTerms_output_size {indexTy messageTy : Ty CryptoAtom}
    (cost : PrimitiveCosts) (terms : Expr CryptoOp [messageTy] (.list (termTy indexTy)))
    (tr : List (messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F)
    (tokenCap termCount indexWidth fieldWidth : Nat)
    (ht : tr.length ≤ tokenCap)
    (hlen : ∀ m, (terms.denote (arithmetic F G₁ G₂ K M cost) (m, ())).length = termCount)
    (hi : ∀ p ∈ tr, ∀ t ∈ terms.denote (arithmetic F G₁ G₂ K M cost) (p.1, ()),
      Q.size (rep.ty indexTy) t.1 ≤ indexWidth)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ fieldWidth) :
    Q.size (rep.ty (.list (termTy indexTy)))
      ((signedTerms terms).denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, ())) ≤
        tokenCap * termCount * (indexWidth + fieldWidth + 2 * header) + header := by
  rw [signedTerms_denote]
  apply (lists.size_le_cap (rep.ty (termTy indexTy)) _ (indexWidth + fieldWidth + header)
    (tokenCap * termCount) ?_ ?_).trans
  · simp [two_mul, Nat.add_assoc]
  · intro row hr
    obtain ⟨ts, hts, hr⟩ := List.mem_flatten.mp hr
    obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hts
    obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hr
    have hk := hi _ (List.mem_reverse.mp (List.getElem_mem hn)) t ht'
    have hp := sizes.prod_le (rep.ty indexTy) (rep.ty scalar)
      (t.1, Model.LazyAGM.tokenCoeff coeff n * t.2)
    have hs := hf (Model.LazyAGM.tokenCoeff coeff n * t.2)
    dsimp only at hp
    exact hp.trans (by omega)
  · rw [source_signedTerms_length _ _ _ termCount hlen, List.length_reverse]
    exact Nat.mul_le_mul_right termCount ht

theorem oops_signedTerms_output_size (cost : PrimitiveCosts) (d : Nat)
    (tr : List ((F × K) × G₁)) (coeff : List F) (tokenCap width : Nat)
    (ht : tr.length ≤ tokenCap) (hh : header ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hk : ∀ p ∈ tr, Q.size (rep.ty key) p.1.2 ≤ width)
    (hj : ∀ j : Fin (d + 1), Q.size (rep.ty (boundedNat d)) j ≤ width) :
    Q.size (rep.ty (.list (termTy (Weights.oopsKey d))))
      ((signedTerms (Terms.oops d)).denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, ())) ≤
        (6 * tokenCap * (d + 1) + 1) * width := by
  have h := signedTerms_output_size rep sizes lists cost (Terms.oops d) tr coeff
    tokenCap (d + 1) (3 * width) width ht
    (by intro m; rw [← Expr.run_value, Terms.oops_value]; exact OOPS.LazyAGM.terms_length d m)
    (by
      intro p hp t ht'
      rw [← Expr.run_value, Terms.oops_value] at ht'
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ht'
      have hprod := sizes.prod_le (rep.ty key) (rep.ty (boundedNat d)) (p.1.2, j)
      have htopic := hk p hp
      have hindex := hj j
      change Q.size (rep.ty (Weights.oopsKey d)) (p.1.2, j) ≤ _ at hprod ⊢
      dsimp only at hprod
      omega) hf
  have hm := Nat.mul_le_mul_left (tokenCap * (d + 1)) hh
  nlinarith

theorem proximity_signedTerms_output_size (cost : PrimitiveCosts) (ell : Nat)
    (tr : List ((Weights.proximityTupleMessage ell).Value (cryptoBase F G₁ G₂ K M) × G₁))
    (coeff : List F) (tokenCap width : Nat)
    (ht : tr.length ≤ tokenCap) (hh : header ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hk : ∀ p ∈ tr, Q.size (rep.ty key) p.1.2 ≤ width)
    (hj : ∀ j : Fin (ell + 1), Q.size (rep.ty (boundedNat ell)) j ≤ width) :
    Q.size (rep.ty (.list (termTy (Weights.proximityKey ell))))
      ((signedTerms (Terms.proximity ell)).denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, ())) ≤
        (6 * tokenCap * (ell + 1) + 1) * width := by
  have h := signedTerms_output_size rep sizes lists cost (Terms.proximity ell) tr coeff
    tokenCap (ell + 1) (3 * width) width ht
    (by intro m; rw [← Expr.run_value, Terms.proximity_value]; simp)
    (by
      intro p hp t ht'
      rw [← Expr.run_value, Terms.proximity_value] at ht'
      obtain ⟨sourceTerm, hsource, hencode⟩ := List.mem_map.mp ht'
      subst t
      have hkey (j : Fin (ell + 1)) :
          Q.size (rep.ty (Weights.proximityKey ell)) (j, p.1.2) ≤ 3 * width := by
        have hprod := sizes.prod_le (rep.ty (boundedNat ell)) (rep.ty key) (j, p.1.2)
        have htopic := hk p hp
        have hindex := hj j
        change Q.size (rep.ty (Weights.proximityKey ell)) (j, p.1.2) ≤ _ at hprod
        dsimp only at hprod
        omega
      simp only [Proximity.LazyAGM.terms, List.mem_cons, List.mem_ofFn] at hsource
      rcases hsource with rfl | ⟨j, rfl⟩
      · exact hkey 0
      · exact hkey j.succ) hf
  have hm := Nat.mul_le_mul_left (tokenCap * (ell + 1)) hh
  nlinarith

end Signatures.Runtime.WeightedAGM.Coefficients
