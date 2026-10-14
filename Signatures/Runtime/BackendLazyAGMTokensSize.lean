import Signatures.Runtime.BackendTokenRows
import Signatures.Runtime.BackendLazyAGMEvaluateSize

/-! Encoded preparation/evaluation frames. The complete coefficient list is
retained and charged even when its suffix has no transcript occurrence. -/

open PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram

def tokenFrameWidth (width tokenCap coeffCap cacheCap : Nat) : Nat :=
  evaluationWidth (9 * width) tokenCap (cacheCap + tokenCap) +
    (4 * tokenCap + 4 * coeffCap + 16) * width

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type} [Field F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes lists

omit lists in
theorem tokenRows_entries (cost : PrimitiveCosts)
    (tr : List (M × G₁)) (coeff : List F) (default : (M × G₁) × F) (width : Nat)
    (hh : header ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ht : ∀ p ∈ tr, Q.size (rep.ty (AGM.tokenTy message)) p ≤ width) :
    let rows := ((AGM.tokenRows (dataTy := message)).weakenTail [evalRowTy]).denote
      (arithmetic F G₁ G₂ M M cost) (tr, coeff, default, ())
    rows.length = tr.length ∧ ∀ row ∈ rows,
      Q.size (rep.ty evalRowTy) row ≤ 3 * width ∧ Q.size (rep.ty message) row.1.1 ≤ width := by
  dsimp only
  rw [TokenCompiler.rows_denote cost]
  refine ⟨by simp only [List.length_mapIdx, List.length_reverse], ?_⟩
  intro row hrow
  obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hrow
  have ht' := ht _ (List.mem_reverse.mp (List.getElem_mem hn))
  have hf' := hf (Model.LazyAGM.tokenCoeff coeff n)
  have hp := sizes.prod_le (rep.ty (AGM.tokenTy message)) (rep.ty scalar)
    (tr.reverse[n], Model.LazyAGM.tokenCoeff coeff n)
  change Q.size (rep.ty evalRowTy) _ ≤ _ at hp
  dsimp only at hp
  exact ⟨by omega, (sizes.fst_le (rep.ty message) (rep.ty point₁) tr.reverse[n]).trans ht'⟩

omit [Field F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M] in
theorem tokenInput_size
    (tr : List (M × G₁)) (coeff : List F) (default : (M × G₁) × F)
    (width tokenCap coeffCap cacheCap : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ht : ∀ p ∈ tr, Q.size (rep.ty (AGM.tokenTy message)) p ≤ width)
    (hd : Q.size (rep.ty evalRowTy) default ≤ width)
    (hnt : tr.length ≤ tokenCap) (hnc : coeff.length ≤ coeffCap) :
    Q.size (rep.env [.list (AGM.tokenTy message), .list scalar, evalRowTy]) (tr, coeff, default, ()) ≤
      tokenFrameWidth width tokenCap coeffCap cacheCap := by
  have htSize := lists.size_le_cap (rep.ty (AGM.tokenTy message)) tr width tokenCap ht hnt
  have hcSize := lists.size_le_cap (rep.ty scalar) coeff width coeffCap (fun f _ => hf f) hnc
  have hp := @sizes.prod_le
  have hntHeader := Nat.mul_le_mul_left tokenCap hh
  have hncHeader := Nat.mul_le_mul_left coeffCap hh
  dsimp only [tokenFrameWidth, evaluationWidth, LanguageRepresentation.env, LanguageRepresentation.ty] at *
  clear hf ht
  grind only

omit [Field F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M] in
theorem tokenCache_size {value : Ty CryptoAtom}
    (cache : List (M × value.Value (cryptoBase F G₁ G₂ M M)))
    (width tokenCap coeffCap cacheCap : Nat) (hh : header ≤ width)
    (hk : ∀ p ∈ cache, Q.size (rep.ty message) p.1 ≤ width)
    (hv : ∀ f : value.Value (cryptoBase F G₁ G₂ M M), Q.size (rep.ty value) f ≤ 3 * width)
    (hn : cache.length ≤ cacheCap) :
    Q.size (rep.ty (cacheTy value)) cache ≤ tokenFrameWidth width tokenCap coeffCap cacheCap := by
  have h3 : width ≤ 3 * width := by omega
  have h := evaluationCache_size rep sizes lists (value := value) cache (3 * width) tokenCap (cacheCap + tokenCap)
    (hh.trans h3) (fun p hp => ⟨(hk p hp).trans h3, hv p.2⟩) (by omega)
  exact h.trans (by dsimp [tokenFrameWidth, evaluationWidth]; nlinarith)

end Signatures.Runtime.LazyAGM
