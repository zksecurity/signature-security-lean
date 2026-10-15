import Signatures.Runtime.BackendWeightedExtractionInputs

/-! Encoded frames for extraction preparation. Bounds include the complete
coefficient list, transcript, fallback row and scalar/paired cache, including
unused coefficient suffixes and shadowed cache entries. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM.Extract

open BackendProgram Evaluate

def preparationFrameWidth (width tokenCap coeffCap rowCap cacheCap : Nat) : Nat :=
  (8 * rowCap + 8 * tokenCap + 8 * coeffCap + 16 * cacheCap + 64) * width

theorem preparationFrameWidth_ge (width tokenCap coeffCap rowCap cacheCap : Nat) :
    width ≤ preparationFrameWidth width tokenCap coeffCap rowCap cacheCap := by
  calc
    width = 1 * width := by omega
    _ ≤ preparationFrameWidth width tokenCap coeffCap rowCap cacheCap := Nat.mul_le_mul_right width (by omega)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type} [Field F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes lists

omit [Field F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M] in
theorem preparationInput_size {indexTy messageTy : Ty CryptoAtom}
    (tr : List (messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F)
    (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F)
    (width tokenCap coeffCap rowCap cacheCap : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ht : ∀ p ∈ tr, Q.size (rep.ty (AGM.tokenTy messageTy)) p ≤ width)
    (hd : Q.size (rep.ty (Terms.termTy indexTy)) default ≤ 7 * width)
    (hnt : tr.length ≤ tokenCap) (hnc : coeff.length ≤ coeffCap) :
    Q.size (rep.env [.list (AGM.tokenTy messageTy), .list scalar, Terms.termTy indexTy]) (tr, coeff, default, ()) ≤
      preparationFrameWidth width tokenCap coeffCap rowCap cacheCap := by
  have htSize := lists.size_le_cap (rep.ty (AGM.tokenTy messageTy)) tr width tokenCap ht hnt
  have hcSize := lists.size_le_cap (rep.ty scalar) coeff width coeffCap (fun f _ => hf f) hnc
  have hp := @sizes.prod_le
  have hntHeader := Nat.mul_le_mul_left tokenCap hh
  have hncHeader := Nat.mul_le_mul_left coeffCap hh
  dsimp only [preparationFrameWidth, LanguageRepresentation.env, LanguageRepresentation.ty] at *
  clear hf ht
  grind only

omit [Field F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M] in
theorem preparationCache_size {indexTy value : Ty CryptoAtom}
    (cache : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)))
    (width tokenCap coeffCap rowCap cacheCap : Nat) (hh : header ≤ width)
    (hk : ∀ p ∈ cache, Q.size (rep.ty indexTy) p.1 ≤ 7 * width)
    (hv : ∀ f : value.Value (cryptoBase F G₁ G₂ K M), Q.size (rep.ty value) f ≤ 3 * width)
    (hn : cache.length ≤ cacheCap) :
    Q.size (rep.ty (Reply.cacheTy indexTy value)) cache ≤ preparationFrameWidth width tokenCap coeffCap rowCap cacheCap := by
  have hrow (p) (hp : p ∈ cache) : Q.size (rep.ty (.pair indexTy value)) p ≤ 11 * width := by
    have h := sizes.prod_le (rep.ty indexTy) (rep.ty value) p
    have hi := hk p hp
    have hf := hv p.2
    exact h.trans (by omega)
  have h := lists.size_le_cap (rep.ty (.pair indexTy value)) cache (11 * width) cacheCap hrow hn
  have hcHeader := Nat.mul_le_mul_left cacheCap hh
  exact h.trans (by dsimp [preparationFrameWidth]; nlinarith)

end Signatures.Runtime.WeightedAGM.Extract
