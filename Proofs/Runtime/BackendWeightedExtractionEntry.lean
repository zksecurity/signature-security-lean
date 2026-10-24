import Proofs.Runtime.BackendWeightedHandlerState
import Proofs.Runtime.BackendWeightedOutputSize

/-! Recover every extractor input size and length from the returned output and
the preserved interaction store. Surplus coefficients remain charged through
the actual output encoding. No finite query-domain or separately supplied
transcript-token/default/coefficient-size condition is used. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM

open BackendProgram Reply NativeHandler

def extractionEntryWidth (width cap outputCap : Nat) : Nat :=
  outputCap + (8 * cap + 8) * width

theorem extractionEntryWidth_ge (width cap outputCap : Nat) :
    8 * width ≤ extractionEntryWidth width cap outputCap := by
  have h := Nat.mul_le_mul_right width (show 8 ≤ 8 * cap + 8 by omega)
  dsimp only [extractionEntryWidth]
  omega

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (lengths : ListLengthLaws Q rep.data)

include sizes lists lengths

theorem extractionEntry_bounds (index : Index) {value config : Ty CryptoAtom}
    (output : (AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M))
    (saved : (storeTy index.ty index.messageTy value config).Value (cryptoBase F G₁ G₂ K M))
    (width cap outputCap : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hs : ReservedState (Q := Q) rep index width cap 0 saved)
    (ho : Q.size (rep.ty (AGM.outputTy index.messageTy)) output ≤ outputCap) :
    Q.size (rep.env [AGM.outputTy index.messageTy, transcriptTy index.ty index.messageTy])
      (output, saved.2.2, ()) ≤ extractionEntryWidth width cap outputCap ∧
    (∀ p ∈ saved.2.2.1, Q.size (rep.ty (AGM.tokenTy index.ty)) p ≤ extractionEntryWidth width cap outputCap) ∧
    (∀ p ∈ saved.2.2.2, Q.size (rep.ty (AGM.tokenTy index.messageTy)) p ≤ extractionEntryWidth width cap outputCap) ∧
    saved.2.2.1.length ≤ cap ∧ saved.2.2.2.length ≤ cap ∧
    saved.2.1.length ≤ cap * (index.bound + 1) ∧
    (∀ p ∈ saved.2.1, Q.size (rep.ty index.ty) p.1 ≤ 5 * extractionEntryWidth width cap outputCap) ∧
    output.2.2.1.length ≤ outputCap ∧ output.2.2.2.length ≤ outputCap := by
  have hlog (ty : Ty CryptoAtom) (xs : List (ty.Value (cryptoBase F G₁ G₂ K M) × G₁))
      (hx : ∀ p ∈ xs, Q.size (rep.ty ty) p.1 ≤ 5 * width) :
      (∀ p ∈ xs, Q.size (rep.ty (AGM.tokenTy ty)) p ≤ 7 * width) ∧
      Q.size (rep.ty (.list (AGM.tokenTy ty))) xs ≤ xs.length * (7 * width + header) + header := by
    have hrow : ∀ p ∈ xs, Q.size (rep.ty (AGM.tokenTy ty)) p ≤ 7 * width := by
      intro p hp
      have h := sizes.prod_le (rep.ty ty) (rep.ty point₁) p
      have hk := hx p hp
      have hg' := hg p.2
      exact h.trans (by omega)
    exact ⟨hrow, lists.size_le_length (rep.ty (AGM.tokenTy ty)) xs (7 * width) hrow⟩
  have hhlog := hlog index.ty saved.2.2.1 hs.1.2.1
  have hslog := hlog index.messageTy saved.2.2.2 hs.1.2.2
  have htotal : saved.2.2.1.length + saved.2.2.2.length ≤ cap := by simpa using hs.2.2
  have hcache : saved.2.1.length ≤ cap * (index.bound + 1) := by simpa using hs.2.1
  have hw := extractionEntryWidth_ge width cap outputCap
  have htr := sizes.prod_le (rep.ty (.list (AGM.tokenTy index.ty)))
    (rep.ty (.list (AGM.tokenTy index.messageTy))) saved.2.2
  have htail := sizes.prod_le (rep.ty (transcriptTy index.ty index.messageTy)) rep.data.unit (saved.2.2, ())
  have hframe := sizes.prod_le (rep.ty (AGM.outputTy index.messageTy))
    (rep.env [transcriptTy index.ty index.messageTy]) (output, saved.2.2, ())
  have hcoeff := coefficient_lengths_of_output_cap rep sizes lengths output outputCap ho
  refine ⟨?_, (fun p hp => (hhlog.1 p hp).trans (by omega)),
    (fun p hp => (hslog.1 p hp).trans (by omega)), by omega, by omega, hcache,
    (fun p hp => (hs.1.1 p hp).trans (by omega)), hcoeff.1, hcoeff.2.1⟩
  have hhcap := Nat.mul_le_mul_left cap hh
  have hcount := Nat.mul_le_mul_right (7 * width + header) htotal
  dsimp only [extractionEntryWidth, LanguageRepresentation.env, LanguageRepresentation.ty,
    transcriptTy, AGM.tokenTy] at *
  nlinarith only [hhlog.2, hslog.2, htr, htail, hframe, ho, hu, hhcap, hcount, hh]

end Signatures.Runtime.WeightedAGM
