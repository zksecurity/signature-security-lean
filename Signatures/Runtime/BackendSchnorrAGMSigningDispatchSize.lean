import Signatures.Runtime.BackendSchnorrAGMSigningDispatch

/-! All incoming group and coefficient cells contribute to the signing
dispatch representation bound, including ignored rows and rejected requests. -/

open PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.SigningDispatch

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

structure Input (width cap basisCap signedCap groupCap rowCap coeffCap : Nat)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) : Prop where
  decoded : Signing.Input (Q := Q) rep width cap basisCap signedCap input.2.2
  groups : input.1.length ≤ groupCap
  rows : input.2.1.length ≤ rowCap
  coefficients : ∀ row ∈ input.2.1, row.length ≤ coeffCap

structure Output (width cap basisCap signedCap : Nat)
    (output : outputTy.Value (cryptoBase F G₁ G₂ K M)) : Prop where
  scalar : Q.size (rep.ty Signatures.Runtime.scalar) output.1.1 ≤ width
  groups : ∀ g ∈ output.1.2, Q.size (rep.ty point₁) g ≤ width
  groupLength : output.1.2.length ≤ 1
  state : Signing.StateBound (Q := Q) rep width (cap + 1) (basisCap + 1) (signedCap + 1) output.2

def frameWidth (width cap basisCap signedCap groupCap rowCap coeffCap : Nat) : Nat :=
  Signing.frameWidth width cap basisCap signedCap +
    (4 * groupCap + 4 * rowCap * (coeffCap + 1) + 128) * width

theorem wrap_property (width cap basisCap signedCap : Nat)
    (input : Signing.outputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Signing.Output (Q := Q) rep width cap basisCap signedCap input) :
    Output (Q := Q) rep width cap basisCap signedCap (wrapValue input) := by
  refine ⟨hi.scalar, ?_, by simp [wrapValue], hi.state⟩
  intro g hg
  simpa only [wrapValue, List.mem_singleton.mp hg] using hi.point

theorem reject_property [Zero F] (width cap basisCap signedCap : Nat)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (input : Signing.inputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Signing.Input (Q := Q) rep width cap basisCap signedCap input) :
    Output (Q := Q) rep width cap basisCap signedCap (rejectValue input) := by
  refine ⟨hz, by intro g hg; simp [rejectValue] at hg, by simp [rejectValue],
    hi.state.cache, hi.state.cacheLength.trans (Nat.le_succ _), ?_, hi.state.history.signed, ?_⟩
  · exact hi.state.history.basisLength.trans (Nat.le_succ _)
  · exact hi.state.history.signedLength.trans (Nat.le_succ _)

variable [C.HasSum] [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes lists

theorem input_size (width cap basisCap signedCap groupCap rowCap coeffCap : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width) (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep width cap basisCap signedCap groupCap rowCap coeffCap input) :
    Q.size (rep.ty inputTy) input ≤ frameWidth width cap basisCap signedCap groupCap rowCap coeffCap ∧
      Q.size (rep.env [inputTy]) (input, ()) ≤ frameWidth width cap basisCap signedCap groupCap rowCap coeffCap := by
  have hd := Signing.input_size rep sizes lists width cap basisCap signedCap hh hb hf input.2.2 hi.decoded
  have hgroups := lists.size_le_cap (rep.ty point₁) input.1 width groupCap (fun g _ => hg g) hi.groups
  have hrow (row : List F) (hr : row ∈ input.2.1) :
      Q.size (rep.ty (.list scalar)) row ≤ (2 * coeffCap + 1) * width := by
    have h := lists.size_le_cap (rep.ty scalar) row width coeffCap (fun f _ => hf f) (hi.coefficients row hr)
    change Q.size (rep.ty (.list scalar)) row ≤ _ at h
    nlinarith [Nat.mul_le_mul_left coeffCap hh]
  have hrows := lists.size_le_cap (rep.ty (.list scalar)) input.2.1
    ((2 * coeffCap + 1) * width) rowCap hrow hi.rows
  have hgheader := Nat.mul_le_mul_left groupCap hh
  have hrheader := Nat.mul_le_mul_left rowCap hh
  have hp := @sizes.prod_le
  dsimp only [frameWidth, LanguageRepresentation.ty, LanguageRepresentation.env] at *
  constructor <;> grind only

theorem prepare_size (width cap basisCap signedCap groupCap rowCap coeffCap : Nat)
    (hh : header ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep width cap basisCap signedCap groupCap rowCap coeffCap input) :
    Q.size (rep.ty preparedTy) (prepareValue input) ≤ frameWidth width cap basisCap signedCap groupCap rowCap coeffCap := by
  have hd := Signing.input_size rep sizes lists width cap basisCap signedCap hh hb hf input.2.2 hi.decoded
  have hp := sizes.prod_le rep.data.bool (rep.ty Signing.inputTy) (prepareValue input)
  have hflag := hb input.1.isEmpty
  have hpad := Nat.mul_le_mul_right width (show 2 ≤ 4 * groupCap + 4 * rowCap * (coeffCap + 1) + 128 by omega)
  dsimp only [prepareValue, frameWidth] at *
  exact hp.trans (by omega)

theorem route_size (width cap basisCap signedCap groupCap rowCap coeffCap : Nat)
    (hh : header ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep width cap basisCap signedCap groupCap rowCap coeffCap input) :
    Q.size (StepClass.HasSum.sum (rep.ty Signing.inputTy) (rep.ty Signing.inputTy)) (routeValue input) ≤
      frameWidth width cap basisCap signedCap groupCap rowCap coeffCap := by
  have hd := Signing.input_size rep sizes lists width cap basisCap signedCap hh hb hf input.2.2 hi.decoded
  have hs := sizes.sum_le (rep.ty Signing.inputTy) (rep.ty Signing.inputTy) (routeValue input)
  have hpad := Nat.mul_le_mul_right width (show 1 ≤ 4 * groupCap + 4 * rowCap * (coeffCap + 1) + 128 by omega)
  dsimp only [routeValue, frameWidth] at *
  cases hflag : (prepareValue input).1 <;>
    simp only [hflag, Bool.false_eq_true, ↓reduceIte, Sum.elim] at hs ⊢ <;> omega

theorem output_size (width cap basisCap signedCap : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (output : outputTy.Value (cryptoBase F G₁ G₂ K M)) (ho : Output (Q := Q) rep width cap basisCap signedCap output) :
    Q.size (rep.ty outputTy) output ≤ Signing.frameWidth width cap basisCap signedCap := by
  have hs := Signing.state_size rep sizes lists width (cap + 1) (basisCap + 1) (signedCap + 1) hh hb hf output.2 ho.state
  have hg := lists.size_le_cap (rep.ty point₁) output.1.2 width 1 ho.groups ho.groupLength
  have hf' := ho.scalar
  have hp := @sizes.prod_le
  dsimp only [LanguageRepresentation.ty, outputTy, scalarGroupReplyTy, groupReplyTy, Signing.frameWidth] at *
  grind only

end Signatures.Runtime.SchnorrAGM.Native.SigningDispatch
