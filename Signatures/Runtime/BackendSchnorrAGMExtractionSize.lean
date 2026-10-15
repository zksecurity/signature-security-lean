import Signatures.Runtime.BackendSchnorrAGMExtraction

/-! Bounds for every retained final-output frame, including malformed and
ignored rows. Rejection preserves the input state and needs no cache growth. -/

open PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Extraction

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

def StartingInput (width cap historyWidth basisCap groupCap rowCap coeffCap : Nat)
    (input : startingTy.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  HashDispatch.Input (Q := Q) rep width cap historyWidth basisCap groupCap rowCap coeffCap input.1 ∧
    Q.size (rep.ty scalar) input.2 ≤ width

def Input (width cap historyWidth basisCap groupCap rowCap coeffCap : Nat)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  StartingInput (Q := Q) rep width cap historyWidth basisCap groupCap rowCap coeffCap (startValue input)

def DecodedInput (width cap historyWidth basisCap coeffCap : Nat)
    (input : decodedTy.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  Hash.Input (Q := Q) rep width cap historyWidth basisCap coeffCap input.1 ∧
    Q.size (rep.ty scalar) input.2 ≤ width

def RoutedInput (width cap historyWidth basisCap coeffCap : Nat)
    (input : (Hash.inputTy.Value (cryptoBase F G₁ G₂ K M) ⊕
      Hash.inputTy.Value (cryptoBase F G₁ G₂ K M)) × F) : Prop :=
  Sum.elim (Hash.Input (Q := Q) rep width cap historyWidth basisCap coeffCap)
    (Hash.Input (Q := Q) rep width cap historyWidth basisCap coeffCap) input.1 ∧
      Q.size (rep.ty scalar) input.2 ≤ width

abbrev frameWidth := HashDispatch.frameWidth

omit C Q rep sizes lists in
theorem width_le_frame (width cap historyWidth groupCap rowCap coeffCap : Nat) :
    width ≤ frameWidth width cap historyWidth groupCap rowCap coeffCap := by
  have h := Nat.mul_le_mul_right width (show 1 ≤
    4 * groupCap + 4 * rowCap * (coeffCap + 1) + 4 * coeffCap + 128 by omega)
  dsimp only [frameWidth, HashDispatch.frameWidth]
  omega

omit C Q rep sizes lists in
theorem hash_frame_le (width cap historyWidth groupCap rowCap coeffCap : Nat) :
    Hash.frameWidth width cap coeffCap historyWidth ≤
      frameWidth width cap historyWidth groupCap rowCap coeffCap := by
  have h := Nat.mul_le_mul_right width (show 4 * coeffCap + 64 ≤
    4 * groupCap + 4 * rowCap * (coeffCap + 1) + 4 * coeffCap + 128 by omega)
  dsimp only [frameWidth, HashDispatch.frameWidth, Hash.frameWidth]
  omega

include sizes lists

variable (width cap historyWidth basisCap groupCap rowCap coeffCap : Nat)
  (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
  (hb : ∀ b, Q.size rep.data.bool b ≤ width)
  (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)

include hh hu hb hf

theorem starting_size (input : startingTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : StartingInput (Q := Q) rep width cap historyWidth basisCap groupCap rowCap coeffCap input) :
    Q.size (rep.ty startingTy) input ≤ 3 * frameWidth width cap historyWidth groupCap rowCap coeffCap := by
  have hp := (HashDispatch.input_size rep sizes lists width cap historyWidth basisCap groupCap rowCap coeffCap
    hh hu hb hf input.1 hi.1).1
  change _ ≤ frameWidth width cap historyWidth groupCap rowCap coeffCap at hp
  have hs := hi.2
  have hw := width_le_frame width cap historyWidth groupCap rowCap coeffCap
  exact (sizes.prod_le (rep.ty HashDispatch.inputTy) (rep.ty scalar) input).trans (by omega)

theorem input_size (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep width cap historyWidth basisCap groupCap rowCap coeffCap input) :
    Q.size (rep.ty inputTy) input ≤ 16 * frameWidth width cap historyWidth groupCap rowCap coeffCap := by
  have hp := (HashDispatch.input_size rep sizes lists width cap historyWidth basisCap groupCap rowCap coeffCap
    hh hu hb hf (startValue input).1 hi.1).1
  have hs := hi.2
  have hw := width_le_frame width cap historyWidth groupCap rowCap coeffCap
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  dsimp only [startValue, LanguageRepresentation.ty] at hp hs ⊢
  grind only

variable [Field F]

theorem decoded_size (input : decodedTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : DecodedInput (Q := Q) rep width cap historyWidth basisCap coeffCap input) :
    Q.size (rep.ty decodedTy) input ≤ 3 * frameWidth width cap historyWidth groupCap rowCap coeffCap := by
  have hp := (Hash.input_size rep sizes lists width cap historyWidth basisCap coeffCap hh hu hb hf input.1 hi.1).1
  have hs := hi.2
  have hw := width_le_frame width cap historyWidth groupCap rowCap coeffCap
  have hframe := hash_frame_le width cap historyWidth groupCap rowCap coeffCap
  exact (sizes.prod_le (rep.ty Hash.inputTy) (rep.ty scalar) input).trans (by omega)

theorem routed_size (input : (Hash.inputTy.Value (cryptoBase F G₁ G₂ K M) ⊕
      Hash.inputTy.Value (cryptoBase F G₁ G₂ K M)) × F)
    (hi : RoutedInput (Q := Q) rep width cap historyWidth basisCap coeffCap input) :
    Q.size (StepClass.HasProd.prod (StepClass.HasSum.sum (rep.ty Hash.inputTy) (rep.ty Hash.inputTy))
      (rep.ty scalar)) input ≤ 4 * frameWidth width cap historyWidth groupCap rowCap coeffCap := by
  have hw := width_le_frame width cap historyWidth groupCap rowCap coeffCap
  have hframe := hash_frame_le width cap historyWidth groupCap rowCap coeffCap
  have hprod := sizes.prod_le (StepClass.HasSum.sum (rep.ty Hash.inputTy) (rep.ty Hash.inputTy)) (rep.ty scalar) input
  have hsum := sizes.sum_le (rep.ty Hash.inputTy) (rep.ty Hash.inputTy) input.1
  rcases input with ⟨input, z⟩
  obtain ⟨hi, hz⟩ := hi
  cases input with
  | inl value =>
      have hp := (Hash.input_size rep sizes lists width cap historyWidth basisCap coeffCap hh hu hb hf value hi).1
      dsimp only [Sum.elim] at hprod hsum hz
      omega
  | inr value =>
      have hp := (Hash.input_size rep sizes lists width cap historyWidth basisCap coeffCap hh hu hb hf value hi).1
      dsimp only [Sum.elim] at hprod hsum hz
      omega

omit [C.HasSum] [C.HasOption] [Field F] sizes lists hh hu hb hf groupCap rowCap in
theorem reject_property [Zero F] (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (input : decodedTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : DecodedInput (Q := Q) rep width cap historyWidth basisCap coeffCap input) :
    Read.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth (0, input.1.2.2) :=
  ⟨hz.trans (by omega), hi.1.2.1.1, hi.1.2.1.2.1.trans (by omega), hi.1.2.1.2.2⟩

end Signatures.Runtime.SchnorrAGM.Native.Extraction
