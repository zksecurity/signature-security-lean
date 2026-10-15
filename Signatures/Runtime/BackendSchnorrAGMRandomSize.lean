import Signatures.Runtime.BackendSchnorrAGMRandom

/-! Random requests preserve all storage capacities. Their size accounting
includes ignored coefficient rows and the runtime-selected arity encoding. -/

open PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Random

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

structure Input (width cap basisCap signedCap groupCap rowCap coeffCap arityCap : Nat)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) : Prop where
  arity : input.2.2.1 ≤ arityCap
  state : Signing.StateBound (Q := Q) rep width cap basisCap signedCap input.2.2.2
  groups : input.1.length ≤ groupCap
  rows : input.2.1.length ≤ rowCap
  coefficients : ∀ row ∈ input.2.1, row.length ≤ coeffCap

def Prepared (width cap basisCap signedCap arityCap : Nat)
    (input : preparedTy.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  input.1 ≤ arityCap ∧ Signing.StateBound (Q := Q) rep width cap basisCap signedCap input.2

structure Output (width cap basisCap signedCap arityCap : Nat)
    (output : outputTy.Value (cryptoBase F G₁ G₂ K M)) : Prop where
  value : output.1.1 ≤ arityCap
  groups : output.1.2 = []
  state : Signing.StateBound (Q := Q) rep width cap basisCap signedCap output.2

def frameWidth (width cap basisCap signedCap groupCap rowCap coeffCap : Nat) : Nat :=
  Signing.frameWidth width cap basisCap signedCap + (4 * groupCap + 4 * rowCap * (coeffCap + 1) + 128) * width

theorem marked_property (width cap basisCap signedCap : Nat) (empty : Bool) (s : EncodedState F G₁ M)
    (hs : Signing.StateBound (Q := Q) rep width cap basisCap signedCap s) :
    Signing.StateBound (Q := Q) rep width cap basisCap signedCap (marked empty s) :=
  ⟨hs.cache, hs.cacheLength, hs.history.basisLength, hs.history.signed, hs.history.signedLength⟩

theorem prepare_property (width cap basisCap signedCap groupCap rowCap coeffCap arityCap : Nat)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep width cap basisCap signedCap groupCap rowCap coeffCap arityCap input) :
    Prepared (Q := Q) rep width cap basisCap signedCap arityCap (prepareValue input) :=
  ⟨hi.arity, marked_property rep width cap basisCap signedCap input.1.isEmpty input.2.2.2 hi.state⟩

theorem wrap_property (width cap basisCap signedCap arityCap : Nat)
    (input : preparedTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Prepared (Q := Q) rep width cap basisCap signedCap arityCap input) :
    Output (Q := Q) rep width cap basisCap signedCap arityCap (wrapValue input) :=
  ⟨hi.1, rfl, hi.2⟩

variable [C.HasSum] [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes lists

theorem input_size (width cap basisCap signedCap groupCap rowCap coeffCap arityCap : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width) (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hn : ∀ n ≤ arityCap, Q.size rep.data.nat n ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep width cap basisCap signedCap groupCap rowCap coeffCap arityCap input) :
    Q.size (rep.ty inputTy) input ≤ frameWidth width cap basisCap signedCap groupCap rowCap coeffCap ∧
      Q.size (rep.env [inputTy]) (input, ()) ≤ frameWidth width cap basisCap signedCap groupCap rowCap coeffCap := by
  have hs := Signing.state_size rep sizes lists width cap basisCap signedCap hh hb hf input.2.2.2 hi.state
  have hn' := hn input.2.2.1 hi.arity
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
  dsimp only [frameWidth, Signing.frameWidth, LanguageRepresentation.ty, LanguageRepresentation.env] at *
  constructor <;> grind only

theorem prepared_size (width cap basisCap signedCap arityCap : Nat)
    (hh : header ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hn : ∀ n ≤ arityCap, Q.size rep.data.nat n ≤ width)
    (input : preparedTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Prepared (Q := Q) rep width cap basisCap signedCap arityCap input) :
    Q.size (rep.ty preparedTy) input ≤ Signing.frameWidth width cap basisCap signedCap := by
  have hs := Signing.state_size rep sizes lists width cap basisCap signedCap hh hb hf input.2 hi.2
  have hn' := hn input.1 hi.1
  have hp := sizes.prod_le rep.data.nat (rep.ty stateTy) input
  dsimp only [Signing.frameWidth, LanguageRepresentation.ty] at *
  grind only

theorem output_size (width cap basisCap signedCap arityCap : Nat)
    (hh : header ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hn : ∀ n ≤ arityCap, Q.size rep.data.nat n ≤ width)
    (output : outputTy.Value (cryptoBase F G₁ G₂ K M))
    (ho : Output (Q := Q) rep width cap basisCap signedCap arityCap output) :
    Q.size (rep.ty outputTy) output ≤ Signing.frameWidth width cap basisCap signedCap := by
  have hs := Signing.state_size rep sizes lists width cap basisCap signedCap hh hb hf output.2 ho.state
  have hn' := hn output.1.1 ho.value
  have hg : Q.size (rep.ty (.list point₁)) output.1.2 ≤ header := by
    rw [ho.groups]
    exact lists.nil_le _
  have hp := @sizes.prod_le
  dsimp only [Signing.frameWidth, LanguageRepresentation.ty] at *
  grind only

end Signatures.Runtime.SchnorrAGM.Native.Random
