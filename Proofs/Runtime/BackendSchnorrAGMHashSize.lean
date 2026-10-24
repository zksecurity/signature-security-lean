import Proofs.Runtime.BackendSchnorrAGMHash

/-! Hash preparation preserves the whole state and computes an affine pair of
bounded size. Coefficient suffixes contribute to the retained input size. -/

open PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Hash

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

def Input (width cap historyWidth basisCap coeffCap : Nat)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  Q.size (rep.ty cacheKeyTy) input.1 ≤ 15 * width ∧
    Read.StateBound (Q := Q) rep (3 * width) cap historyWidth input.2.2 ∧
      input.2.2.2.1.length ≤ basisCap ∧ input.2.1.length ≤ coeffCap

def frameWidth (width cap coeffCap historyWidth : Nat) : Nat :=
  Read.frameWidth (3 * width) cap historyWidth + (4 * coeffCap + 64) * width

include sizes

theorem prepare_property [Field F] (width cap historyWidth basisCap coeffCap : Nat)
    (hh : header ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep width cap historyWidth basisCap coeffCap input) :
    Read.Input (Q := Q) rep (3 * width) cap historyWidth (prepareValue input) := by
  exact ⟨by have := hi.1; change Q.size (rep.ty cacheKeyTy) input.1 ≤ 5 * (3 * width); omega,
    Flatten.output_size rep sizes _ _ width hh hf, hi.2.1⟩

include lists in
theorem input_size [Field F] (width cap historyWidth basisCap coeffCap : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep width cap historyWidth basisCap coeffCap input) :
    Q.size (rep.ty inputTy) input ≤ frameWidth width cap coeffCap historyWidth ∧
      Q.size (rep.env [inputTy]) (input, ()) ≤ frameWidth width cap coeffCap historyWidth := by
  obtain ⟨hk, ⟨he, hn, hm⟩, _, hcc⟩ := hi
  have hc := CacheCompiler.list_size rep sizes lists input.2.2.1 (5 * (3 * width)) cap (by omega) he hn
  have hm := Read.history_size rep sizes width historyWidth hh hb input.2.2.2 hm
  have hcoeff := lists.size_le_cap (rep.ty scalar) input.2.1 width coeffCap (fun f _ => hf f) hcc
  have hcoeffHeader := Nat.mul_le_mul_left coeffCap hh
  have hprod := @sizes.prod_le
  dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env, frameWidth, Read.frameWidth] at *
  constructor <;> grind only

end Signatures.Runtime.SchnorrAGM.Native.Hash
