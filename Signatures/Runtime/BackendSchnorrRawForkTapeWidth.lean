import Signatures.Runtime.BackendSchnorrRawForkComposition

/-! Keep narrow tape-entry encodings while charging complete retained outputs
at a wider frame size. This avoids feeding a whole-result width back into each
tape cell when composing the two actual passes. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativeFork

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

def IncomingWidths {config : Ty CryptoAtom} (width tapeWidth savedCap remainingCap : Nat)
    (valid : config.Value (cryptoBase F G₁ G₂ K M) → Prop) :
    (passInput config).Value (cryptoBase F G₁ G₂ K M) → Prop :=
  Both (NativeUniform.StateBound (Q := Q) rep tapeWidth savedCap remainingCap)
    (Ready (Q := Q) rep width valid)

def ReturnedWidths {out : Ty CryptoAtom} (width tapeWidth savedCap remainingCap : Nat)
    (valid : out.Value (cryptoBase F G₁ G₂ K M) → Prop) :
    (passOutput out).Value (cryptoBase F G₁ G₂ K M) → Prop :=
  Both (Ready (Q := Q) rep width valid)
    (NativeUniform.StateBound (Q := Q) rep tapeWidth savedCap remainingCap)

variable [C.HasSum] [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

def Frame.stateAt (width tapeWidth savedCap remainingCap : Nat)
    (hh : header ≤ tapeWidth) (ht : tapeWidth ≤ width) :
    Frame (Q := Q) (rep.ty stateTy) width where
  property := NativeUniform.StateBound (Q := Q) rep tapeWidth savedCap remainingCap
  factor := 6 * (savedCap + remainingCap) + 3
  size_le := fun state hs =>
    (NativeUniform.state_size rep sizes lists tapeWidth savedCap remainingCap hh state hs).trans
      (Nat.mul_le_mul_left _ ht)

def Frame.tapeAt (width tapeWidth savedCap : Nat)
    (hh : header ≤ tapeWidth) (ht : tapeWidth ≤ width) :
    Frame (Q := Q) (rep.ty (.list Replay.Mixed.event)) width where
  property := NativeUniform.TapeBound (Q := Q) rep tapeWidth savedCap
  factor := 6 * savedCap + 1
  size_le := fun tape hs =>
    (NativeUniform.tape_size rep sizes lists tapeWidth savedCap hh tape hs).trans
      (Nat.mul_le_mul_left _ ht)

end Signatures.Runtime.Schnorr.RawTape.NativeFork
