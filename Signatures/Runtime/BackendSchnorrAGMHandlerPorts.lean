import Signatures.Runtime.BackendSchnorrAGMHandler
import Signatures.Runtime.BackendSchnorrAGMHandlerPrimitiveBudget

/-! Encoding and time contracts for the actual general-request decoder and
dependent reply taggers. All supplied groups and coefficient rows remain in
the tagger input. These local contracts do not assume a whole-handler budget. -/

open PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Handler

open BackendProgram Interface

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M Input Output : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

def RandomArgsBound (width groupCap rowCap coeffCap arityCap : Nat) (args : Interface.Args Nat F G₁) : Prop :=
  HandlerComponents.ArgsBound (Q := Q) rep .nat width groupCap rowCap coeffCap args ∧ args.1 ≤ arityCap

def NativeRequestBound (width groupCap rowCap coeffCap arityCap : Nat) : NativeRequest F G₁ M → Prop :=
  Sum.elim (RandomArgsBound (Q := Q) rep width groupCap rowCap coeffCap arityCap)
    (Sum.elim (HandlerComponents.ArgsBound (Q := Q) rep message width groupCap rowCap coeffCap)
      (HandlerComponents.ArgsBound (Q := Q) rep message width groupCap rowCap coeffCap))

def RequestBound (width groupCap rowCap coeffCap arityCap : Nat) (q : SourceRequest F G₁ M) : Prop :=
  NativeRequestBound (Q := Q) rep width groupCap rowCap coeffCap arityCap (encodeRequest q)

structure ReplyBound (value : Ty CryptoAtom) (width : Nat)
    (reply : (groupReplyTy value).Value (cryptoBase F G₁ G₂ K M)) : Prop where
  data : Q.size (rep.ty value) reply.1 ≤ width
  groups : ∀ g ∈ reply.2, Q.size (rep.ty point₁) g ≤ width
  groupLength : reply.2.length ≤ 1

variable (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output)
  (ports : Ports (Q := Q) rep bd)

structure PortCaps (width groupCap rowCap coeffCap arityCap portWidth requestTime tagTime : Nat) : Prop where
  request : ∀ q, RequestBound (Q := Q) rep width groupCap rowCap coeffCap arityCap q →
    Q.size bd.pos q ≤ portWidth ∧ Q.cost ports.request q ≤ requestTime
  randomTag : ∀ args reply, RandomArgsBound (Q := Q) rep width groupCap rowCap coeffCap arityCap args →
    ReplyBound (Q := Q) rep .nat width reply → reply.1 ≤ arityCap →
    Q.size bd.idx (Interface.randomTag (args, reply)) ≤ portWidth ∧ Q.cost ports.randomTag (args, reply) ≤ tagTime
  scalarTag : ∀ signing args reply, HandlerComponents.ArgsBound (Q := Q) rep message width groupCap rowCap coeffCap args →
    ReplyBound (Q := Q) rep scalar width reply →
    Q.size bd.idx (Interface.scalarTag signing (args, reply)) ≤ portWidth ∧ Q.cost (ports.scalarTag signing) (args, reply) ≤ tagTime

def requestWidth (width groupCap rowCap coeffCap : Nat) : Nat :=
  (2 * groupCap + 2 * rowCap * (coeffCap + 1) + 5) * width

def frameWidth (width cap basisCap signedCap groupCap rowCap coeffCap portWidth : Nat) : Nat :=
  16 * (HandlerComponents.frameWidth width cap basisCap signedCap groupCap rowCap coeffCap +
    portWidth + requestWidth width groupCap rowCap coeffCap)

theorem frame_widths (width cap basisCap signedCap groupCap rowCap coeffCap portWidth : Nat) :
    8 * width ≤ frameWidth width cap basisCap signedCap groupCap rowCap coeffCap portWidth ∧
    portWidth ≤ frameWidth width cap basisCap signedCap groupCap rowCap coeffCap portWidth ∧
    3 * requestWidth width groupCap rowCap coeffCap ≤ frameWidth width cap basisCap signedCap groupCap rowCap coeffCap portWidth ∧
    Signing.frameWidth width cap basisCap signedCap ≤ frameWidth width cap basisCap signedCap groupCap rowCap coeffCap portWidth := by
  have hc : Signing.frameWidth width cap basisCap signedCap ≤
      HandlerComponents.frameWidth width cap basisCap signedCap groupCap rowCap coeffCap := by
    dsimp only [HandlerComponents.frameWidth, SigningDispatch.frameWidth]
    omega
  have hw : 8 * width ≤ Signing.frameWidth width cap basisCap signedCap := by dsimp [Signing.frameWidth]; nlinarith
  dsimp only [frameWidth]
  omega

variable [C.HasOption] {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes lists

theorem args_size (value : Ty CryptoAtom) (width cap basisCap signedCap groupCap rowCap coeffCap portWidth : Nat)
    (hh : header ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (args : (argsTy value).Value (cryptoBase F G₁ G₂ K M))
    (hi : HandlerComponents.ArgsBound (Q := Q) rep value width groupCap rowCap coeffCap args) :
    Q.size (rep.ty (argsTy value)) args ≤ frameWidth width cap basisCap signedCap groupCap rowCap coeffCap portWidth := by
  have h := HandlerComponents.args_size rep sizes lists value width groupCap rowCap coeffCap hh hf hg args hi
  have hw := (frame_widths width cap basisCap signedCap groupCap rowCap coeffCap portWidth).2.2.1
  exact h.trans (by dsimp only [requestWidth] at hw; omega)

theorem reply_size (value : Ty CryptoAtom) (width : Nat) (hh : header ≤ width)
    (reply : (groupReplyTy value).Value (cryptoBase F G₁ G₂ K M))
    (hi : ReplyBound (Q := Q) rep value width reply) :
    Q.size (rep.ty (groupReplyTy value)) reply ≤ 5 * width := by
  have hg := lists.size_le_cap (rep.ty point₁) reply.2 width 1 hi.groups hi.groupLength
  have hd := hi.data
  have hp := sizes.prod_le (rep.ty value) (rep.ty (.list point₁)) reply
  dsimp only [LanguageRepresentation.ty] at *
  omega

theorem store_size (width cap basisCap signedCap groupCap rowCap coeffCap portWidth : Nat)
    (hh : header ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (saved : (G₁ × G₁) × EncodedState F G₁ M)
    (hi : HandlerComponents.StoreBound (Q := Q) rep width (cap + 1) (basisCap + 1) (signedCap + 1) saved) :
    Q.size (rep.ty storeTy) saved ≤ frameWidth width cap basisCap signedCap groupCap rowCap coeffCap portWidth := by
  have h := HandlerComponents.store_size rep sizes lists width (cap + 1) (basisCap + 1) (signedCap + 1) hh hb hf saved hi
  have hs : Q.size (rep.ty storeTy) saved ≤ Signing.frameWidth width cap basisCap signedCap :=
    h.trans (by dsimp only [Signing.frameWidth]; nlinarith)
  exact hs.trans (frame_widths width cap basisCap signedCap groupCap rowCap coeffCap portWidth).2.2.2

theorem nativeRequest_size (width groupCap rowCap coeffCap arityCap : Nat)
    (hh : header ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (request : NativeRequest F G₁ M) (hi : NativeRequestBound (Q := Q) rep width groupCap rowCap coeffCap arityCap request) :
    Q.size (positions rep) request ≤ 3 * requestWidth width groupCap rowCap coeffCap := by
  have hwidth : width ≤ requestWidth width groupCap rowCap coeffCap := by
    exact Nat.le_mul_of_pos_left width (by omega)
  have hsum := sizes.sum_le (rep.ty randomArgsTy) (StepClass.HasSum.sum (rep.ty groupArgsTy) (rep.ty groupArgsTy)) request
  rcases request with args | args | args
  · have ha := HandlerComponents.args_size rep sizes lists .nat width groupCap rowCap coeffCap hh hf hg args hi.1
    dsimp only [positions, Sum.elim, randomArgsTy, groupArgsTy, requestWidth] at *
    omega
  · have ha := HandlerComponents.args_size rep sizes lists message width groupCap rowCap coeffCap hh hf hg args hi
    have hinner := sizes.sum_le (rep.ty groupArgsTy) (rep.ty groupArgsTy) (.inl args)
    dsimp only [positions, Sum.elim, randomArgsTy, groupArgsTy, requestWidth] at *
    omega
  · have ha := HandlerComponents.args_size rep sizes lists message width groupCap rowCap coeffCap hh hf hg args hi
    have hinner := sizes.sum_le (rep.ty groupArgsTy) (rep.ty groupArgsTy) (.inr args)
    dsimp only [positions, Sum.elim, randomArgsTy, groupArgsTy, requestWidth] at *
    omega

end Signatures.Runtime.SchnorrAGM.Native.Handler
