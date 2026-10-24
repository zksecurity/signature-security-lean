import Proofs.Runtime.BackendSchnorrROMHandler
import Proofs.Runtime.BackendSchnorrROMHandlerPrimitiveBudget

/-! Local encoding/time contracts for the ordinary-ROM request conversion and
dependent reply taggers. Random tagging includes modulo decoding of raw replies;
its contract covers every bounded encoding, including malformed replay values. -/

open PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.ListROM.NativeHandler

open BackendProgram NativeInterface NativeComponents

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M Input Output : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

def RequestBound (width arityCap : Nat) : NativeInterface.Request G₁ M → Prop :=
  Sum.elim (Sum.elim (fun n => n ≤ arityCap) (fun k => Q.size (rep.ty hashKey) k ≤ 3 * width))
    (fun msg => Q.size (rep.ty message) msg ≤ width)

variable (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output)
  (ports : Ports (Q := Q) rep bd)

structure PortCaps (width tapeWidth arityCap portWidth requestTime tagTime : Nat) : Prop where
  request : ∀ q, RequestBound (Q := Q) rep width arityCap q →
    Q.size bd.pos q ≤ portWidth ∧ Q.cost ports.request q ≤ requestTime
  randomTag : ∀ n r, n ≤ arityCap → Q.size rep.data.nat r ≤ tapeWidth →
    Q.size bd.idx (NativeInterface.randomTag (n, r)) ≤ portWidth ∧ Q.cost ports.randomTag (n, r) ≤ tagTime
  hashTag : ∀ k c, Q.size (rep.ty hashKey) k ≤ 3 * width → Q.size (rep.ty scalar) c ≤ 3 * width →
    Q.size bd.idx (NativeInterface.hashTag (k, c)) ≤ portWidth ∧ Q.cost ports.hashTag (k, c) ≤ tagTime
  signingTag : ∀ msg sig, Q.size (rep.ty message) msg ≤ width → Q.size (rep.ty signatureTy) sig ≤ 3 * width →
    Q.size bd.idx (NativeInterface.signingTag (msg, sig)) ≤ portWidth ∧ Q.cost ports.signingTag (msg, sig) ≤ tagTime

def frameWidth (width managedCap liveCap portWidth : Nat) : Nat :=
  8 * (NativeComponents.frameWidth width managedCap liveCap + portWidth)

theorem frame_widths (width managedCap liveCap portWidth : Nat) :
    8 * width ≤ frameWidth width managedCap liveCap portWidth ∧
    portWidth ≤ frameWidth width managedCap liveCap portWidth ∧
    NativeComponents.frameWidth width managedCap liveCap ≤ frameWidth width managedCap liveCap portWidth := by
  have hw : 8 * width ≤ NativeComponents.frameWidth width managedCap liveCap := by
    unfold NativeComponents.frameWidth
    nlinarith only [Nat.zero_le ((managedCap + liveCap) * width)]
  unfold frameWidth
  omega

variable [C.HasOption] {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes

theorem nativeRequest_size (width tapeWidth arityCap : Nat) (hh : header ≤ width) (htw : tapeWidth ≤ width)
    (hn : ∀ n ≤ arityCap, Q.size rep.data.nat n ≤ tapeWidth)
    (request : NativeInterface.Request G₁ M) (hi : RequestBound (Q := Q) rep width arityCap request) :
    Q.size (positions rep) request ≤ 5 * width := by
  have hsum := sizes.sum_le (StepClass.HasSum.sum rep.data.nat (rep.ty hashKey)) (rep.ty message) request
  rcases request with (n | k) | msg
  · have ha := hn n hi
    have hinner := sizes.sum_le rep.data.nat (rep.ty hashKey) (.inl n)
    dsimp only [positions, Sum.elim] at *
    omega
  · have hinner := sizes.sum_le rep.data.nat (rep.ty hashKey) (.inr k)
    change Q.size (rep.ty hashKey) k ≤ 3 * width at hi
    dsimp only [positions, Sum.elim] at *
    omega
  · change Q.size (rep.ty message) msg ≤ width at hi
    dsimp only [positions, Sum.elim] at *
    omega

include lists

theorem store_size (width tapeWidth mc lc sc rc portWidth : Nat)
    (hh : header ≤ width) (ht : header ≤ tapeWidth)
    (hw : (6 * (sc + rc) + 3) * tapeWidth ≤ width)
    (saved : Shared.Store F G₁ M)
    (bound : StoreBound (Q := Q) rep width tapeWidth (mc + 1) (lc + 1) sc rc saved) :
    Q.size (rep.ty storeTy) saved ≤ frameWidth width mc lc portWidth := by
  have h := NativeComponents.store_size rep sizes lists width tapeWidth (mc + 1) (lc + 1) sc rc hh ht hw saved bound
  have hn : Q.size (rep.ty storeTy) saved ≤ NativeComponents.frameWidth width mc lc := by
    unfold NativeComponents.frameWidth
    nlinarith only [h, Nat.zero_le ((mc + lc) * width)]
  exact hn.trans (frame_widths width mc lc portWidth).2.2

end Signatures.Runtime.Schnorr.ListROM.NativeHandler
