import Signatures.Runtime.BackendCoronSolverWithin
import Signatures.Runtime.GeneralCallerResources

/-! Recover the native BLS caller boundary conditions from measured general
execution resources. Only a representation-level payload-size law is added;
reachability, transition closure, request/return bounds, and termination follow
from actual caller traces and backend code. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Coron

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂ (M × G₁))

/-- A boundary encoding may differ from the wrapper encoding, but decoding its
request or returned message must have a specified size expansion. The actual
conversion code and its cost remain the separate native-port obligations. -/
structure BoundaryRecovery where
  recover : Nat → Nat
  monotone : Monotone recover
  request : ∀ i, NativeHandler.RequestSized (Q := Q) rep (recover (Q.size bd.pos i)) i
  forgery : ∀ out, Q.size (rep.ty message) out.1 ≤ recover (Q.size bd.out out)

variable {header : Nat} (sizes : SizeLaws Q header)

include sizes

/-- Shared canonical message encodings require no size expansion. This proves
the recovery law from sum/product payload laws; it does not assert zero-cost
decoding or copy-free execution. -/
def BoundaryRecovery.canonical (hpos : bd.pos = generalPositions rep randomBound)
    (hout : bd.out = rep.ty (.pair message point₁)) : BoundaryRecovery (Q := Q) rep bd where
  recover := id
  monotone := monotone_id
  request := by
    intro i
    rw [hpos]
    have houter := sizes.sum_payload_le
      (StepClass.HasSum.sum (rep.ty (boundedNat randomBound)) (rep.ty message)) (rep.ty message) i
    rcases i with (n | m) | m
    · have hinner := sizes.sum_payload_le (rep.ty (boundedNat randomBound)) (rep.ty message) (.inl n)
      exact hinner.trans houter
    · have hinner := sizes.sum_payload_le (rep.ty (boundedNat randomBound)) (rep.ty message) (.inr m)
      exact hinner.trans houter
    · exact houter
  forgery := by
    intro out
    rw [hout]
    exact sizes.fst_le (rep.ty message) (rep.ty point₁) out

variable [DecidableEq M]
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (recovery : BoundaryRecovery (Q := Q) rep bd)
  (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))

include recovery hrun

set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] PFunctor.Idx

theorem reachable_request (state : R.machine.State) (hs : GeneralCaller.Reachable R state)
    (i : GeneralRequest M randomBound) (next : (generalSpec M G₁ randomBound).Range i → R.machine.State)
    (hv : R.machine.view state = .inr ⟨i, next⟩) :
    NativeHandler.RequestSized (Q := Q) rep (recovery.recover bound.peakHeadSize) i := by
  have hh := (GeneralCaller.reachable_sizes R bound hrun state hs).2
  rw [R.machine.head_eq_inr_of_view hv] at hh
  have hp := (sizes.sum_payload_le bd.out bd.pos (.inr i)).trans hh
  have hr := recovery.request i
  have hm := recovery.monotone hp
  rcases i with (n | m) | m <;> exact hr.trans hm

theorem reachable_message (state : R.machine.State) (hs : GeneralCaller.Reachable R state)
    (out : M × G₁) (hv : R.machine.view state = .inl out) :
    Q.size (rep.ty message) out.1 ≤ recovery.recover bound.peakHeadSize := by
  have hh := (GeneralCaller.reachable_sizes R bound hrun state hs).2
  rw [R.machine.head_eq_inl_of_view hv] at hh
  exact (recovery.forgery out).trans (recovery.monotone ((sizes.sum_payload_le bd.out bd.pos (.inl out)).trans hh))

theorem resource_step (messageWidth width : Nat) (hm : messageWidth ≤ width)
    (hwidth : recovery.recover bound.peakHeadSize ≤ messageWidth)
    (state : R.machine.State) (hs : GeneralCaller.Reachable R state)
    (i : GeneralRequest M randomBound) (next : (generalSpec M G₁ randomBound).Range i → R.machine.State)
    (hv : R.machine.view state = .inr ⟨i, next⟩) :
    NativeHandler.RequestSized (Q := Q) rep width i ∧
      NativeHandler.RequestMessages (fun m => Q.size (rep.ty message) m ≤ messageWidth) i ∧
      ∀ reply, GeneralCaller.Reachable R (next reply) := by
  have hr := reachable_request rep bd sizes R recovery bound hrun state hs i next hv
  refine ⟨?_, ?_, fun reply => GeneralCaller.reachable_step R state hs i next hv reply⟩
  · rcases i with (r | m) | m <;> exact hr.trans (hwidth.trans hm)
  · rcases i with (r | m) | m
    · trivial
    · exact hr.trans hwidth
    · exact hr.trans hwidth

end Signatures.Runtime.Coron
