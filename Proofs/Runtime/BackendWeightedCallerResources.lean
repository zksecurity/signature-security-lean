import Proofs.Runtime.BackendWeightedCallerBudget
import Proofs.Runtime.GeneralCallerResources

/-! Recover native signature-caller conditions from the attacker's own measured
execution resources. Request decoding has an explicit representation-level size
law; native ports separately account for its execution cost. Reachability and
continuation closure are derived, not extra attacker assumptions. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.WeightedAGM.NativeHandler

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M Input Output : Type} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (indexTy messageTy : Ty CryptoAtom)
  (bd : Boundary C (generalSpec (indexTy.Value (cryptoBase F G₁ G₂ K M)) (messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor Input Output)

/-- Size expansion from the caller's request representation to native payloads.
This law does not make decoding free: `PortCaps` still charges its actual code. -/
structure RequestRecovery where
  recover : Nat → Nat
  monotone : Monotone recover
  request : ∀ i, RequestSized (Q := Q) rep indexTy messageTy (recover (Q.size bd.pos i)) i

variable {header : Nat} (sizes : SizeLaws Q header)

include sizes

/-- Shared request encodings need no size expansion. -/
def RequestRecovery.canonical (hpos : bd.pos = generalPositions rep indexTy messageTy randomBound) :
    RequestRecovery (Q := Q) rep indexTy messageTy bd where
  recover := id
  monotone := monotone_id
  request := by
    intro i
    rw [hpos]
    have houter := sizes.sum_payload_le
      (StepClass.HasSum.sum (rep.ty (boundedNat randomBound)) (rep.ty indexTy)) (rep.ty messageTy) i
    rcases i with (n | m) | m
    · have hinner := sizes.sum_payload_le (rep.ty (boundedNat randomBound)) (rep.ty indexTy) (.inl n)
      exact hinner.trans houter
    · have hinner := sizes.sum_payload_le (rep.ty (boundedNat randomBound)) (rep.ty indexTy) (.inr m)
      exact hinner.trans houter
    · exact houter

variable [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
  [DecidableEq (messageTy.Value (cryptoBase F G₁ G₂ K M))]
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (recovery : RequestRecovery (Q := Q) rep indexTy messageTy bd)
  (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))

include hrun

attribute [local implicit_reducible] PFunctor.Idx

include recovery in
theorem reachable_request (state : R.machine.State) (hs : GeneralCaller.Reachable R state)
    (i : GeneralRequest (indexTy.Value (cryptoBase F G₁ G₂ K M)) (messageTy.Value (cryptoBase F G₁ G₂ K M)) randomBound) (next : (generalSpec (indexTy.Value (cryptoBase F G₁ G₂ K M)) (messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).Range i → R.machine.State)
    (hv : R.machine.view state = .inr ⟨i, next⟩) :
    RequestSized (Q := Q) rep indexTy messageTy (recovery.recover bound.peakHeadSize) i := by
  have hh := (GeneralCaller.reachable_sizes R bound hrun state hs).2
  rw [R.machine.head_eq_inr_of_view hv] at hh
  have hp := (sizes.sum_payload_le bd.out bd.pos (.inr i)).trans hh
  have hr := recovery.request i
  have hm := recovery.monotone hp
  rcases i with (n | m) | m <;> exact hr.trans hm

/-- The entire returned encoding is bounded, including any representation
coefficients. Projecting a message or recovering list lengths is a separate law. -/
theorem reachable_output (state : R.machine.State) (hs : GeneralCaller.Reachable R state)
    (out : Output) (hv : R.machine.view state = .inl out) :
    Q.size bd.out out ≤ bound.peakHeadSize := by
  have hh := (GeneralCaller.reachable_sizes R bound hrun state hs).2
  rw [R.machine.head_eq_inl_of_view hv] at hh
  exact (sizes.sum_payload_le bd.out bd.pos (.inl out)).trans hh

include recovery in
theorem resource_step (width : Nat) (hwidth : recovery.recover bound.peakHeadSize ≤ width)
    (state : R.machine.State) (hs : GeneralCaller.Reachable R state)
    (i : GeneralRequest (indexTy.Value (cryptoBase F G₁ G₂ K M)) (messageTy.Value (cryptoBase F G₁ G₂ K M)) randomBound) (next : (generalSpec (indexTy.Value (cryptoBase F G₁ G₂ K M)) (messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).Range i → R.machine.State)
    (hv : R.machine.view state = .inr ⟨i, next⟩) :
    RequestSized (Q := Q) rep indexTy messageTy width i ∧ ∀ reply, GeneralCaller.Reachable R (next reply) := by
  have hr := reachable_request rep indexTy messageTy bd sizes R recovery bound hrun state hs i next hv
  refine ⟨?_, fun reply => GeneralCaller.reachable_step R state hs i next hv reply⟩
  rcases i with (r | m) | m <;> exact hr.trans hwidth

end Signatures.Runtime.WeightedAGM.NativeHandler
