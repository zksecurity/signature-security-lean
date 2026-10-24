import Proofs.Runtime.BackendSchnorrROMHandlerPorts
import Proofs.Runtime.BackendNatValue

/-! Recover ordinary-ROM request bounds from measured caller encodings. The
numeric random arity may be exponential in its encoded width. Its capacity is
used only to state local contracts, never to enumerate possible requests. -/

open PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.ListROM.NativeHandler

open BackendProgram NativeInterface NativeComponents

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M Input Output : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

omit [C.HasSum] in
theorem requestBound_mono (width arity width' arity' : Nat)
    (hw : width ≤ width') (ha : arity ≤ arity')
    (q : NativeInterface.Request G₁ M) (h : RequestBound (Q := Q) rep width arity q) :
    RequestBound (Q := Q) rep width' arity' q := by
  rcases q with (n | key) | msg
  · exact h.trans ha
  · exact h.trans (Nat.mul_le_mul_left 3 hw)
  · exact h.trans hw

variable (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output)

structure RequestRecovery where
  recover : Nat → Nat
  monotone : Monotone recover
  natural : NatValueLaws Q rep.data
  request : ∀ q,
    let width := recover (Q.size bd.pos q)
    RequestBound (Q := Q) rep width (natural.capacity width) q

variable [C.HasOption] {header : Nat} (sizes : SizeLaws Q header)

include sizes

theorem requestBound_of_size (natural : NatValueLaws Q rep.data)
    (q : NativeInterface.Request G₁ M) (width : Nat) (hw : Q.size (positions rep) q ≤ width) :
    RequestBound (Q := Q) rep width (natural.capacity width) q := by
  have houter := sizes.sum_payload_le (StepClass.HasSum.sum rep.data.nat (rep.ty hashKey)) (rep.ty message) q
  rcases q with (n | key) | msg
  · have hinner := sizes.sum_payload_le rep.data.nat (rep.ty hashKey) (.inl n)
    exact (natural.value_le n).trans (natural.monotone (hinner.trans (houter.trans hw)))
  · have hinner := sizes.sum_payload_le rep.data.nat (rep.ty hashKey) (.inr key)
    exact (hinner.trans (houter.trans hw)).trans (by omega)
  · exact houter.trans hw

/-- Runtime of the actual conversion is charged separately by PortCaps. -/
def recovery_of_encoding (natural : NatValueLaws Q rep.data) (recover : Nat → Nat) (mono : Monotone recover)
    (encoded : ∀ q, Q.size (positions rep) q ≤ recover (Q.size bd.pos q)) :
    RequestRecovery (Q := Q) rep bd where
  recover := recover
  monotone := mono
  natural := natural
  request q := requestBound_of_size rep sizes natural q _ (encoded q)

def canonicalRecovery (natural : NatValueLaws Q rep.data)
    (encoded : ∀ q, Q.size (positions rep) q = Q.size bd.pos q) :
    RequestRecovery (Q := Q) rep bd :=
  recovery_of_encoding rep bd sizes natural id monotone_id (fun q => (encoded q).le)

end Signatures.Runtime.Schnorr.ListROM.NativeHandler
