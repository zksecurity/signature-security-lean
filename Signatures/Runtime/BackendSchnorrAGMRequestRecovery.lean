import Signatures.Runtime.BackendSchnorrAGMHandlerPorts
import Signatures.Runtime.BackendListPayload
import Signatures.Runtime.BackendNatValue

/-! Recover complete Schnorr request conditions from the caller's encoded
request size. Positive cells bound group/row counts; payload accounting bounds
every nested coefficient row. Natural arity is recovered as a numeric range,
which may be exponential in width. Decoding is still charged by PortCaps. -/

open PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Handler

open BackendProgram Interface

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M Input Output : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

omit [C.HasSum] in
theorem argsBound_mono (value : Ty CryptoAtom) (width groups rows coefficients width' groups' rows' coefficients' : Nat)
    (hw : width ≤ width') (hg : groups ≤ groups') (hr : rows ≤ rows') (hc : coefficients ≤ coefficients')
    (args : (argsTy value).Value (cryptoBase F G₁ G₂ K M))
    (h : HandlerComponents.ArgsBound (Q := Q) rep value width groups rows coefficients args) :
    HandlerComponents.ArgsBound (Q := Q) rep value width' groups' rows' coefficients' args :=
  ⟨h.data.trans hw, h.groups.trans hg, h.rows.trans hr, fun row hm => (h.coefficients row hm).trans hc⟩

omit [C.HasSum] in
theorem nativeRequestBound_mono (width groups rows coefficients arity width' groups' rows' coefficients' arity' : Nat)
    (hw : width ≤ width') (hg : groups ≤ groups') (hr : rows ≤ rows') (hc : coefficients ≤ coefficients') (ha : arity ≤ arity')
    (q : NativeRequest F G₁ M) (h : NativeRequestBound (Q := Q) rep width groups rows coefficients arity q) :
    NativeRequestBound (Q := Q) rep width' groups' rows' coefficients' arity' q := by
  rcases q with args | args | args
  · exact ⟨argsBound_mono rep .nat width groups rows coefficients width' groups' rows' coefficients' hw hg hr hc args h.1, h.2.trans ha⟩
  · exact argsBound_mono rep message width groups rows coefficients width' groups' rows' coefficients' hw hg hr hc args h
  · exact argsBound_mono rep message width groups rows coefficients width' groups' rows' coefficients' hw hg hr hc args h

omit [C.HasSum] in
theorem requestBound_mono (width groups rows coefficients arity width' groups' rows' coefficients' arity' : Nat)
    (hw : width ≤ width') (hg : groups ≤ groups') (hr : rows ≤ rows') (hc : coefficients ≤ coefficients') (ha : arity ≤ arity')
    (q : SourceRequest F G₁ M) (h : RequestBound (Q := Q) rep width groups rows coefficients arity q) :
    RequestBound (Q := Q) rep width' groups' rows' coefficients' arity' q :=
  nativeRequestBound_mono rep width groups rows coefficients arity width' groups' rows' coefficients' arity'
    hw hg hr hc ha (encodeRequest q) h

variable (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output)

structure RequestRecovery where
  recover : Nat → Nat
  monotone : Monotone recover
  natural : NatValueLaws Q rep.data
  request : ∀ q,
    let width := recover (Q.size bd.pos q)
    RequestBound (Q := Q) rep width width width width (natural.capacity width) q

variable [C.HasOption] {header : Nat} (sizes : SizeLaws Q header)
  (lengths : ListLengthLaws Q rep.data) (payloads : ListPayloadLaws Q rep.data)

include sizes lengths payloads

theorem argsBound_of_size (value : Ty CryptoAtom) (args : (argsTy value).Value (cryptoBase F G₁ G₂ K M))
    (width : Nat) (hw : Q.size (rep.ty (argsTy value)) args ≤ width) :
    HandlerComponents.ArgsBound (Q := Q) rep value width width width width args := by
  have hdata := sizes.fst_le (rep.ty value) (rep.ty (.pair (.list point₁) (.list (.list scalar)))) args
  have hbody := sizes.snd_le (rep.ty value) (rep.ty (.pair (.list point₁) (.list (.list scalar)))) args
  have hgroups := sizes.fst_le (rep.ty (.list point₁)) (rep.ty (.list (.list scalar))) args.2
  have hrows := sizes.snd_le (rep.ty (.list point₁)) (rep.ty (.list (.list scalar))) args.2
  have hg := lengths.length_le_size (rep.ty point₁) args.2.1
  have hr := lengths.length_le_size (rep.ty (.list scalar)) args.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hdata.trans hw
  · exact hg.trans (hgroups.trans (hbody.trans hw))
  · exact hr.trans (hrows.trans (hbody.trans hw))
  · intro row hm
    have hc := lengths.length_le_size (rep.ty scalar) row
    have hp := payloads.member_size_le lengths (rep.ty (.list scalar)) args.2.2 row hm
    exact hc.trans (hp.trans (hrows.trans (hbody.trans hw)))

theorem nativeRequestBound_of_size (natural : NatValueLaws Q rep.data)
    (q : NativeRequest F G₁ M) (width : Nat) (hw : Q.size (positions rep) q ≤ width) :
    NativeRequestBound (Q := Q) rep width width width width (natural.capacity width) q := by
  have houter := sizes.sum_payload_le (rep.ty randomArgsTy)
    (StepClass.HasSum.sum (rep.ty groupArgsTy) (rep.ty groupArgsTy)) q
  rcases q with args | args | args
  · have hargs := houter.trans hw
    have ha := argsBound_of_size rep sizes lengths payloads .nat args width hargs
    exact ⟨ha, (natural.value_le args.1).trans (natural.monotone ha.data)⟩
  · have hinner := sizes.sum_payload_le (rep.ty groupArgsTy) (rep.ty groupArgsTy) (.inl args)
    exact argsBound_of_size rep sizes lengths payloads message args width (hinner.trans (houter.trans hw))
  · have hinner := sizes.sum_payload_le (rep.ty groupArgsTy) (rep.ty groupArgsTy) (.inr args)
    exact argsBound_of_size rep sizes lengths payloads message args width (hinner.trans (houter.trans hw))

/-- The native request conversion may expand encodings by this explicit size
function. Runtime of the actual conversion is supplied separately by PortCaps. -/
def recovery_of_encoding (natural : NatValueLaws Q rep.data) (recover : Nat → Nat) (mono : Monotone recover)
    (encoded : ∀ q, Q.size (positions rep) (encodeRequest q) ≤ recover (Q.size bd.pos q)) :
    RequestRecovery (Q := Q) rep bd where
  recover := recover
  monotone := mono
  natural := natural
  request q := nativeRequestBound_of_size rep sizes lengths payloads natural (encodeRequest q) _ (encoded q)

/-- Shared encodings recover all cell bounds with no size expansion. The
natural-value contract still distinguishes numeric arity from bit width. -/
def canonicalRecovery (natural : NatValueLaws Q rep.data)
    (encoded : ∀ q, Q.size (positions rep) (encodeRequest q) = Q.size bd.pos q) :
    RequestRecovery (Q := Q) rep bd :=
  recovery_of_encoding rep bd sizes lengths payloads natural id monotone_id (fun q => (encoded q).le)

end Signatures.Runtime.SchnorrAGM.Native.Handler
