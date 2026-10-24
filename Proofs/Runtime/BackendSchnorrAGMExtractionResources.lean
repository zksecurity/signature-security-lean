import Proofs.Runtime.BackendSchnorrAGMExtractionSize
import Proofs.Runtime.BackendSchnorrAGMOutputSize

/-! Recover the complete extraction input contract from the measured final
encoding and the caller's state invariant. All returned group payloads and
coefficient rows are covered, including ignored and malformed output. -/

open PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Extraction

open BackendProgram Interface

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  {header : Nat} (sizes : SizeLaws Q header)
  (lengths : ListLengthLaws Q rep.data) (payloads : ListPayloadLaws Q rep.data)

include sizes lengths payloads

theorem input_of_forgery_size (width cap historyWidth basisCap : Nat)
    (out : SourceForgery F G₁ M) (state : EncodedState F G₁ M)
    (hout : Q.size (rep.ty forgeryTy) (encodeForgery out) ≤ width)
    (hs : Read.StateBound (Q := Q) rep (3 * width) cap historyWidth state)
    (hbasis : state.2.1.length ≤ basisCap) :
    Input (Q := Q) rep width cap historyWidth basisCap width width width (encodeForgery out, state) := by
  have ho := Handler.forgeryBound_of_size rep sizes lengths payloads out width hout
  have hgroups : Q.size (rep.ty (.list point₁)) (out.value.groups ()) ≤ width := by
    exact ((sizes.fst_le (rep.ty (.list point₁)) (rep.ty (.list (.list scalar)))
      (encodeForgery out).2).trans
      (sizes.snd_le (rep.ty (.pair message scalar)) (rep.ty (.pair (.list point₁) (.list (.list scalar))))
        (encodeForgery out))).trans hout
  refine ⟨⟨ho.message, ?_, ho.groups, ho.rows, ho.coefficients, hs, hbasis⟩, ho.scalar⟩
  intro g hg
  exact (payloads.member_size_le lengths (rep.ty point₁) (out.value.groups ()) g hg).trans hgroups

variable (lists : ListSizeLaws Q rep.data header)

include lists

/-- Widen only field/key widths when combining caller and output resources.
The two stored histories keep the caller's existing bound. -/
theorem input_of_state (width outputWidth cap basisCap signedCap : Nat)
    (hh : header ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (out : SourceForgery F G₁ M) (state : EncodedState F G₁ M)
    (hout : Q.size (rep.ty forgeryTy) (encodeForgery out) ≤ outputWidth)
    (hs : Signing.StateBound (Q := Q) rep width cap basisCap signedCap state) :
    Input (Q := Q) rep (max width outputWidth) cap (HandlerComponents.historyWidth width basisCap signedCap)
      basisCap (max width outputWidth) (max width outputWidth) (max width outputWidth)
      (encodeForgery out, state) := by
  have hstate := HandlerComponents.read_state rep sizes lists width cap basisCap signedCap hh hb hf state hs
  apply input_of_forgery_size rep sizes lengths payloads (max width outputWidth) cap
    (HandlerComponents.historyWidth width basisCap signedCap) basisCap out state
    (hout.trans (le_max_right _ _)) ?_ hs.history.basisLength
  refine ⟨?_, hstate.2.1, hstate.2.2⟩
  intro entry hentry
  obtain ⟨hk, hv⟩ := hstate.1 entry hentry
  have hw : width ≤ max width outputWidth := le_max_left _ _
  exact ⟨hk.trans (by omega), hv.trans (by omega)⟩

theorem input_of_store (width outputWidth cap basisCap signedCap : Nat)
    (hh : header ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (out : SourceForgery F G₁ M) (saved : (G₁ × G₁) × EncodedState F G₁ M)
    (hout : Q.size (rep.ty forgeryTy) (encodeForgery out) ≤ outputWidth)
    (hs : HandlerComponents.StoreBound (Q := Q) rep width cap basisCap signedCap saved) :
    Input (Q := Q) rep (max width outputWidth) cap (HandlerComponents.historyWidth width basisCap signedCap)
      basisCap (max width outputWidth) (max width outputWidth) (max width outputWidth)
      (encodeForgery out, saved.2) :=
  input_of_state rep sizes lengths payloads lists width outputWidth cap basisCap signedCap
    hh hb hf out saved.2 hout hs.state

end Signatures.Runtime.SchnorrAGM.Native.Extraction
