import Signatures.Runtime.BackendLazyAGMSolver
import Signatures.Runtime.BackendLazyAGMExtractionSize
import Signatures.Runtime.BackendLazyAGMOutputSize

/-! Derive the extractor's input capacities from the native caller's reserved
state and the decoded full output. Cache/transcript capacities count encountered
requests, and coefficient capacities follow from positive-cell output encoding.
No separate coefficient-length certificate is supplied by the attacker. -/

open PFunctor

namespace Signatures.Runtime.LazyAGM.NativeSolver

open BackendProgram NativeHandler

def terminalInputWidth (width outputWidth cap : Nat) : Nat :=
  outputWidth + handlerStoreWidth width cap + 3 * width

def terminalFrameWidth (width outputWidth routeWidth cap : Nat) : Nat :=
  routeWidth + terminalInputWidth width outputWidth cap +
    extractionWidth (terminalInputWidth width outputWidth cap) cap outputWidth cap

theorem terminalInputWidth_base (width outputWidth cap : Nat) :
    width ≤ terminalInputWidth width outputWidth cap := by
  dsimp [terminalInputWidth, handlerStoreWidth]
  nlinarith

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))

structure ExtractionInputCaps (value : Ty CryptoAtom) (width queryCap coeffCap cacheCap : Nat)
    (output : (AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M))
    (tr : Model.LazyAGM.Transcript M M G₁)
    (cache : List (M × value.Value (cryptoBase F G₁ G₂ M M))) : Prop where
  environment : Q.size (rep.env [AGM.outputTy message, transcriptTy]) (output, tr, ()) ≤ width
  tokens : ∀ p ∈ tr.1 ++ tr.2, Q.size (rep.ty (AGM.tokenTy message)) p ≤ width
  transcript : tr.1.length ≤ queryCap ∧ tr.2.length ≤ queryCap
  coefficients : output.2.2.1.length ≤ coeffCap ∧ output.2.2.2.length ≤ coeffCap
  cached : cache.length ≤ cacheCap
  keys : ∀ p ∈ cache, Q.size (rep.ty message) p.1 ≤ width

variable {header : Nat} (sizes : SizeLaws Q header) (lengths : ListLengthLaws Q rep.data)

include sizes lengths

theorem extraction_input_caps (value config : Ty CryptoAtom) (width outputWidth cap : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (output : (AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M))
    (saved : (storeTy value config).Value (cryptoBase F G₁ G₂ M M))
    (ho : Q.size (rep.ty (AGM.outputTy message)) output ≤ outputWidth)
    (hs : ReservedState (Q := Q) rep width cap 0 saved)
    (hstore : Q.size (rep.ty (storeTy value config)) saved ≤ handlerStoreWidth width cap) :
    ExtractionInputCaps (Q := Q) rep value (terminalInputWidth width outputWidth cap) cap outputWidth cap
      output saved.2.2 saved.2.1 := by
  have hw := terminalInputWidth_base width outputWidth cap
  have hl := coefficient_lengths_le_output rep sizes lengths output
  have htr : Q.size (rep.ty transcriptTy) saved.2.2 ≤ handlerStoreWidth width cap :=
    (sizes.snd_le (rep.ty (cacheTy value)) (rep.ty transcriptTy) saved.2).trans
      ((sizes.snd_le (rep.ty config) (rep.ty (.pair (cacheTy value) transcriptTy)) saved).trans hstore)
  refine ⟨?_, ?_, ?_, ⟨hl.1.trans ho, hl.2.trans ho⟩, ?_, ?_⟩
  · have hp := sizes.prod_le (rep.ty transcriptTy) rep.data.unit (saved.2.2, ())
    have he := sizes.prod_le (rep.ty (AGM.outputTy message))
      (StepClass.HasProd.prod (rep.ty transcriptTy) rep.data.unit) (output, saved.2.2, ())
    change Q.size (StepClass.HasProd.prod (rep.ty (AGM.outputTy message))
      (StepClass.HasProd.prod (rep.ty transcriptTy) rep.data.unit)) (output, saved.2.2, ()) ≤ _
    dsimp only [terminalInputWidth] at *
    omega
  · intro p hp
    have hm : Q.size (rep.ty message) p.1 ≤ width := by
      rcases List.mem_append.mp hp with hp | hp
      · exact hs.1.2.1 p hp
      · exact hs.1.2.2 p hp
    have hg' := hg p.2
    have ht := sizes.prod_le (rep.ty message) (rep.ty point₁) p
    have h3 : 3 * width ≤ terminalInputWidth width outputWidth cap := by dsimp [terminalInputWidth]; omega
    change Q.size (StepClass.HasProd.prod (rep.ty message) (rep.ty point₁)) p ≤ _
    omega
  · have ht := hs.2.2
    omega
  · have hc := hs.2.1
    omega
  · intro p hp
    exact (hs.1.1 p hp).trans hw

end Signatures.Runtime.LazyAGM.NativeSolver
