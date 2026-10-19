import Signatures.Runtime.Caliper.BLSExtractorFrameBounds
import Signatures.Runtime.Caliper.InteractiveInvariantViews

/-! The hash pass executes the original transcript evaluator while retaining
the forgery target, beta, signature log and signature coefficients. Its remaining
cache reservation is proved for every supported answer, ready for the tail. -/
namespace Signatures.Runtime.CaliperBackend.BLSExtractor
open Caliper BoundedSource OracleComp OracleSpec
section Layout
variable {w : Nat} {M G F : Type} (layout : BLSTokens.Layouts w M G F)
abbrev GoodInput := (BLSExtractorFrame.input layout.good).Value
abbrev BadInput := (BLSExtractorFrame.input layout.bad).Value
abbrev HashInput := (BLSExtractorFrame.prepared layout.good).Value
abbrev HashOutput := (BLSExtractorFrame.returned layout.good).Value
abbrev goodReady := BLSExtractorFrame.ready layout.good
abbrev badReady := BLSExtractorFrame.signatureReady layout.bad
def hashInput (value : HashInput layout) : layout.good.input.Value :=
  (productView layout.good.input (BLSExtractorFrame.context layout.good) value).1
def hashValue (value : HashInput layout) (answer : layout.rows.good.state.Value) : HashOutput layout :=
  (productView layout.rows.good.state (BLSExtractorFrame.context layout.good)).symm
    (answer, (productView layout.good.input (BLSExtractorFrame.context layout.good) value).2)
def hashReady (value : HashInput layout) : Prop :=
  value.val.1.2.length + value.val.1.1.1.length + value.val.2.2.1.length + 1 ≤ layout.rows.accumulation.cache.capacityPred + 1
def afterHashReady (value : HashOutput layout) : Prop :=
  value.val.1.2.length + value.val.2.2.1.length + 1 ≤ layout.rows.accumulation.cache.capacityPred + 1
theorem prepare_preserves (value : GoodInput layout) (ready : goodReady layout value) :
    hashReady layout (BLSExtractorFrame.prepareValue layout.good value) := ready
theorem hash_evaluation_ready (value : HashInput layout) (ready : hashReady layout value) : layout.good.ready (hashInput layout value) := by
  change value.val.1.2.length + value.val.1.1.1.length ≤ layout.rows.accumulation.cache.capacityPred + 1
  unfold hashReady at ready
  omega

end Layout

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {G : Type}
    [DecidableEq (key.Value base)] [Zero (val.Value base)] [Mul (val.Value base)] [Add (val.Value base)]
    (layout : BLSTokens.Layouts w (key.Value base) G (val.Value base))
    (zeroValid : layout.rows.accumulation.cache.value.valid 0)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (mul : Implementation .unit layout.rows.accumulation.arithmetic.pair layout.rows.accumulation.cache.value (fun value => value.1 * value.2))
    (add : Implementation .unit layout.rows.accumulation.arithmetic.pair layout.rows.accumulation.cache.value (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w)

variable {I : Type} {spec : OracleSpec I}
def hashCode (port : Interactive.Port w spec) (scalar : Interactive.Code w) : Interactive.Code w :=
  let body := BLSTokens.goodCode layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalar
  Interactive.retain body (Interactive.savedBuffer port body) layout.good.input.representation.encoding.words
    layout.rows.good.state.representation.encoding.words (BLSExtractorFrame.context layout.good).representation.encoding.words
def hashDenote (source : OracleComp spec layout.rows.accumulation.cache.value.Value) (value : HashInput layout) : OracleComp spec (HashOutput layout) :=
  hashValue layout value <$> BLSTokens.goodDenote layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers source (hashInput layout value)

theorem hash_preserves (source : OracleComp spec layout.rows.accumulation.cache.value.Value)
    (value : HashInput layout) (ready : hashReady layout value) (answer : HashOutput layout)
    (reached : answer ∈ support (hashDenote layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve source value)) :
    afterHashReady layout answer := by
  simp only [hashDenote, support_map, Set.mem_image] at reached
  obtain ⟨result, supported, rfl⟩ := reached
  have room := TokenEvaluation.remaining_room layout.good (BLSTokens.zero layout zeroValid) (BLSTokens.zero layout zeroValid)
    (BLSTokens.zero layout zeroValid) P comparison correct
    (BLSPrivateAccumulate.goodUpdate layout.rows.accumulation mul add mulBuffers reserve)
    (BLSPrivateAccumulate.goodUpdate_buffers layout.rows.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.good_reserve layout.rows.accumulation reserve) source (hashInput layout value)
    (value.val.2.2.1.length + 1) (by
      change value.val.1.2.length + value.val.1.1.1.length + (value.val.2.2.1.length + 1) ≤ layout.rows.accumulation.cache.capacityPred + 1
      unfold hashReady at ready
      omega) result supported
  change result.val.2.length + (value.val.2.2.1.length + 1) ≤ layout.rows.accumulation.cache.capacityPred + 1 at room
  change result.val.2.length + value.val.2.2.1.length + 1 ≤ _
  omega

variable (port : Interactive.Port w spec) {source : OracleComp spec layout.rows.accumulation.cache.value.Value} {scalar : Interactive.Code w}
    (scalarCorrect : Interactive.Refines port .unit layout.rows.accumulation.cache.lookup.unit.representation
      layout.rows.accumulation.cache.value.representation (fun _ => source) scalar)
include scalarCorrect in
theorem hash_refines : Interactive.RefinesOn (hashReady layout) port .unit (BLSExtractorFrame.prepared layout.good).representation
    (BLSExtractorFrame.returned layout.good).representation
    (hashDenote layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve source)
    (hashCode layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar) := by
  have retained := (BLSTokens.good_refines layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalarCorrect).retain
    (by decide) (BLSExtractorFrame.context layout.good).representation layout.rows.accumulation.cache.wordFits
    (BLSExtractorFrame.prepared layout.good).representation.fits (BLSExtractorFrame.returned layout.good).representation.fits
  have viewed := (retained.viewInput (BLSExtractorFrame.prepared layout.good).representation
    (productView layout.good.input (BLSExtractorFrame.context layout.good)) (fun _ => rfl)).viewOutput
    (BLSExtractorFrame.returned layout.good).representation
    (productView layout.rows.good.state (BLSExtractorFrame.context layout.good)).symm (fun _ => rfl)
  intro tape value ready before holds
  have result := viewed tape value (hash_evaluation_ready layout value ready) before holds
  convert result using 1
  · rfl
  · exact PFunctor.FreeM.comp_map
      (productView layout.rows.good.state (BLSExtractorFrame.context layout.good)).symm
      (fun answer => (answer, (productView layout.good.input (BLSExtractorFrame.context layout.good) value).2)) _
  · rfl
end Signatures.Runtime.CaliperBackend.BLSExtractor
