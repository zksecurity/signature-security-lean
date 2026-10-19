import Signatures.Runtime.Caliper.BLSCallerFinishLayout
import Signatures.Runtime.Caliper.InteractiveInvariantViews
import Signatures.Runtime.Caliper.EncodedConstant

/-! The caller's return/cutoff tag is inspected by executed dispatch. Successful
returns route to extraction and then copy out the scalar; cutoffs construct an
explicit fallback. The generic composition lemmas are instantiated with the
constructed BLS extractors, rather than assumed complete reduction routines. -/
namespace Signatures.Runtime.CaliperBackend.BLSCallerFinish
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {M G F R C P : Type}
    (layout : TokenEvaluation.Layouts w M G F R)
    (config : Representation w C) (pending : Representation w P)
    (fits : 1 + max (BLSExtractorFrame.forgery layout).representation.encoding.words pending.encoding.words +
      config.encoding.words + (BLSExtractorFrame.store layout).representation.encoding.words < 2 ^ w)

abbrev result := CacheScalarResult.output layout.rows.accumulation
def project : Realizer .unit (result layout).representation layout.rows.accumulation.coefficient.representation
    (fun value => ⟨value.val.1, value.property.1⟩) :=
  (Implementation.first (cost := .unit) (by decide) layout.rows.accumulation.coefficient
    layout.rows.accumulation.cache.lookup.table layout.rows.accumulation.cache.wordFits (result layout).representation.fits).program
def fallback (default : layout.rows.accumulation.coefficient.Value) :
    Realizer .unit (cutoff layout config pending fits) layout.rows.accumulation.coefficient.representation (fun _ => default) :=
  Assembly.realizer .unit (by decide) _ _ _
    ((layout.rows.accumulation.coefficient.representation.encoding.encode default).map Assembly.Operand.literal)
    layout.rows.accumulation.cache.wordFits
    (by simp only [List.length_map, Encoding.encode_length])
    (by intro operand member; obtain ⟨word, _, rfl⟩ := List.mem_map.mp member; trivial)
    (by intro value state represented operand member; obtain ⟨word, _, rfl⟩ := List.mem_map.mp member; trivial)
    (by intro value state represented; simp only [Assembly.values, List.map_map]; exact List.map_id _)

def successCode (extractor : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (route layout config pending fits).code)
    (.seq extractor (.compute (project layout).code))
def code (default : layout.rows.accumulation.coefficient.Value) (extractor : Interactive.Code w) : Interactive.Code w :=
  Interactive.dispatch (successCode layout config pending fits extractor) (.compute (fallback layout config pending fits default).code)
    (returned layout config pending fits).encoding.words (cutoff layout config pending fits).encoding.words

variable {I : Type} {spec : OracleSpec I}
def success (extract : (BLSExtractorFrame.input layout).Value → OracleComp spec (result layout).Value)
    (value : Forgery layout × (C × Store layout)) : OracleComp spec layout.rows.accumulation.coefficient.Value :=
  (fun answer => ⟨answer.val.1, answer.property.1⟩) <$> extract (extractInput layout value)
def denote (default : layout.rows.accumulation.coefficient.Value)
    (extract : (BLSExtractorFrame.input layout).Value → OracleComp spec (result layout).Value)
    (value : Packet (P := P) (C := C) layout) : OracleComp spec layout.rows.accumulation.coefficient.Value :=
  match value.1 with
  | .inl forgery => success layout extract (forgery, value.2)
  | .inr _ => pure default
def ready (admitted : (BLSExtractorFrame.input layout).Value → Prop) (value : Packet (P := P) (C := C) layout) : Prop :=
  match value.1 with
  | .inl forgery => admitted (extractInput layout (forgery, value.2))
  | .inr _ => True

variable (port : Interactive.Port w spec)
    {admitted : (BLSExtractorFrame.input layout).Value → Prop}
    {extract : (BLSExtractorFrame.input layout).Value → OracleComp spec (result layout).Value}
    {extractor : Interactive.Code w}
    (extractCorrect : Interactive.RefinesOn admitted port .unit (BLSExtractorFrame.input layout).representation
      (result layout).representation extract extractor)

include extractCorrect in
theorem success_refines : Interactive.RefinesOn (fun value => admitted (extractInput layout value)) port .unit
    (returned layout config pending fits) layout.rows.accumulation.coefficient.representation
    (success layout extract) (successCode layout config pending fits extractor) := by
  have projected := extractCorrect.seq
    ((Interactive.Refines.compute port .unit (project layout)).on (fun _ => True)) (by intros; trivial)
  have routed := ((Interactive.Refines.compute port .unit (route layout config pending fits)).on
    (fun value => admitted (extractInput layout value))).seq projected (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact valid)
  convert routed using 1
  · funext value
    simp only [pure_bind, bind_pure_comp]
    rfl
  · rfl

include extractCorrect in
theorem refines (default : layout.rows.accumulation.coefficient.Value) :
    Interactive.RefinesOn (ready layout admitted) port .unit (input layout config pending fits)
      layout.rows.accumulation.coefficient.representation (denote layout default extract)
      (code layout config pending fits default extractor) := by
  have branches := Interactive.RefinesOn.dispatch (returned layout config pending fits) (cutoff layout config pending fits)
    layout.rows.accumulation.coefficient.representation (success_refines layout config pending fits port extractCorrect)
    ((Interactive.Refines.compute port .unit (fallback layout config pending fits default)).on (fun _ => True))
    (width_pos layout.rows.accumulation.cache.wordFits) (choice_fits layout config pending fits)
  have viewed := branches.viewInput (input layout config pending fits) SumContext.view (input_bytes layout config pending fits)
  convert viewed using 1
  · funext value; rcases value with ⟨forgery | next, stored⟩ <;> rfl
  · funext value; rcases value with ⟨forgery | next, stored⟩ <;> rfl
  · rfl

end Signatures.Runtime.CaliperBackend.BLSCallerFinish
