import Proofs.Runtime.Caliper.WeightedCallerFinish
import Proofs.Runtime.Caliper.InteractiveAcceptance

/-! Derived overhead of caller termination: tag and padded-payload copies,
configuration removal, final scalar projection, and the literal cutoff result.
Both branches are charged in stored code, including the unreachable cutoff
branch when the source machine has a proved query bound. -/
namespace Signatures.Runtime.CaliperBackend.WeightedCallerFinish
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {K M G F R C P : Type}
    (layout : WeightedExtractor.Layouts w K M G F R)
    (config : Representation w C) (pending : Representation w P)
    (fits : 1 + max layout.forgery.representation.encoding.words pending.encoding.words +
      config.encoding.words + layout.store.representation.encoding.words < 2 ^ w)

theorem project_time (value) : (project layout).time value ≤ 8 * layout.signing.rows.accumulation.coefficient.representation.encoding.words :=
  (Implementation.first_boundedBy _ _ layout.signing.rows.accumulation.cache.wordFits (result layout).representation.fits).time_le value
theorem project_words : descriptionWords (project layout).code ≤ 26 * layout.signing.rows.accumulation.coefficient.representation.encoding.words + 14 :=
  (Implementation.first_boundedBy _ _ layout.signing.rows.accumulation.cache.wordFits (result layout).representation.fits).code_le
theorem project_names (slots : Nat) : NamesAccounted (project layout).code slots := selectSlice_names _ _ _
theorem fallback_time (default : layout.signing.rows.accumulation.coefficient.Value) (value) :
    (fallback layout config pending fits default).time value ≤ 8 * layout.signing.rows.accumulation.coefficient.representation.encoding.words := by
  have bound := Assembly.code_time_unit_le ((layout.signing.rows.accumulation.coefficient.representation.encoding.encode default).map Assembly.Operand.literal)
  change (Assembly.code ((layout.signing.rows.accumulation.coefficient.representation.encoding.encode default).map Assembly.Operand.literal)).staticTime .unit ≤ _
  simpa only [List.length_map, Encoding.encode_length] using bound
theorem fallback_words (default : layout.signing.rows.accumulation.coefficient.Value) :
    descriptionWords (fallback layout config pending fits default).code ≤ 26 * layout.signing.rows.accumulation.coefficient.representation.encoding.words + 14 := by
  have bound := Assembly.code_descriptionWords_le ((layout.signing.rows.accumulation.coefficient.representation.encoding.encode default).map Assembly.Operand.literal)
  change descriptionWords (Assembly.code ((layout.signing.rows.accumulation.coefficient.representation.encoding.encode default).map Assembly.Operand.literal)) ≤ _
  simpa only [List.length_map, Encoding.encode_length] using bound
theorem fallback_names (default : layout.signing.rows.accumulation.coefficient.Value) (slots : Nat) :
    NamesAccounted (fallback layout config pending fits default).code slots :=
  Assembly.code_namesAccounted _ slots (by
    intro operand member; obtain ⟨word, _, rfl⟩ := List.mem_map.mp member; trivial)

def timeBudget (extractTime : Nat) : Nat := extractTime + 8 * layout.input.representation.encoding.words +
  8 * layout.signing.rows.accumulation.coefficient.representation.encoding.words + 8 * (returned layout config pending fits).encoding.words + 2
def codeBudget (extractWords : Nat) : Nat := extractWords + 26 * layout.input.representation.encoding.words +
  52 * layout.signing.rows.accumulation.coefficient.representation.encoding.words +
  26 * (returned layout config pending fits).encoding.words + 26 * (cutoff layout config pending fits).encoding.words + 87

variable {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    {admitted : layout.input.Value → Prop}
    {extract : layout.input.Value → OracleComp spec (result layout).Value}
    {extractor : Interactive.Code w}
    (extractCorrect : Interactive.RefinesOn admitted port .unit layout.input.representation
      (result layout).representation extract extractor)
    {extractTime extractWords slots : Nat}
    (extractBound : Interactive.TimeBoundOn admitted port .unit layout.input.representation extractor extractTime)
    (extractStored : (extractor.lower port).descriptionWords ≤ extractWords)
    (extractNames : WordIO.NamesAccounted (extractor.lower port) slots)

include extractCorrect extractBound in
theorem time_bound (default : layout.signing.rows.accumulation.coefficient.Value) :
    Interactive.TimeBoundOn (ready layout admitted) port .unit (input layout config pending fits)
      (code layout config pending fits default extractor) (timeBudget layout config pending fits extractTime) := by
  have projected := Interactive.TimeBoundOn.seq extractCorrect extractBound
    ((Interactive.TimeBound.compute (port := port) (cost := .unit) (project layout) _ (project_time layout)).on (fun _ => True))
    (by intros; trivial)
  have routed := Interactive.TimeBoundOn.seq
    ((Interactive.Refines.compute port .unit (route layout config pending fits)).on (fun value => admitted (extractInput layout value)))
    ((Interactive.TimeBound.compute (port := port) (cost := .unit) (route layout config pending fits) _ (route_time layout config pending fits)).on
      (fun value => admitted (extractInput layout value))) projected (by
        intro value valid answer reached
        simp only [support_pure, Set.mem_singleton_iff] at reached
        subst answer
        exact valid)
  have branches := Interactive.TimeBoundOn.dispatch (returned layout config pending fits) (cutoff layout config pending fits) routed
    ((Interactive.TimeBound.compute (port := port) (cost := .unit) (fallback layout config pending fits default) _
      (fallback_time layout config pending fits default)).on (fun _ => True))
    (width_pos layout.signing.rows.accumulation.cache.wordFits) (choice_fits layout config pending fits)
  have viewed := branches.viewInput (input layout config pending fits) SumContext.view (input_bytes layout config pending fits)
  have bound := viewed.mono (larger := timeBudget layout config pending fits extractTime) (by
    simp only [Interactive.dispatchTime, selectSlice_staticTime, sliceWordTime, CostModel.unit,
      WordIO.Costs.unit, timeBudget, (frame_sizes layout config pending fits).2]
    omega)
  convert bound using 1
  · funext value; rcases value with ⟨forgery | next, stored⟩ <;> rfl
  · rfl

include extractStored in
theorem code_bound (default : layout.signing.rows.accumulation.coefficient.Value) :
    ((code layout config pending fits default extractor).lower port).descriptionWords ≤ codeBudget layout config pending fits extractWords := by
  have routed := route_words layout config pending fits
  have projected := project_words layout
  have stopped := fallback_words layout config pending fits default
  simp only [code, Interactive.dispatch_descriptionWords, successCode, Interactive.Code.lower,
    WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute, codeBudget]
  omega
include extractNames in
theorem names (default : layout.signing.rows.accumulation.coefficient.Value) :
    WordIO.NamesAccounted ((code layout config pending fits default extractor).lower port) slots :=
  Interactive.dispatch_names port (left := successCode layout config pending fits extractor)
    (right := .compute (fallback layout config pending fits default).code)
    ((WordIO.NamesAccounted.compute (route_names layout config pending fits slots)).seq
      (extractNames.seq (.compute (project_names layout slots))))
    (.compute (fallback_names layout config pending fits default slots)) _ _

theorem descriptionFits (default : layout.signing.rows.accumulation.coefficient.Value)
    (extractFits : (extractor.lower port).DescriptionFits) :
    ((code layout config pending fits default extractor).lower port).DescriptionFits :=
  Interactive.dispatch_descriptionFits port _ _ _ _ layout.signing.rows.accumulation.cache.wordFits
    (.seq layout.signing.rows.accumulation.cache.wordFits (.compute (route layout config pending fits).description_fits)
      (.seq layout.signing.rows.accumulation.cache.wordFits extractFits (.compute (project layout).description_fits)))
    (.compute (fallback layout config pending fits default).description_fits)
    (returned layout config pending fits).fits (cutoff layout config pending fits).fits

include extractCorrect extractBound extractStored extractNames in
theorem resources (default : layout.signing.rows.accumulation.coefficient.Value)
    (tape : RandomTape w) (value : Packet (P := P) (C := C) layout) (valid : ready layout admitted value)
    (before : State w) (holds : (input layout config pending fits).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout config pending fits default extractor).execute port .unit tape before)) :
    finished.time ≤ timeBudget layout config pending fits extractTime ∧
      ∃ answer ∈ support (denote layout default extract value), layout.signing.rows.accumulation.coefficient.representation.Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit tape ((code layout config pending fits default extractor).lower port)
          before finished.state finished.trace finished.time finished.net finished.peak,
          ∀ between, execution.Visits between →
            RegisterBound between (max registers ((code layout config pending fits default extractor).lower port).registerSlots) ∧
            between.SupportBound (max buffers ((code layout config pending fits default extractor).lower port).memBound) ∧ between.WellFormed ∧
            (((code layout config pending fits default extractor).lower port).staticWords registers buffers : Int) +
              between.liveMem (max buffers ((code layout config pending fits default extractor).lower port).memBound) ≤
                5 * codeBudget layout config pending fits extractWords + 4 * slots + registers + 3 * buffers +
                  before.liveMem buffers + timeBudget layout config pending fits extractTime := by
  have refined := refines layout config pending fits port extractCorrect default
  have bounded := time_bound layout config pending fits port extractCorrect extractBound default
  have stored := code_bound layout config pending fits port extractStored default
  have accounted := names layout config pending fits port extractNames default
  obtain ⟨elapsed, answer, supported, output, execution, memory⟩ := refined.resources bounded stored accounted
    tape value valid before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨regs, bufs, wf, total⟩ := memory between visited
  exact ⟨regs, bufs, wf, by omega⟩

end Signatures.Runtime.CaliperBackend.WeightedCallerFinish
