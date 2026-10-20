import Signatures.Runtime.Caliper.SchnorrAGMCallerFinish
import Signatures.Runtime.Caliper.InteractiveAcceptance

/-! Derived overhead of caller termination: tag and padded-payload copies,
configuration removal, final scalar projection, and the literal cutoff result.
Both branches are charged in stored code, including the unreachable cutoff
branch when the source machine has a proved query bound. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerFinish
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS : Nat} {M F G P : Type}
    (layout : HashDispatch.Layouts w M F G qH qS) (pending : Representation w P)
    (fits : 1 + max (forgery layout).representation.encoding.words pending.encoding.words +
      layout.hash.scheme.store.representation.encoding.words < 2 ^ w)

theorem project_time (value) : (project layout).time value ≤ 8 * layout.hash.scheme.scalar.representation.encoding.words :=
  (Implementation.first_boundedBy _ _ layout.hash.scheme.wordFits (Read.output layout.hash.scheme).representation.fits).time_le value
theorem project_words : descriptionWords (project layout).code ≤ 26 * layout.hash.scheme.scalar.representation.encoding.words + 14 :=
  (Implementation.first_boundedBy _ _ layout.hash.scheme.wordFits (Read.output layout.hash.scheme).representation.fits).code_le
theorem project_names (slots : Nat) : NamesAccounted (project layout).code slots := selectSlice_names _ _ _
theorem fallback_time (zero : layout.hash.scheme.scalar.Value) (value) :
    (fallback layout pending fits zero).time value ≤ 8 * layout.hash.scheme.scalar.representation.encoding.words := by
  have bound := Assembly.code_time_unit_le ((layout.hash.scheme.scalar.representation.encoding.encode zero).map Assembly.Operand.literal)
  change (Assembly.code ((layout.hash.scheme.scalar.representation.encoding.encode zero).map Assembly.Operand.literal)).staticTime .unit ≤ _
  simpa only [List.length_map, Encoding.encode_length] using bound
theorem fallback_words (zero : layout.hash.scheme.scalar.Value) :
    descriptionWords (fallback layout pending fits zero).code ≤ 26 * layout.hash.scheme.scalar.representation.encoding.words + 14 := by
  have bound := Assembly.code_descriptionWords_le ((layout.hash.scheme.scalar.representation.encoding.encode zero).map Assembly.Operand.literal)
  change descriptionWords (Assembly.code ((layout.hash.scheme.scalar.representation.encoding.encode zero).map Assembly.Operand.literal)) ≤ _
  simpa only [List.length_map, Encoding.encode_length] using bound
theorem fallback_names (zero : layout.hash.scheme.scalar.Value) (slots : Nat) :
    NamesAccounted (fallback layout pending fits zero).code slots :=
  Assembly.code_namesAccounted _ slots (by
    intro operand member; obtain ⟨word, _, rfl⟩ := List.mem_map.mp member; trivial)

variable [DecidableEq M] [DecidableEq G]

def timeBudget (extractTime : Nat) : Nat := extractTime + 8 * (Extraction.input layout).representation.encoding.words +
  8 * layout.hash.scheme.scalar.representation.encoding.words + 8 * (returned layout pending fits).encoding.words + 2
def codeBudget (extractWords : Nat) : Nat := extractWords + 26 * (Extraction.input layout).representation.encoding.words +
  52 * layout.hash.scheme.scalar.representation.encoding.words +
  26 * (returned layout pending fits).encoding.words + 26 * (cutoff layout pending fits).encoding.words + 87

variable {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    {extract : (Extraction.input layout).Value → OracleComp spec (Read.output layout.hash.scheme).Value}
    {extractor : Interactive.Code w}
    (extractCorrect : Interactive.Refines port .unit (Extraction.input layout).representation
      (Read.output layout.hash.scheme).representation extract extractor)
    {extractTime extractWords slots : Nat}
    (extractBound : Interactive.TimeBound port .unit (Extraction.input layout).representation extractor extractTime)
    (extractStored : (extractor.lower port).descriptionWords ≤ extractWords)
    (extractNames : WordIO.NamesAccounted (extractor.lower port) slots)

include extractCorrect extractBound in
theorem time_bound (zero : layout.hash.scheme.scalar.Value) :
    Interactive.TimeBoundOn (ready layout) port .unit (input layout pending fits)
      (code layout pending fits zero extractor) (timeBudget layout pending fits extractTime) := by
  have projected := extractBound.seq extractCorrect
    (Interactive.TimeBound.compute (port := port) (cost := .unit) (project layout) _ (project_time layout))
  have routed := (Interactive.TimeBound.compute (port := port) (cost := .unit) (route layout pending fits) _
    (route_time layout pending fits)).seq (Interactive.Refines.compute port .unit (route layout pending fits)) projected
  have admittedTime : Interactive.TimeBoundOn (admitted layout) port .unit (returned layout pending fits)
      (successCode layout pending fits extractor)
      (8 * (Extraction.input layout).representation.encoding.words + (extractTime + 8 * layout.hash.scheme.scalar.representation.encoding.words)) :=
    fun tape value valid before represented => routed tape ⟨value, valid⟩ before represented
  have branches := Interactive.TimeBoundOn.dispatch (returned layout pending fits) (cutoff layout pending fits) admittedTime
    ((Interactive.TimeBound.compute (port := port) (cost := .unit) (fallback layout pending fits zero) _
      (fallback_time layout pending fits zero)).on (fun _ => True))
    (width_pos layout.hash.scheme.wordFits) (choice_fits layout pending fits)
  have viewed := branches.viewInput (input layout pending fits) SumContext.view (input_bytes layout pending fits)
  have bound := viewed.mono (larger := timeBudget layout pending fits extractTime) (by
    simp only [Interactive.dispatchTime, selectSlice_staticTime, sliceWordTime, Caliper.CostModel.unit,
      WordIO.Costs.unit, timeBudget, (frame_sizes layout pending fits).2]
    omega)
  convert bound using 1
  · funext value; rcases value with ⟨forgery | next, stored⟩ <;> rfl
  · rfl

include extractStored in
theorem code_bound (zero : layout.hash.scheme.scalar.Value) :
    ((code layout pending fits zero extractor).lower port).descriptionWords ≤ codeBudget layout pending fits extractWords := by
  have routed := route_words layout pending fits
  have projected := project_words layout
  have stopped := fallback_words layout pending fits zero
  simp only [code, Interactive.dispatch_descriptionWords, successCode, Interactive.Code.lower,
    WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute, codeBudget]
  omega
include extractNames in
theorem names (zero : layout.hash.scheme.scalar.Value) :
    WordIO.NamesAccounted ((code layout pending fits zero extractor).lower port) slots :=
  Interactive.dispatch_names port («left» := successCode layout pending fits extractor)
    («right» := .compute (fallback layout pending fits zero).code)
    ((WordIO.NamesAccounted.compute (route_names layout pending fits slots)).seq
      (extractNames.seq (.compute (project_names layout slots))))
    (.compute (fallback_names layout pending fits zero slots)) _ _

theorem descriptionFits (zero : layout.hash.scheme.scalar.Value)
    (extractFits : (extractor.lower port).DescriptionFits) :
    ((code layout pending fits zero extractor).lower port).DescriptionFits :=
  Interactive.dispatch_descriptionFits port _ _ _ _ layout.hash.scheme.wordFits
    (.seq layout.hash.scheme.wordFits (.compute (route layout pending fits).description_fits)
      (.seq layout.hash.scheme.wordFits extractFits (.compute (project layout).description_fits)))
    (.compute (fallback layout pending fits zero).description_fits)
    (returned layout pending fits).fits (cutoff layout pending fits).fits

include extractCorrect extractBound extractStored extractNames in
theorem resources (zero : layout.hash.scheme.scalar.Value)
    (tape : RandomTape w) (value : Packet layout P) (valid : ready layout value)
    (before : State w) (holds : (input layout pending fits).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout pending fits zero extractor).execute port .unit tape before)) :
    finished.time ≤ timeBudget layout pending fits extractTime ∧
      ∃ answer ∈ support (denote layout zero extract value), layout.hash.scheme.scalar.representation.Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit tape ((code layout pending fits zero extractor).lower port)
          before finished.state finished.trace finished.time finished.net finished.peak,
          ∀ between, execution.Visits between →
            RegisterBound between (max registers ((code layout pending fits zero extractor).lower port).registerSlots) ∧
            between.SupportBound (max buffers ((code layout pending fits zero extractor).lower port).memBound) ∧ between.WellFormed ∧
            (((code layout pending fits zero extractor).lower port).staticWords registers buffers : Int) +
              between.liveMem (max buffers ((code layout pending fits zero extractor).lower port).memBound) ≤
                5 * codeBudget layout pending fits extractWords + 4 * slots + registers + 3 * buffers +
                  before.liveMem buffers + timeBudget layout pending fits extractTime := by
  have refined := refines layout pending fits port extractCorrect zero
  have bounded := time_bound layout pending fits port extractCorrect extractBound zero
  have stored := code_bound layout pending fits port extractStored zero
  have accounted := names layout pending fits port extractNames zero
  obtain ⟨elapsed, answer, supported, output, execution, memory⟩ := refined.resources bounded stored accounted
    tape value valid before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨regs, bufs, wf, total⟩ := memory between visited
  exact ⟨regs, bufs, wf, by omega⟩

end Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerFinish
