import Signatures.Runtime.Caliper.TokenEvaluationSource

/-! Stored code, names and all visited memory for the combined transcript
evaluator. The resource theorem refers to the same source-supported result and
execution as the refinement theorem. -/
namespace Signatures.Runtime.CaliperBackend.TokenEvaluation
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {G F : Type}
    [DecidableEq (key.Value base)] (layout : Layouts w (key.Value base) G F (val.Value base))
    (coefficientDefault : layout.rows.accumulation.coefficient.Value)
    (initial default : layout.rows.accumulation.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.rows.accumulation.combine layout.rows.accumulation.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec) (draw : Interactive.Code w)

theorem names {drawNames updateNames : Nat} (drawBound : WordIO.NamesBound (draw.lower port) drawNames)
    (updateBound : NamesAccounted update.program.code updateNames) :
    WordIO.NamesAccounted ((code layout coefficientDefault initial default P comparison correct update updateBuffers reserve port draw).lower port)
      (max (max 5 drawNames) updateNames) :=
  (WordIO.NamesAccounted.compute (prepare_names layout coefficientDefault initial _)).seq
    (RowFold.names layout.rows default P comparison correct update updateBuffers reserve port layout.capacity draw drawBound updateBound)
theorem descriptionFits (drawFits : (draw.lower port).DescriptionFits) {drawNames : Nat}
    (drawBound : WordIO.NamesBound (draw.lower port) drawNames) (namesFit : drawNames + 2 < 2 ^ w) :
    ((code layout coefficientDefault initial default P comparison correct update updateBuffers reserve port draw).lower port).DescriptionFits :=
  WordIO.Code.DescriptionFits.seq layout.rows.accumulation.cache.wordFits
    (.compute (prepare layout coefficientDefault initial).program.description_fits)
    (RowFold.descriptionFits layout.rows default P comparison correct update updateBuffers reserve port layout.capacity
      layout.countFits layout.foldFits draw drawFits drawBound namesFit)

theorem resources {source : OracleComp spec layout.rows.accumulation.cache.value.Value}
    (drawCorrect : Interactive.Refines port .unit layout.rows.accumulation.cache.lookup.unit.representation
      layout.rows.accumulation.cache.value.representation (fun _ => source) draw)
    {drawTime drawWords updateTime updateWords drawNames updateNames : Nat}
    (drawTimeBound : Interactive.TimeBound port .unit layout.rows.accumulation.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords) (updateBound : update.BoundedBy updateTime updateWords)
    (drawNamesBound : WordIO.NamesBound (draw.lower port) drawNames) (updateNamesBound : NamesAccounted update.program.code updateNames)
    (tape : RandomTape w) (value : layout.input.Value) (ready : layout.ready value) (before : State w)
    (holds : layout.input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout coefficientDefault initial default P comparison correct update updateBuffers reserve port draw).execute port .unit tape before)) :
    finished.time ≤ timeBudget layout drawTime updateTime ∧
    ∃ answer ∈ support (denote layout coefficientDefault initial default P comparison correct update updateBuffers reserve source value),
      layout.rows.state.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape ((code layout coefficientDefault initial default P comparison correct update updateBuffers reserve port draw).lower port)
          before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers ((code layout coefficientDefault initial default P comparison correct update updateBuffers reserve port draw).lower port).registerSlots) ∧
          between.SupportBound (max buffers ((code layout coefficientDefault initial default P comparison correct update updateBuffers reserve port draw).lower port).memBound) ∧ between.WellFormed ∧
          (((code layout coefficientDefault initial default P comparison correct update updateBuffers reserve port draw).lower port).staticWords registers buffers : Int) +
            between.liveMem (max buffers ((code layout coefficientDefault initial default P comparison correct update updateBuffers reserve port draw).lower port).memBound) ≤
              5 * codeBudget layout drawWords updateWords + 4 * max (max 5 drawNames) updateNames + registers + 3 * buffers +
                before.liveMem buffers + timeBudget layout drawTime updateTime := by
  have refined := refines layout coefficientDefault initial default P comparison correct update updateBuffers reserve port drawCorrect
  have bounded := time_bound layout coefficientDefault initial default P comparison correct update updateBuffers reserve port drawCorrect drawTimeBound updateBound
  have stored := code_bound layout coefficientDefault initial default P comparison correct update updateBuffers reserve port draw drawWordsBound updateBound
  have accounted := names layout coefficientDefault initial default P comparison correct update updateBuffers reserve port draw drawNamesBound updateNamesBound
  obtain ⟨elapsed, answer, supported, output, execution, memory⟩ := refined.resources bounded stored accounted tape value ready before holds
    registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨regs, bufs, wf, total⟩ := memory between visited
  exact ⟨regs, bufs, wf, by omega⟩
end Signatures.Runtime.CaliperBackend.TokenEvaluation
