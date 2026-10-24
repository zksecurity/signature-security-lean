import Proofs.Runtime.Caliper.WeightedExtractionSource

/-! Stored code, names and all visited memory for the combined transcript
evaluator. The resource theorem refers to the same source-supported result and
execution as the refinement theorem. -/
namespace Signatures.Runtime.CaliperBackend.WeightedExtraction
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M G F : Type}
    [DecidableEq (key.Value base)] (layout : Layouts w (key.Value base) M G F (val.Value base))
    (coefficientDefault : layout.rows.accumulation.coefficient.Value)
    (zero initial default : layout.rows.accumulation.cache.value.Value)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit layout.rows.weighted.message
      (GeneratedWeighted.terms layout.rows.accumulation layout.terms layout.termCountFits layout.termStorageFits) generate)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.rows.accumulation.combine layout.rows.accumulation.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    {I : Type} {spec : OracleSpec I}
    (port : Interactive.Port w spec) (draw : Interactive.Code w)

theorem names {generatorNames drawNames updateNames : Nat}
    (generatorBound : NamesAccounted generator.program.code generatorNames) (drawBound : WordIO.NamesBound (draw.lower port) drawNames)
    (updateBound : NamesAccounted update.program.code updateNames) :
    WordIO.NamesAccounted ((code layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve port draw).lower port)
      (max generatorNames (max (max 5 drawNames) updateNames)) :=
  (WordIO.NamesAccounted.compute (prepare_names layout coefficientDefault initial _)).seq
    (WeightedTokenFold.names layout.rows zero layout.terms layout.termCountFits layout.termStorageFits generator default P comparison correct update updateBuffers reserve port layout.capacity draw generatorBound drawBound updateBound)
theorem descriptionFits {generatorSlots drawSlots : Nat}
    (generatorBound : generator.program.code.memBound ≤ generatorSlots) (generatorReserve : generatorSlots + 2 < 2 ^ w)
    (drawFits : (draw.lower port).DescriptionFits)
    (drawBound : WordIO.NamesBound (draw.lower port) drawSlots) (drawReserve : drawSlots + 4 < 2 ^ w)
    (updateReserve : slots + 3 < 2 ^ w) :
    ((code layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve port draw).lower port).DescriptionFits :=
  .seq layout.rows.accumulation.cache.wordFits (.compute (prepare layout coefficientDefault initial).program.description_fits)
    (WeightedTokenFold.descriptionFits layout.rows zero layout.terms layout.termCountFits layout.termStorageFits generator default
      P comparison correct update updateBuffers reserve port layout.capacity layout.countFits layout.foldFits draw
      generatorBound generatorReserve drawFits drawBound drawReserve updateReserve)

theorem resources {source : OracleComp spec layout.rows.accumulation.cache.value.Value}
    (drawCorrect : Interactive.Refines port .unit layout.rows.accumulation.cache.lookup.unit.representation
      layout.rows.accumulation.cache.value.representation (fun _ => source) draw)
    {generatorTime generatorWords drawTime drawWords updateTime updateWords generatorNames drawNames updateNames : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawTimeBound : Interactive.TimeBound port .unit layout.rows.accumulation.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords) (updateBound : update.BoundedBy updateTime updateWords)
    (generatorNamesBound : NamesAccounted generator.program.code generatorNames)
    (drawNamesBound : WordIO.NamesBound (draw.lower port) drawNames) (updateNamesBound : NamesAccounted update.program.code updateNames)
    (tape : RandomTape w) (value : layout.input.Value) (ready : layout.ready value) (before : State w)
    (holds : layout.input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve port draw).execute port .unit tape before)) :
    finished.time ≤ timeBudget layout generatorTime drawTime updateTime ∧
    ∃ answer ∈ support (denote layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve source value),
      layout.rows.state.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape ((code layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve port draw).lower port)
          before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers ((code layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve port draw).lower port).registerSlots) ∧
          between.SupportBound (max buffers ((code layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve port draw).lower port).memBound) ∧ between.WellFormed ∧
          (((code layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve port draw).lower port).staticWords registers buffers : Int) +
            between.liveMem (max buffers ((code layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve port draw).lower port).memBound) ≤
              5 * codeBudget layout generatorWords drawWords updateWords + 4 * max generatorNames (max (max 5 drawNames) updateNames) + registers + 3 * buffers +
                before.liveMem buffers + timeBudget layout generatorTime drawTime updateTime := by
  have refined := refines layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve port drawCorrect
  have bounded := time_bound layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve port drawCorrect generatorBound drawTimeBound updateBound
  have stored := code_bound layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve port draw generatorBound drawWordsBound updateBound
  have accounted := names layout coefficientDefault zero initial default generator P comparison correct update updateBuffers reserve port draw generatorNamesBound drawNamesBound updateNamesBound
  obtain ⟨elapsed, answer, supported, output, execution, memory⟩ := refined.resources bounded stored accounted tape value ready before holds
    registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨regs, bufs, wf, total⟩ := memory between visited
  exact ⟨regs, bufs, wf, by omega⟩
end Signatures.Runtime.CaliperBackend.WeightedExtraction
