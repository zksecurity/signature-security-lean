import Signatures.Runtime.Caliper.WeightedSignatureTailBounds

/-! Scratch names and complete memory for the composed signing/target tail.
All bounds concern the same actual execution and source-supported output. -/
namespace Signatures.Runtime.CaliperBackend.WeightedSignatureTail
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M G F : Type}
    [DecidableEq (key.Value base)] (layout : WeightedExtraction.Layouts w (key.Value base) M G F (val.Value base))
    (coefficientDefault : layout.rows.accumulation.coefficient.Value)
    (zero default : layout.rows.accumulation.cache.value.Value)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit layout.rows.weighted.message
      (GeneratedWeighted.terms layout.rows.accumulation layout.terms layout.termCountFits layout.termStorageFits) generate)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.rows.accumulation.combine layout.rows.accumulation.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    {calculate : F × (val.Value base × val.Value base) → F}
    (extract : Implementation .unit layout.rows.accumulation.combine layout.rows.accumulation.coefficient calculate)
    {extractSlots : Nat} (extractBuffers : extract.program.code.memBound ≤ extractSlots)
    (extractReserve : extractSlots + 2 < 2 ^ w)
    {I : Type} {spec : OracleSpec I}

variable (port : Interactive.Port w spec) (draw : Interactive.Code w)

theorem names {generatorNames drawNames updateNames extractNames : Nat}
    (generatorBound : NamesAccounted generator.program.code generatorNames)
    (drawBound : WordIO.NamesBound (draw.lower port) drawNames)
    (updateBound : NamesAccounted update.program.code updateNames)
    (extractBound : NamesAccounted extract.program.code extractNames) :
    WordIO.NamesAccounted ((code layout coefficientDefault zero default generator P comparison correct
      update updateBuffers reserve extract extractBuffers extractReserve port draw).lower port)
      (max generatorNames (max (max 5 drawNames) (max updateNames extractNames))) := by
  have core := WeightedExtraction.names layout coefficientDefault zero zero default generator
    P comparison correct update updateBuffers reserve port draw generatorBound drawBound updateBound
  have target := WeightedTarget.names layout.rows.weighted zero layout.terms layout.termCountFits layout.termStorageFits
    generator default P comparison correct update updateBuffers reserve extract extractBuffers extractReserve
    port draw generatorBound drawBound updateBound extractBound
  exact (Interactive.retain_names port (core.mono (by omega)) _ _ _).seq
    ((WordIO.NamesAccounted.compute (route_names layout _)).seq target)

theorem buffers {generatorSlots drawSlots : Nat}
    (generatorBound : generator.program.code.memBound ≤ generatorSlots)
    (drawBound : (draw.lower port).memBound ≤ drawSlots) :
    ((code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve port draw).lower port).memBound ≤
      max (max 14 (max (generatorSlots + 4) (max (drawSlots + 6) (slots + 5)))) (max 4 extractSlots + 1) := by
  have core := WeightedExtraction.buffers layout coefficientDefault zero zero default generator
    P comparison correct update updateBuffers reserve port draw generatorBound drawBound
  have retained := Interactive.retain_buffers port
    (WeightedExtraction.code layout coefficientDefault zero zero default generator P comparison correct update updateBuffers reserve port draw)
    layout.input.representation.encoding.words layout.rows.state.representation.encoding.words
    (context layout).representation.encoding.words
  change ((evaluationCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve port draw).lower port).memBound ≤ _ at retained
  have first : ((evaluationCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve port draw).lower port).memBound ≤
      max 14 (max (generatorSlots + 4) (max (drawSlots + 6) (slots + 5))) := by omega
  have target := WeightedTarget.buffers layout.rows.weighted zero layout.terms layout.termCountFits layout.termStorageFits
    generator default P comparison correct update updateBuffers reserve extract extractBuffers extractReserve
    port draw generatorBound drawBound
  have grow : max 12 (max (generatorSlots + 2) (max (drawSlots + 4) (slots + 3))) ≤
      max 14 (max (generatorSlots + 4) (max (drawSlots + 6) (slots + 5))) := by omega
  have routed : (route layout).code.memBound ≤ max 14 (max (generatorSlots + 4) (max (drawSlots + 6) (slots + 5))) :=
    (route_buffers layout).trans ((by decide : 2 ≤ 14).trans (Nat.le_max_left _ _))
  change max
    ((evaluationCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve port draw).lower port).memBound
    (max (route layout).code.memBound
      ((WeightedTarget.code layout.rows.weighted zero layout.terms layout.termCountFits layout.termStorageFits
        generator default P comparison correct update updateBuffers reserve extract extractBuffers extractReserve port draw).lower port).memBound) ≤ _
  exact max_le (first.trans (Nat.le_max_left _ _))
    (max_le (routed.trans (Nat.le_max_left _ _)) (target.trans (max_le_max grow le_rfl)))

theorem descriptionFits {generatorSlots drawSlots : Nat}
    (generatorBound : generator.program.code.memBound ≤ generatorSlots) (generatorReserve : generatorSlots + 3 < 2 ^ w)
    (drawFits : (draw.lower port).DescriptionFits)
    (drawBound : WordIO.NamesBound (draw.lower port) drawSlots) (drawReserve : drawSlots + 5 < 2 ^ w)
    (updateReserve : slots + 4 < 2 ^ w) :
    ((code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve port draw).lower port).DescriptionFits := by
  have core := WeightedExtraction.descriptionFits layout coefficientDefault zero zero default generator
    P comparison correct update updateBuffers reserve port draw generatorBound (by omega) drawFits drawBound (by omega) (by omega)
  have saved := WeightedExtraction.savedNameFits layout coefficientDefault zero zero default generator
    P comparison correct update updateBuffers reserve port draw generatorBound generatorReserve drawBound drawReserve updateReserve
  exact .seq layout.rows.accumulation.cache.wordFits
    (Interactive.retain_descriptionFits port _ _ _ _ _ layout.rows.accumulation.cache.wordFits core saved
      layout.input.representation.fits (context layout).representation.fits (returned layout).fits)
    (.seq layout.rows.accumulation.cache.wordFits (.compute (route layout).description_fits)
      (WeightedTarget.descriptionFits layout.rows.weighted zero layout.terms layout.termCountFits layout.termStorageFits
        generator default P comparison correct update updateBuffers reserve extract extractBuffers extractReserve
        port draw generatorBound (by omega) drawFits drawBound (by omega)))

theorem resources {source : OracleComp spec layout.rows.accumulation.cache.value.Value}
    (drawCorrect : Interactive.Refines port .unit layout.rows.accumulation.cache.lookup.unit.representation
      layout.rows.accumulation.cache.value.representation (fun _ => source) draw)
    {generatorTime generatorWords drawTime drawWords updateTime updateWords extractTime extractWords
      generatorNames drawNames updateNames extractNames : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawTimeBound : Interactive.TimeBound port .unit layout.rows.accumulation.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords)
    (updateBound : update.BoundedBy updateTime updateWords) (extractBound : extract.BoundedBy extractTime extractWords)
    (generatorNamesBound : NamesAccounted generator.program.code generatorNames)
    (drawNamesBound : WordIO.NamesBound (draw.lower port) drawNames)
    (updateNamesBound : NamesAccounted update.program.code updateNames)
    (extractNamesBound : NamesAccounted extract.program.code extractNames)
    (tape : RandomTape w) (value : Input layout) (admitted : ready layout value)
    (before : State w) (holds : (input layout).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout coefficientDefault zero default generator P comparison correct
      update updateBuffers reserve extract extractBuffers extractReserve port draw).execute port .unit tape before)) :
    finished.time ≤ timeBudget layout generatorTime drawTime updateTime extractTime ∧
    ∃ answer ∈ support (denote layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
        extract extractBuffers extractReserve source value),
      (output layout).representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape
          ((code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
            extract extractBuffers extractReserve port draw).lower port)
          before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers
            ((code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
              extract extractBuffers extractReserve port draw).lower port).registerSlots) ∧
          between.SupportBound (max buffers
            ((code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
              extract extractBuffers extractReserve port draw).lower port).memBound) ∧ between.WellFormed ∧
          (((code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
              extract extractBuffers extractReserve port draw).lower port).staticWords registers buffers : Int) +
            between.liveMem (max buffers
              ((code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
                extract extractBuffers extractReserve port draw).lower port).memBound) ≤
              5 * codeBudget layout generatorWords drawWords updateWords extractWords +
                4 * max generatorNames (max (max 5 drawNames) (max updateNames extractNames)) + registers + 3 * buffers +
                before.liveMem buffers + timeBudget layout generatorTime drawTime updateTime extractTime := by
  have refined := refines layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve port drawCorrect
  have bounded := time_bound layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve port drawCorrect generatorBound drawTimeBound updateBound extractBound
  have stored := code_bound layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve port generatorBound updateBound extractBound draw drawWordsBound
  have accounted := names layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve port draw generatorNamesBound drawNamesBound updateNamesBound extractNamesBound
  obtain ⟨elapsed, answer, supported, represented, execution, memory⟩ :=
    refined.resources bounded stored accounted tape value admitted before holds
      registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, represented, execution, ?_⟩
  intro between visited
  obtain ⟨regs, bufs, wf, total⟩ := memory between visited
  exact ⟨regs, bufs, wf, by omega⟩

end Signatures.Runtime.CaliperBackend.WeightedSignatureTail
