import Proofs.Runtime.Caliper.WeightedExtractorBounds

/-! Complete extractor name/address and memory bounds use the same executed
program and source-supported result as the functional refinement. -/
namespace Signatures.Runtime.CaliperBackend.WeightedExtractor
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M G F : Type}
    [DecidableEq (key.Value base)] (layout : Layouts w (key.Value base) M G F (val.Value base))
    (coefficientDefault : layout.signing.rows.accumulation.coefficient.Value)
    (zero default : layout.signing.rows.accumulation.cache.value.Value)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit layout.signing.rows.weighted.message
      (GeneratedWeighted.terms layout.signing.rows.accumulation layout.signing.terms layout.signing.termCountFits layout.signing.termStorageFits) generate)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.signing.rows.accumulation.combine layout.signing.rows.accumulation.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    {calculate : F × (val.Value base × val.Value base) → F}
    (extract : Implementation .unit layout.signing.rows.accumulation.combine layout.signing.rows.accumulation.coefficient calculate)
    {extractSlots : Nat} (extractBuffers : extract.program.code.memBound ≤ extractSlots)
    (extractReserve : extractSlots + 2 < 2 ^ w)
    {numerator : F × val.Value base → F}
    (sum : Implementation .unit layout.numeratorInput layout.scalar numerator)
    {sumSlots : Nat} (sumBuffers : sum.program.code.memBound ≤ sumSlots) (sumReserve : sumSlots + 1 < 2 ^ w)
    {I : Type} {spec : OracleSpec I}

variable (port : Interactive.Port w spec) (draw : Interactive.Code w)

def nameBudget (generatorNames drawNames updateNames extractNames sumNames : Nat) : Nat :=
  generatorNames + drawNames + updateNames + extractNames + sumNames + 5

theorem names {generatorNames drawNames updateNames extractNames sumNames : Nat}
    (generatorBound : NamesAccounted generator.program.code generatorNames)
    (drawBound : WordIO.NamesBound (draw.lower port) drawNames)
    (updateBound : NamesAccounted update.program.code updateNames)
    (extractBound : NamesAccounted extract.program.code extractNames)
    (sumBound : NamesAccounted sum.program.code sumNames) :
    WordIO.NamesAccounted ((code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve sum sumBuffers sumReserve port draw).lower port)
      (nameBudget generatorNames drawNames updateNames extractNames sumNames) := by
  have hashes := TokenEvaluation.names layout.hashes coefficientDefault zero default P comparison correct
    update updateBuffers reserve port draw drawBound updateBound
  have tail := WeightedSignatureTail.names layout.signing coefficientDefault zero default generator P comparison correct
    update updateBuffers reserve extract extractBuffers extractReserve port draw generatorBound drawBound updateBound extractBound
  unfold nameBudget
  exact (WordIO.NamesAccounted.compute (prepare_names layout _)).seq
    ((Interactive.retain_names port (hashes.mono (by omega)) _ _ _).seq
      ((WordIO.NamesAccounted.compute (transition_names layout sum sumBuffers sumReserve (sumBound.mono (by omega)))).seq
        (tail.mono (by omega))))
theorem bad_names {generatorNames drawNames updateNames extractNames : Nat}
    (generatorBound : NamesAccounted generator.program.code generatorNames)
    (drawBound : WordIO.NamesBound (draw.lower port) drawNames)
    (updateBound : NamesAccounted update.program.code updateNames)
    (extractBound : NamesAccounted extract.program.code extractNames) :
    WordIO.NamesAccounted ((badCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve port draw).lower port)
      (max generatorNames (max (max 5 drawNames) (max updateNames extractNames))) :=
  (WordIO.NamesAccounted.compute (prepareBad_names layout _)).seq
    (WeightedSignatureTail.names layout.signing coefficientDefault zero default generator P comparison correct
      update updateBuffers reserve extract extractBuffers extractReserve port draw generatorBound drawBound updateBound extractBound)

theorem buffers {generatorSlots drawSlots : Nat}
    (generatorBound : generator.program.code.memBound ≤ generatorSlots) (drawBound : (draw.lower port).memBound ≤ drawSlots) :
    ((code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve sum sumBuffers sumReserve port draw).lower port).memBound ≤
        14 + generatorSlots + drawSlots + slots + extractSlots + sumSlots := by
  have hashed := TokenEvaluation.buffers layout.hashes coefficientDefault zero default P comparison correct
    update updateBuffers reserve port draw
  have held := Interactive.retain_buffers port
    (TokenEvaluation.code layout.hashes coefficientDefault zero default P comparison correct update updateBuffers reserve port draw)
    layout.hashes.input.representation.encoding.words layout.state.representation.encoding.words layout.context.representation.encoding.words
  change ((hashCode layout coefficientDefault zero default P comparison correct update updateBuffers reserve port draw).lower port).memBound ≤ _ at held
  have tail := WeightedSignatureTail.buffers layout.signing coefficientDefault zero default generator P comparison correct
    update updateBuffers reserve extract extractBuffers extractReserve port draw generatorBound drawBound
  have first := prepare_buffers layout
  have middle := transition_buffers layout sum sumBuffers sumReserve
  change max (prepare layout).code.memBound
    (max ((hashCode layout coefficientDefault zero default P comparison correct update updateBuffers reserve port draw).lower port).memBound
      (max (transition layout sum sumBuffers sumReserve).code.memBound
        ((WeightedSignatureTail.code layout.signing coefficientDefault zero default generator P comparison correct
          update updateBuffers reserve extract extractBuffers extractReserve port draw).lower port).memBound)) ≤ _
  apply max_le (by omega)
  apply max_le (by omega)
  exact max_le (by omega) (by omega)

theorem descriptionFits {generatorSlots drawSlots : Nat}
    (generatorBound : generator.program.code.memBound ≤ generatorSlots) (generatorReserve : generatorSlots + 3 < 2 ^ w)
    (drawFits : (draw.lower port).DescriptionFits) (drawBound : WordIO.NamesBound (draw.lower port) drawSlots)
    (drawReserve : drawSlots + 5 < 2 ^ w) (updateReserve : slots + 4 < 2 ^ w) :
    ((code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve sum sumBuffers sumReserve port draw).lower port).DescriptionFits := by
  have core := TokenEvaluation.descriptionFits layout.hashes coefficientDefault zero default P comparison correct
    update updateBuffers reserve port draw drawFits drawBound (by omega)
  have extent := TokenEvaluation.buffers layout.hashes coefficientDefault zero default P comparison correct update updateBuffers reserve port draw
  have sampled := drawBound.buffers
  have word := layout.signing.rows.accumulation.cache.wordFits
  have saved : Interactive.savedBuffer port
      (TokenEvaluation.code layout.hashes coefficientDefault zero default P comparison correct update updateBuffers reserve port draw) < 2 ^ w := by
    unfold Interactive.savedBuffer
    omega
  have retained := Interactive.retain_descriptionFits port _ _ _ _ _ word core saved
    layout.hashes.input.representation.fits layout.context.representation.fits layout.hashOutput.fits
  exact .seq word (.compute (prepare layout).description_fits)
    (.seq word retained
      (.seq word (.compute (transition layout sum sumBuffers sumReserve).description_fits)
        (WeightedSignatureTail.descriptionFits layout.signing coefficientDefault zero default generator P comparison correct
          update updateBuffers reserve extract extractBuffers extractReserve port draw
          generatorBound generatorReserve drawFits drawBound drawReserve updateReserve)))

theorem bad_descriptionFits {generatorSlots drawSlots : Nat}
    (generatorBound : generator.program.code.memBound ≤ generatorSlots) (generatorReserve : generatorSlots + 3 < 2 ^ w)
    (drawFits : (draw.lower port).DescriptionFits) (drawBound : WordIO.NamesBound (draw.lower port) drawSlots)
    (drawReserve : drawSlots + 5 < 2 ^ w) (updateReserve : slots + 4 < 2 ^ w) :
    ((badCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
      extract extractBuffers extractReserve port draw).lower port).DescriptionFits :=
  .seq layout.signing.rows.accumulation.cache.wordFits (.compute (prepareBad layout).description_fits)
    (WeightedSignatureTail.descriptionFits layout.signing coefficientDefault zero default generator P comparison correct
      update updateBuffers reserve extract extractBuffers extractReserve port draw
      generatorBound generatorReserve drawFits drawBound drawReserve updateReserve)

theorem resources {source : OracleComp spec layout.signing.rows.accumulation.cache.value.Value}
    (drawCorrect : Interactive.Refines port .unit layout.signing.rows.accumulation.cache.lookup.unit.representation
      layout.signing.rows.accumulation.cache.value.representation (fun _ => source) draw)
    {generatorTime generatorWords drawTime drawWords updateTime updateWords extractTime extractWords
      generatorNames drawNames updateNames extractNames sumNames sumTime sumWords : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawTimeBound : Interactive.TimeBound port .unit layout.signing.rows.accumulation.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords)
    (updateBound : update.BoundedBy updateTime updateWords) (extractBound : extract.BoundedBy extractTime extractWords)
    (generatorNamesBound : NamesAccounted generator.program.code generatorNames)
    (drawNamesBound : WordIO.NamesBound (draw.lower port) drawNames)
    (updateNamesBound : NamesAccounted update.program.code updateNames)
    (extractNamesBound : NamesAccounted extract.program.code extractNames)
    (sumBound : sum.BoundedBy sumTime sumWords)
    (sumNamesBound : NamesAccounted sum.program.code sumNames)
    (tape : RandomTape w) (value : layout.input.Value) (admitted : layout.ready value)
    (before : State w) (holds : layout.input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout coefficientDefault zero default generator P comparison correct
      update updateBuffers reserve extract extractBuffers extractReserve sum sumBuffers sumReserve port draw).execute port .unit tape before)) :
    finished.time ≤ timeBudget layout generatorTime drawTime updateTime extractTime sumTime ∧
    ∃ answer ∈ support (denote layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
        extract extractBuffers extractReserve sum source value),
      (WeightedSignatureTail.output layout.signing).representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape
          ((code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
            extract extractBuffers extractReserve sum sumBuffers sumReserve port draw).lower port)
          before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers
            ((code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
              extract extractBuffers extractReserve sum sumBuffers sumReserve port draw).lower port).registerSlots) ∧
          between.SupportBound (max buffers
            ((code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
              extract extractBuffers extractReserve sum sumBuffers sumReserve port draw).lower port).memBound) ∧ between.WellFormed ∧
          (((code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
              extract extractBuffers extractReserve sum sumBuffers sumReserve port draw).lower port).staticWords registers buffers : Int) +
            between.liveMem (max buffers
              ((code layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
                extract extractBuffers extractReserve sum sumBuffers sumReserve port draw).lower port).memBound) ≤
              5 * codeBudget layout generatorWords drawWords updateWords extractWords sumWords +
                4 * nameBudget generatorNames drawNames updateNames extractNames sumNames + registers + 3 * buffers +
                before.liveMem buffers + timeBudget layout generatorTime drawTime updateTime extractTime sumTime := by
  have refined := refines layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve sum sumBuffers sumReserve port drawCorrect
  have bounded := time_bound layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve sum sumBuffers sumReserve port drawCorrect generatorBound drawTimeBound updateBound extractBound sumBound
  have stored := code_bound layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve sum sumBuffers sumReserve port generatorBound updateBound extractBound sumBound draw drawWordsBound
  have accounted := names layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve sum sumBuffers sumReserve port draw generatorNamesBound drawNamesBound updateNamesBound extractNamesBound sumNamesBound
  obtain ⟨elapsed, answer, supported, represented, execution, memory⟩ :=
    refined.resources bounded stored accounted tape value admitted before holds
      registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, represented, execution, ?_⟩
  intro between visited
  obtain ⟨regs, bufs, wf, total⟩ := memory between visited
  exact ⟨regs, bufs, wf, by omega⟩


theorem bad_resources {source : OracleComp spec layout.signing.rows.accumulation.cache.value.Value}
    (drawCorrect : Interactive.Refines port .unit layout.signing.rows.accumulation.cache.lookup.unit.representation
      layout.signing.rows.accumulation.cache.value.representation (fun _ => source) draw)
    {generatorTime generatorWords drawTime drawWords updateTime updateWords extractTime extractWords
      generatorNames drawNames updateNames extractNames : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawTimeBound : Interactive.TimeBound port .unit layout.signing.rows.accumulation.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords)
    (updateBound : update.BoundedBy updateTime updateWords) (extractBound : extract.BoundedBy extractTime extractWords)
    (generatorNamesBound : NamesAccounted generator.program.code generatorNames)
    (drawNamesBound : WordIO.NamesBound (draw.lower port) drawNames)
    (updateNamesBound : NamesAccounted update.program.code updateNames)
    (extractNamesBound : NamesAccounted extract.program.code extractNames)
    (tape : RandomTape w) (value : layout.input.Value) (admitted : layout.badReady value)
    (before : State w) (holds : layout.input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((badCode layout coefficientDefault zero default generator P comparison correct
      update updateBuffers reserve extract extractBuffers extractReserve port draw).execute port .unit tape before)) :
    finished.time ≤ badTimeBudget layout generatorTime drawTime updateTime extractTime ∧
    ∃ answer ∈ support (badDenote layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
        extract extractBuffers extractReserve source value),
      (WeightedSignatureTail.output layout.signing).representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape
          ((badCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
            extract extractBuffers extractReserve port draw).lower port)
          before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers
            ((badCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
              extract extractBuffers extractReserve port draw).lower port).registerSlots) ∧
          between.SupportBound (max buffers
            ((badCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
              extract extractBuffers extractReserve port draw).lower port).memBound) ∧ between.WellFormed ∧
          (((badCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
              extract extractBuffers extractReserve port draw).lower port).staticWords registers buffers : Int) +
            between.liveMem (max buffers
              ((badCode layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
                extract extractBuffers extractReserve port draw).lower port).memBound) ≤
              5 * badCodeBudget layout generatorWords drawWords updateWords extractWords +
                4 * max generatorNames (max (max 5 drawNames) (max updateNames extractNames)) + registers + 3 * buffers +
                before.liveMem buffers + badTimeBudget layout generatorTime drawTime updateTime extractTime := by
  have refined := bad_refines layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve port drawCorrect
  have bounded := bad_time_bound layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve port drawCorrect generatorBound drawTimeBound updateBound extractBound
  have stored := bad_code_bound layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve port generatorBound updateBound extractBound draw drawWordsBound
  have accounted := bad_names layout coefficientDefault zero default generator P comparison correct update updateBuffers reserve
    extract extractBuffers extractReserve port draw generatorNamesBound drawNamesBound updateNamesBound extractNamesBound
  obtain ⟨elapsed, answer, supported, represented, execution, memory⟩ :=
    refined.resources bounded stored accounted tape value admitted before holds
      registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, represented, execution, ?_⟩
  intro between visited
  obtain ⟨regs, bufs, wf, total⟩ := memory between visited
  exact ⟨regs, bufs, wf, by omega⟩


end Signatures.Runtime.CaliperBackend.WeightedExtractor
