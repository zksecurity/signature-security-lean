import Signatures.Runtime.Caliper.WeightedSign
import Signatures.Runtime.Caliper.GeneratedWeightedBuffers

/-! Complete signing costs derived from generator, sampler, scalar update and
group-response costs. All routing and retained-state copying is included. -/
namespace Signatures.Runtime.CaliperBackend.WeightedSign
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M F C G : Type}
    [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) M F (val.Value base) C G)
    (zero : layout.evaluation.cache.value.Value)
    (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * (WeightedRows.term layout.evaluation).representation.encoding.words +
      layout.evaluated.representation.encoding.words < 2 ^ w)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit layout.message
      (GeneratedWeighted.terms layout.evaluation capacity countFits storageFits) generate)
    (default : layout.evaluation.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.evaluation.combine layout.evaluation.cache.value combine)
    {updateSlots : Nat} (updateBuffers : update.program.code.memBound ≤ updateSlots)
    (updateReserve : updateSlots + 2 < 2 ^ w)
    {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec) (draw : Interactive.Code w)
    {respond : val.Value base × C → G} (response : Implementation .unit layout.responseInput layout.point respond)
    {responseSlots : Nat} (responseBuffers : response.program.code.memBound ≤ responseSlots)
    (responseReserve : responseSlots < 2 ^ w)

def timeBudget (generatorTime drawTime updateTime responseTime : Nat) : Nat :=
  8 * layout.prepared.encoding.words +
    (GeneratedWeighted.prepareTime layout.evaluation layout.message capacity countFits storageFits generatorTime +
      RowFold.timeBudget (WeightedRows.rows layout.evaluation) capacity drawTime updateTime +
      8 * layout.evaluationInput.encoding.words + 8 * layout.evaluated.representation.encoding.words +
      12 * layout.input.representation.encoding.words + tailTime layout responseTime)
def codeBudget (generatorWords drawWords updateWords responseWords : Nat) : Nat :=
  (26 * layout.prepared.encoding.words + 15) +
    (GeneratedWeighted.codeBudget layout.evaluation layout.message capacity countFits storageFits
      generatorWords drawWords updateWords +
      26 * layout.evaluationInput.encoding.words + 26 * layout.evaluated.representation.encoding.words +
      39 * layout.input.representation.encoding.words + 42 + tailWords layout responseWords + 2) + 1

variable {source : OracleComp spec layout.evaluation.cache.value.Value}
    (drawCorrect : Interactive.Refines port .unit layout.evaluation.cache.lookup.unit.representation
      layout.evaluation.cache.value.representation (fun _ => source) draw)

include drawCorrect in
theorem time_bound {generatorTime generatorWords drawTime updateTime updateWords responseTime responseWords : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawBound : Interactive.TimeBound port .unit layout.evaluation.cache.lookup.unit.representation draw drawTime)
    (updateBound : update.BoundedBy updateTime updateWords) (responseBound : response.BoundedBy responseTime responseWords) :
    Interactive.TimeBoundOn (valid layout (generate := generate)) port .unit layout.input.representation
      (code layout zero capacity countFits storageFits generator default P comparison correct
        update updateBuffers updateReserve port draw response responseBuffers responseReserve)
      (timeBudget layout capacity countFits storageFits generatorTime drawTime updateTime responseTime) := by
  have coreCorrect := GeneratedWeighted.refines layout.evaluation layout.message capacity countFits storageFits generator
    port layout.evaluationInput.fits default P comparison correct update updateBuffers updateReserve drawCorrect
  have coreTime := GeneratedWeighted.time_bound layout.evaluation layout.message capacity countFits storageFits generator
    port layout.evaluationInput.fits default P comparison correct update updateBuffers updateReserve drawCorrect
    generatorBound drawBound updateBound
  have retainedCorrect := coreCorrect.retain (by decide) layout.input.representation layout.evaluation.cache.wordFits
    layout.prepared.fits layout.post.fits
  have retainedTime := (Interactive.TimeBoundOn.retain coreCorrect coreTime (by decide) layout.input.representation
    layout.evaluation.cache.wordFits layout.prepared.fits).mono (Interactive.retain_time_unit_le _ _ _ _ _)
  have ended := retainedTime.seq retainedCorrect
    ((Interactive.TimeBound.compute (port := port) (cost := .unit)
      (tail layout response responseBuffers responseReserve) (tailTime layout responseTime)
      (tail_time layout response responseBuffers responseReserve responseBound)).on (fun _ => True))
    (fun _ _ _ _ => trivial)
  have start := Interactive.TimeBound.compute (port := port) (cost := .unit)
    (prepare layout zero) (8 * layout.prepared.encoding.words)
    (ByteRoute.time _ _ _ (prepareParts layout zero) layout.evaluation.cache.wordFits
      (prepareParts_valid layout zero) (prepareParts_words layout zero) (prepare_bytes layout zero))
  exact (start.on (valid layout (generate := generate))).seq
    ((Interactive.Refines.compute port .unit (prepare layout zero)).on (valid layout (generate := generate)))
    ended (by
      intro value admitted answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact admitted)

theorem code_bound {generatorTime generatorWords drawWords updateTime updateWords responseTime responseWords : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawBound : (draw.lower port).descriptionWords ≤ drawWords)
    (updateBound : update.BoundedBy updateTime updateWords) (responseBound : response.BoundedBy responseTime responseWords) :
    ((code layout zero capacity countFits storageFits generator default P comparison correct
      update updateBuffers updateReserve port draw response responseBuffers responseReserve).lower port).descriptionWords ≤
      codeBudget layout capacity countFits storageFits generatorWords drawWords updateWords responseWords := by
  have core := GeneratedWeighted.code_bound layout.evaluation layout.message capacity countFits storageFits generator
    port default P comparison correct update updateBuffers updateReserve draw generatorBound drawBound updateBound
  have retained := Interactive.retain_descriptionWords_le port
    (evaluator layout capacity countFits storageFits generator default P comparison correct update updateBuffers updateReserve port draw)
    (Interactive.savedBuffer port (evaluator layout capacity countFits storageFits generator default P comparison correct
      update updateBuffers updateReserve port draw))
    layout.evaluationInput.encoding.words layout.evaluated.representation.encoding.words layout.input.representation.encoding.words
  have start := ByteRoute.codeWords _ _ _ (prepareParts layout zero) layout.evaluation.cache.wordFits
    (prepareParts_valid layout zero) (prepareParts_words layout zero) (prepare_bytes layout zero)
  have ended := tail_words layout response responseBuffers responseReserve responseBound
  change ((evaluator layout capacity countFits storageFits generator default P comparison correct
    update updateBuffers updateReserve port draw).lower port).descriptionWords ≤ _ at core
  change ((evaluate layout capacity countFits storageFits generator default P comparison correct
    update updateBuffers updateReserve port draw).lower port).descriptionWords ≤ _ at retained
  change descriptionWords (prepare layout zero).code ≤ _ at start
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names {generatorNames drawNames updateNames responseNames : Nat}
    (generatorBound : NamesAccounted generator.program.code generatorNames)
    (drawBound : WordIO.NamesBound (draw.lower port) drawNames)
    (updateBound : NamesAccounted update.program.code updateNames)
    (responseBound : NamesAccounted response.program.code responseNames) :
    WordIO.NamesAccounted ((code layout zero capacity countFits storageFits generator default P comparison correct
      update updateBuffers updateReserve port draw response responseBuffers responseReserve).lower port)
      (max (max generatorNames (max (max 5 drawNames) updateNames)) responseNames) := by
  have core := GeneratedWeighted.names layout.evaluation layout.message capacity countFits storageFits generator
    port default P comparison correct update updateBuffers updateReserve draw generatorBound drawBound updateBound
  exact (WordIO.NamesAccounted.compute (ByteRoute.names _ _ _ (prepareParts layout zero) layout.evaluation.cache.wordFits
    (prepareParts_valid layout zero) (prepareParts_words layout zero) (prepare_bytes layout zero) _)).seq
    (((Interactive.retain_names port core _ _ _).mono (Nat.le_max_left _ _)).seq
      (WordIO.NamesAccounted.compute ((tail_names layout response responseBuffers responseReserve responseBound).mono
        (Nat.le_max_right _ _))))

theorem descriptionFits
    (generatorReserve : generator.program.savedBuffer < 2 ^ w)
    (drawFits : (draw.lower port).DescriptionFits) {drawNames : Nat}
    (drawNamesBound : WordIO.NamesBound (draw.lower port) drawNames) (drawReserve : drawNames + 2 < 2 ^ w)
    (evaluationReserve : Interactive.savedBuffer port
      (evaluator layout capacity countFits storageFits generator default P comparison correct
        update updateBuffers updateReserve port draw) < 2 ^ w) :
    ((code layout zero capacity countFits storageFits generator default P comparison correct
      update updateBuffers updateReserve port draw response responseBuffers responseReserve).lower port).DescriptionFits :=
  .seq layout.evaluation.cache.wordFits (.compute (prepare layout zero).description_fits)
    (.seq layout.evaluation.cache.wordFits
      (Interactive.retain_descriptionFits port
        (evaluator layout capacity countFits storageFits generator default P comparison correct
          update updateBuffers updateReserve port draw) _ _ _ _ layout.evaluation.cache.wordFits
        (GeneratedWeighted.descriptionFits layout.evaluation layout.message capacity countFits storageFits generator
          port default P comparison correct update updateBuffers updateReserve draw
          generatorReserve drawFits drawNamesBound drawReserve) evaluationReserve
        layout.evaluationInput.fits layout.input.representation.fits layout.post.fits)
      (.compute (tail layout response responseBuffers responseReserve).description_fits))

theorem descriptionFits_of_components {generatorSlots drawSlots : Nat}
    (generatorBound : generator.program.code.memBound ≤ generatorSlots) (generatorReserve : generatorSlots + 1 < 2 ^ w)
    (drawFits : (draw.lower port).DescriptionFits)
    (drawBound : WordIO.NamesBound (draw.lower port) drawSlots) (drawReserve : drawSlots + 3 < 2 ^ w) :
    ((code layout zero capacity countFits storageFits generator default P comparison correct
      update updateBuffers updateReserve port draw response responseBuffers responseReserve).lower port).DescriptionFits := by
  have generatorName : generator.program.savedBuffer < 2 ^ w := by
    have hw := layout.evaluation.cache.wordFits
    unfold Realizer.savedBuffer
    omega
  exact descriptionFits layout zero capacity countFits storageFits generator default P comparison correct
    update updateBuffers updateReserve port draw response responseBuffers responseReserve generatorName drawFits drawBound
    (by omega)
    (GeneratedWeighted.savedNameFits layout.evaluation layout.message capacity countFits storageFits generator
      port default P comparison correct update updateBuffers updateReserve draw generatorBound generatorReserve drawBound drawReserve)

include drawCorrect in
theorem resources {generatorTime generatorWords drawTime drawWords updateTime updateWords responseTime responseWords
      generatorNames drawNames updateNames responseNames : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawTimeBound : Interactive.TimeBound port .unit layout.evaluation.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords)
    (updateBound : update.BoundedBy updateTime updateWords) (responseBound : response.BoundedBy responseTime responseWords)
    (generatorNamesBound : NamesAccounted generator.program.code generatorNames)
    (drawNamesBound : WordIO.NamesBound (draw.lower port) drawNames)
    (updateNamesBound : NamesAccounted update.program.code updateNames)
    (responseNamesBound : NamesAccounted response.program.code responseNames)
    (tape : RandomTape w) (value : layout.input.Value) (admitted : valid layout (generate := generate) value)
    (before : State w) (holds : layout.input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support
      ((code layout zero capacity countFits storageFits generator default P comparison correct update updateBuffers updateReserve
        port draw response responseBuffers responseReserve).execute port .unit tape before)) :
    finished.time ≤ timeBudget layout capacity countFits storageFits generatorTime drawTime updateTime responseTime ∧
    ∃ answer ∈ support (denote layout zero capacity countFits storageFits generator default P comparison correct
        update updateBuffers updateReserve response source value),
      layout.output.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape
          ((code layout zero capacity countFits storageFits generator default P comparison correct
            update updateBuffers updateReserve port draw response responseBuffers responseReserve).lower port)
          before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          ((code layout zero capacity countFits storageFits generator default P comparison correct
              update updateBuffers updateReserve port draw response responseBuffers responseReserve).lower port).staticWords registers buffers +
            (between.liveMem (max buffers
              ((code layout zero capacity countFits storageFits generator default P comparison correct
                update updateBuffers updateReserve port draw response responseBuffers responseReserve).lower port).memBound) : Int) ≤
            5 * codeBudget layout capacity countFits storageFits generatorWords drawWords updateWords responseWords +
              4 * max (max generatorNames (max (max 5 drawNames) updateNames)) responseNames + registers + 3 * buffers +
              before.liveMem buffers + timeBudget layout capacity countFits storageFits generatorTime drawTime updateTime responseTime := by
  have stored := code_bound layout zero capacity countFits storageFits generator default P comparison correct update updateBuffers
    updateReserve port draw response responseBuffers responseReserve generatorBound drawWordsBound updateBound responseBound
  have named := names layout zero capacity countFits storageFits generator default P comparison correct update updateBuffers
    updateReserve port draw response responseBuffers responseReserve
    generatorNamesBound drawNamesBound updateNamesBound responseNamesBound
  obtain ⟨elapsed, answer, supported, represented, execution, memory⟩ :=
    (refines layout zero capacity countFits storageFits generator default P comparison correct update updateBuffers
      updateReserve port draw response responseBuffers responseReserve drawCorrect).resources
    (time_bound layout zero capacity countFits storageFits generator default P comparison correct update updateBuffers
      updateReserve port draw response responseBuffers responseReserve drawCorrect
      generatorBound drawTimeBound updateBound responseBound)
    stored named tape value admitted before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, represented, execution, ?_⟩
  intro between visited
  have bound := (memory between visited).2.2.2
  omega

end Signatures.Runtime.CaliperBackend.WeightedSign
