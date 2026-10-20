import Signatures.Runtime.Caliper.WeightedTarget
import Signatures.Runtime.Caliper.GeneratedWeightedBuffers

/-! Bounds for final-target evaluation and scalar extraction. Term generation,
cache reads, retained extraction inputs and local arithmetic are charged. -/
namespace Signatures.Runtime.CaliperBackend.WeightedTarget
open Caliper BoundedSource OracleComp OracleSpec WeightedCoefficient

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M F : Type}
    [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) M F (val.Value base))
    (zero : layout.evaluation.cache.value.Value)
    (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * (WeightedRows.term layout.evaluation).representation.encoding.words +
      layout.state.representation.encoding.words < 2 ^ w)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit layout.message
      (GeneratedWeighted.terms layout.evaluation capacity countFits storageFits) generate)
    (default : layout.evaluation.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.evaluation.combine layout.evaluation.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    {calculate : F × (val.Value base × val.Value base) → F}
    (extract : Implementation .unit layout.evaluation.combine layout.evaluation.coefficient calculate)
    {extractSlots : Nat} (extractBuffers : extract.program.code.memBound ≤ extractSlots)
    (extractReserve : extractSlots + 2 < 2 ^ w)
    {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec) (draw : Interactive.Code w)

def timeBudget (generatorTime drawTime updateTime extractTime : Nat) : Nat :=
  8 * layout.prepared.encoding.words +
    (GeneratedWeighted.prepareTime layout.evaluation layout.message capacity countFits storageFits generatorTime +
      RowFold.timeBudget (WeightedRows.rows layout.evaluation) capacity drawTime updateTime +
      8 * layout.evaluationInput.encoding.words + 8 * layout.state.representation.encoding.words +
      12 * layout.evaluation.saved.representation.encoding.words +
      (376 * layout.evaluation.width + extractTime))
def codeBudget (generatorWords drawWords updateWords extractWords : Nat) : Nat :=
  (26 * layout.prepared.encoding.words + 15) +
    (GeneratedWeighted.codeBudget layout.evaluation layout.message capacity countFits storageFits
      generatorWords drawWords updateWords +
      26 * layout.evaluationInput.encoding.words + 26 * layout.state.representation.encoding.words +
      39 * layout.evaluation.saved.representation.encoding.words + 42 +
      (1222 * layout.evaluation.width + 489 + extractWords) + 2) + 1

variable {source : OracleComp spec layout.evaluation.cache.value.Value}
    (drawCorrect : Interactive.Refines port .unit layout.evaluation.cache.lookup.unit.representation
      layout.evaluation.cache.value.representation (fun _ => source) draw)

include drawCorrect in
theorem time_bound {generatorTime generatorWords drawTime updateTime updateWords extractTime extractWords : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawBound : Interactive.TimeBound port .unit layout.evaluation.cache.lookup.unit.representation draw drawTime)
    (updateBound : update.BoundedBy updateTime updateWords)
    (extractBound : extract.BoundedBy extractTime extractWords) :
    Interactive.TimeBoundOn (valid layout (generate := generate)) port .unit layout.input.representation
      (code layout zero capacity countFits storageFits generator default P comparison correct
        update updateBuffers reserve extract extractBuffers extractReserve port draw)
      (timeBudget layout capacity countFits storageFits generatorTime drawTime updateTime extractTime) := by
  have coreCorrect := GeneratedWeighted.refines layout.evaluation layout.message capacity countFits storageFits generator
    port layout.evaluationInput.fits default P comparison correct update updateBuffers reserve drawCorrect
  have coreTime := GeneratedWeighted.time_bound layout.evaluation layout.message capacity countFits storageFits generator
    port layout.evaluationInput.fits default P comparison correct update updateBuffers reserve drawCorrect
    generatorBound drawBound updateBound
  have retainedCorrect := coreCorrect.retain (by decide) layout.evaluation.saved.representation
    layout.evaluation.cache.wordFits layout.prepared.fits layout.post.representation.fits
  have retainedTime := (Interactive.TimeBoundOn.retain coreCorrect coreTime (by decide)
    layout.evaluation.saved.representation layout.evaluation.cache.wordFits layout.prepared.fits).mono
    (Interactive.retain_time_unit_le _ _ _ _ _)
  have ended := retainedTime.seq retainedCorrect
    ((Interactive.TimeBound.compute (port := port) (cost := .unit) (tail layout extract extractBuffers extractReserve)
      (376 * layout.evaluation.width + extractTime) (fun value =>
        (CacheScalarResult.finish_bounded layout.evaluation extract extractBuffers extractReserve extractBound).time_le
          (postValue layout value))).on (fun _ => True)) (fun _ _ _ _ => trivial)
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

theorem code_bound {generatorTime generatorWords drawWords updateTime updateWords extractTime extractWords : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawBound : (draw.lower port).descriptionWords ≤ drawWords)
    (updateBound : update.BoundedBy updateTime updateWords)
    (extractBound : extract.BoundedBy extractTime extractWords) :
    ((code layout zero capacity countFits storageFits generator default P comparison correct
      update updateBuffers reserve extract extractBuffers extractReserve port draw).lower port).descriptionWords ≤
      codeBudget layout capacity countFits storageFits generatorWords drawWords updateWords extractWords := by
  have core := GeneratedWeighted.code_bound layout.evaluation layout.message capacity countFits storageFits generator
    port default P comparison correct update updateBuffers reserve draw generatorBound drawBound updateBound
  have retained := Interactive.retain_descriptionWords_le port
    (evaluator layout capacity countFits storageFits generator default P comparison correct update updateBuffers reserve port draw)
    (Interactive.savedBuffer port (evaluator layout capacity countFits storageFits generator default P comparison correct
      update updateBuffers reserve port draw))
    layout.evaluationInput.encoding.words layout.state.representation.encoding.words
    layout.evaluation.saved.representation.encoding.words
  have start := ByteRoute.codeWords _ _ _ (prepareParts layout zero) layout.evaluation.cache.wordFits
    (prepareParts_valid layout zero) (prepareParts_words layout zero) (prepare_bytes layout zero)
  have ended := (CacheScalarResult.finish_bounded layout.evaluation extract extractBuffers extractReserve extractBound).code_le
  change ((evaluator layout capacity countFits storageFits generator default P comparison correct
    update updateBuffers reserve port draw).lower port).descriptionWords ≤ _ at core
  change ((evaluate layout capacity countFits storageFits generator default P comparison correct
    update updateBuffers reserve port draw).lower port).descriptionWords ≤ _ at retained
  change descriptionWords (prepare layout zero).code ≤ _ at start
  change descriptionWords (tail layout extract extractBuffers extractReserve).code ≤ _ at ended
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names {generatorNames drawNames updateNames extractNames : Nat}
    (generatorBound : NamesAccounted generator.program.code generatorNames)
    (drawBound : WordIO.NamesBound (draw.lower port) drawNames)
    (updateBound : NamesAccounted update.program.code updateNames)
    (extractBound : NamesAccounted extract.program.code extractNames) :
    WordIO.NamesAccounted ((code layout zero capacity countFits storageFits generator default P comparison correct
      update updateBuffers reserve extract extractBuffers extractReserve port draw).lower port)
      (max generatorNames (max (max 5 drawNames) (max updateNames extractNames))) := by
  have core := GeneratedWeighted.names layout.evaluation layout.message capacity countFits storageFits generator
    port default P comparison correct update updateBuffers reserve draw generatorBound drawBound updateBound
  exact (WordIO.NamesAccounted.compute (ByteRoute.names _ _ _ (prepareParts layout zero) layout.evaluation.cache.wordFits
    (prepareParts_valid layout zero) (prepareParts_words layout zero) (prepare_bytes layout zero) _)).seq
    ((Interactive.retain_names port (core.mono (by omega)) _ _ _).seq
      (WordIO.NamesAccounted.compute ((CacheScalarResult.finish_names layout.evaluation extract extractBuffers extractReserve extractBound).mono (by omega))))

theorem buffers {generatorSlots drawSlots : Nat}
    (generatorBound : generator.program.code.memBound ≤ generatorSlots)
    (drawBound : (draw.lower port).memBound ≤ drawSlots) :
    ((code layout zero capacity countFits storageFits generator default P comparison correct
      update updateBuffers reserve extract extractBuffers extractReserve port draw).lower port).memBound ≤
      max (max 12 (max (generatorSlots + 2) (max (drawSlots + 4) (slots + 3))))
        (max 4 extractSlots + 1) := by
  have core := GeneratedWeighted.buffers layout.evaluation layout.message capacity countFits storageFits
    generator port default P comparison correct update updateBuffers reserve draw
  have retained := Interactive.retain_buffers port
    (evaluator layout capacity countFits storageFits generator default
      P comparison correct update updateBuffers reserve port draw)
    layout.evaluationInput.encoding.words layout.state.representation.encoding.words
    layout.evaluation.saved.representation.encoding.words
  have started := ByteRoute.buffers _ _ _ (prepareParts layout zero)
    layout.evaluation.cache.wordFits (prepareParts_valid layout zero)
    (prepareParts_words layout zero) (prepare_bytes layout zero)
  have ended := CacheScalarResult.finish_buffers layout.evaluation extract extractBuffers extractReserve
  change ((evaluator layout capacity countFits storageFits generator default
    P comparison correct update updateBuffers reserve port draw).lower port).memBound ≤ _ at core
  change ((evaluate layout capacity countFits storageFits generator default
    P comparison correct update updateBuffers reserve port draw).lower port).memBound ≤ _ at retained
  change (prepare layout zero).code.memBound ≤ 2 at started
  change (tail layout extract extractBuffers extractReserve).code.memBound ≤ _ at ended
  have retainedBound : ((evaluate layout capacity countFits storageFits generator default
      P comparison correct update updateBuffers reserve port draw).lower port).memBound ≤
      max 12 (max (generatorSlots + 2) (max (drawSlots + 4) (slots + 3))) := by
    omega
  have startBound : (prepare layout zero).code.memBound ≤
      max 12 (max (generatorSlots + 2) (max (drawSlots + 4) (slots + 3))) :=
    started.trans ((by decide : 2 ≤ 12).trans (Nat.le_max_left _ _))
  change max (prepare layout zero).code.memBound
    (max ((evaluate layout capacity countFits storageFits generator default
      P comparison correct update updateBuffers reserve port draw).lower port).memBound
      (tail layout extract extractBuffers extractReserve).code.memBound) ≤ _
  exact max_le (startBound.trans (Nat.le_max_left _ _))
    (max_le (retainedBound.trans (Nat.le_max_left _ _)) (ended.trans (Nat.le_max_right _ _)))

theorem descriptionFits {generatorSlots drawSlots : Nat}
    (generatorBound : generator.program.code.memBound ≤ generatorSlots) (generatorReserve : generatorSlots + 1 < 2 ^ w)
    (drawFits : (draw.lower port).DescriptionFits)
    (drawBound : WordIO.NamesBound (draw.lower port) drawSlots) (drawReserve : drawSlots + 3 < 2 ^ w) :
    ((code layout zero capacity countFits storageFits generator default P comparison correct
      update updateBuffers reserve extract extractBuffers extractReserve port draw).lower port).DescriptionFits := by
  have generatorName : generator.program.savedBuffer < 2 ^ w := by
    have hw := layout.evaluation.cache.wordFits
    unfold Realizer.savedBuffer
    omega
  exact .seq layout.evaluation.cache.wordFits (.compute (prepare layout zero).description_fits)
    (.seq layout.evaluation.cache.wordFits
      (Interactive.retain_descriptionFits port
        (evaluator layout capacity countFits storageFits generator default P comparison correct
          update updateBuffers reserve port draw) _ _ _ _ layout.evaluation.cache.wordFits
        (GeneratedWeighted.descriptionFits layout.evaluation layout.message capacity countFits storageFits generator
          port default P comparison correct update updateBuffers reserve draw
          generatorName drawFits drawBound (by omega))
        (GeneratedWeighted.savedNameFits layout.evaluation layout.message capacity countFits storageFits generator
          port default P comparison correct update updateBuffers reserve draw
          generatorBound generatorReserve drawBound drawReserve)
        layout.evaluationInput.fits layout.evaluation.saved.representation.fits layout.post.representation.fits)
      (.compute (tail layout extract extractBuffers extractReserve).description_fits))

include drawCorrect in
theorem resources {generatorTime generatorWords drawTime drawWords updateTime updateWords extractTime extractWords
      generatorNames drawNames updateNames extractNames : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawTimeBound : Interactive.TimeBound port .unit layout.evaluation.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords)
    (updateBound : update.BoundedBy updateTime updateWords)
    (extractBound : extract.BoundedBy extractTime extractWords)
    (generatorNamesBound : NamesAccounted generator.program.code generatorNames)
    (drawNamesBound : WordIO.NamesBound (draw.lower port) drawNames)
    (updateNamesBound : NamesAccounted update.program.code updateNames)
    (extractNamesBound : NamesAccounted extract.program.code extractNames)
    (tape : RandomTape w) (value : layout.input.Value) (admitted : valid layout (generate := generate) value)
    (before : State w) (holds : layout.input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support
      ((code layout zero capacity countFits storageFits generator default P comparison correct update updateBuffers reserve extract extractBuffers extractReserve
        port draw).execute port .unit tape before)) :
    finished.time ≤ timeBudget layout capacity countFits storageFits generatorTime drawTime updateTime extractTime ∧
    ∃ answer ∈ support (denote layout zero capacity countFits storageFits generator default P comparison correct
        update updateBuffers reserve extract extractBuffers extractReserve source value),
      (output layout).representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape
          ((code layout zero capacity countFits storageFits generator default P comparison correct
            update updateBuffers reserve extract extractBuffers extractReserve port draw).lower port)
          before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          ((code layout zero capacity countFits storageFits generator default P comparison correct
              update updateBuffers reserve extract extractBuffers extractReserve port draw).lower port).staticWords registers buffers +
            (between.liveMem (max buffers
              ((code layout zero capacity countFits storageFits generator default P comparison correct
                update updateBuffers reserve extract extractBuffers extractReserve port draw).lower port).memBound) : Int) ≤
            5 * codeBudget layout capacity countFits storageFits generatorWords drawWords updateWords extractWords +
              4 * max generatorNames (max (max 5 drawNames) (max updateNames extractNames)) + registers + 3 * buffers +
              before.liveMem buffers + timeBudget layout capacity countFits storageFits generatorTime drawTime updateTime extractTime := by
  have stored := code_bound layout zero capacity countFits storageFits generator default P comparison correct update updateBuffers reserve extract extractBuffers extractReserve port draw generatorBound drawWordsBound updateBound extractBound
  have named := names layout zero capacity countFits storageFits generator default P comparison correct update updateBuffers reserve extract extractBuffers extractReserve port draw generatorNamesBound drawNamesBound updateNamesBound extractNamesBound
  obtain ⟨elapsed, answer, supported, represented, execution, memory⟩ :=
    (refines layout zero capacity countFits storageFits generator default P comparison correct update updateBuffers reserve extract extractBuffers extractReserve port draw drawCorrect).resources
    (time_bound layout zero capacity countFits storageFits generator default P comparison correct update updateBuffers reserve extract extractBuffers extractReserve port draw drawCorrect generatorBound drawTimeBound updateBound extractBound)
    stored named tape value admitted before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, represented, execution, ?_⟩
  intro between visited
  have bound := (memory between visited).2.2.2
  omega

end Signatures.Runtime.CaliperBackend.WeightedTarget
