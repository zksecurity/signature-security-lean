import Signatures.Runtime.Caliper.SchnorrROMHashMiss

/-! Bounds for the managed-cache miss routine include the executed copies of
the key around final hashing and every intermediate memory state. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.HashMiss
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} [Zero F] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G)

def timeBudget := FinalHash.timeBudget config + 8 * (prepared config).encoding.words +
  8 * (input config).representation.encoding.words + 8 * (FinalHash.output config).representation.encoding.words +
  12 * config.handler.core.key.representation.encoding.words + 8 * (output config).encoding.words
def codeBudget := FinalHash.codeBudget config + 26 * (prepared config).encoding.words +
  26 * (input config).representation.encoding.words + 26 * (FinalHash.output config).representation.encoding.words +
  39 * config.handler.core.key.representation.encoding.words + 26 * (output config).encoding.words + 73

theorem inner_time : Interactive.TimeBoundOn (ready config) (Fresh.port config.handler.sampler.tape) .unit
    (input config).representation (FinalHash.code config) (FinalHash.timeBudget config) := by
  intro random value valid before holds
  exact FinalHash.time_bound config random (admitted config value valid.1) valid.2 before holds

theorem time_bound : Interactive.TimeBoundOn (ready config) (Fresh.port config.handler.sampler.tape) .unit
    (input config).representation (code config) (timeBudget config) := by
  have held := (Interactive.TimeBoundOn.retain (inner_refines config) (inner_time config)
    (by decide) config.handler.core.key.representation config.sampler.wordFits (prepared config).fits).mono
      (Interactive.retain_time_unit_le _ _ _ _ _)
  have finished := (Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
    (finish config) (8 * (output config).encoding.words) (finish_time config)).on (fun _ => True)
  have suffix := Interactive.TimeBoundOn.seq (retained_refines config) held finished (by intros; trivial)
  have compiled := Interactive.TimeBoundOn.seq
    ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (prepare config)).on (ready config))
    ((Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
      (prepare config) (8 * (prepared config).encoding.words) (prepare_time config)).on (ready config)) suffix (by
        intro value valid answer reached
        simp only [support_pure, Set.mem_singleton_iff] at reached
        subst answer
        exact valid)
  exact compiled.mono (by unfold timeBudget; omega)

theorem code_bound : ((code config).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤ codeBudget config := by
  have body := FinalHash.code_bound config
  have prepared := prepare_words config
  have finished := finish_words config
  have held := Interactive.retain_descriptionWords_le (Fresh.port config.handler.sampler.tape) (FinalHash.code config)
    (Interactive.savedBuffer (Fresh.port config.handler.sampler.tape) (FinalHash.code config))
    (input config).representation.encoding.words (FinalHash.output config).representation.encoding.words
    config.handler.core.key.representation.encoding.words
  change ((retained config).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤ _ at held
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names : WordIO.NamesAccounted ((code config).lower (Fresh.port config.handler.sampler.tape)) (HashCache.nameBudget config) :=
  (WordIO.NamesAccounted.compute (prepare_names config _)).seq
    ((Interactive.retain_names (Fresh.port config.handler.sampler.tape) (FinalHash.names config)
      (input config).representation.encoding.words (FinalHash.output config).representation.encoding.words
      config.handler.core.key.representation.encoding.words).seq (WordIO.NamesAccounted.compute (finish_names config _)))

theorem buffers : ((code config).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ 11 := by
  have prepared := prepare_buffers config
  have finished := finish_buffers config
  have body := FinalHash.buffers config
  have held := Interactive.retain_buffers (Fresh.port config.handler.sampler.tape) (FinalHash.code config)
    (input config).representation.encoding.words (FinalHash.output config).representation.encoding.words
    config.handler.core.key.representation.encoding.words
  change ((retained config).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ _ at held
  change max (prepare config).code.memBound
    (max ((retained config).lower (Fresh.port config.handler.sampler.tape)).memBound (finish config).code.memBound) ≤ _
  omega

theorem descriptionFits : ((code config).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits := by
  have held := Interactive.retain_descriptionFits (Fresh.port config.handler.sampler.tape) (FinalHash.code config)
    (Interactive.savedBuffer (Fresh.port config.handler.sampler.tape) (FinalHash.code config))
    (input config).representation.encoding.words (FinalHash.output config).representation.encoding.words
    config.handler.core.key.representation.encoding.words config.sampler.wordFits (FinalHash.descriptionFits config)
    (by have := FinalHash.buffers config; have := config.sampler.wordFits; unfold Interactive.savedBuffer; omega)
    (input config).representation.fits config.handler.core.key.representation.fits (finished config).fits
  exact .seq config.sampler.wordFits (.compute (prepare config).description_fits)
    (.seq config.sampler.wordFits held (.compute (finish config).description_fits))

theorem resources (random : RandomTape w) (value : (input config).Value) (valid : ready config value)
    (before : State w) (holds : (input config).representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code config).execute (Fresh.port config.handler.sampler.tape) .unit random before)) :
    finished.time ≤ timeBudget config ∧
      ∃ answer ∈ support (source config value), (output config).Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit random ((code config).lower (Fresh.port config.handler.sampler.tape)) before finished.state
            finished.trace finished.time finished.net finished.peak,
          ∀ between, execution.Visits between →
            RegisterBound between (max registers ((code config).lower (Fresh.port config.handler.sampler.tape)).registerSlots) ∧
            between.SupportBound (max buffers ((code config).lower (Fresh.port config.handler.sampler.tape)).memBound) ∧ between.WellFormed ∧
            (((code config).lower (Fresh.port config.handler.sampler.tape)).staticWords registers buffers : Int) +
              between.liveMem (max buffers ((code config).lower (Fresh.port config.handler.sampler.tape)).memBound) ≤
                5 * codeBudget config + 4 * HashCache.nameBudget config + registers + 3 * buffers + before.liveMem buffers + timeBudget config := by
  have stored := code_bound config
  have named := names config
  have allNames : WordIO.NamesBound ((code config).lower (Fresh.port config.handler.sampler.tape))
      (HashCache.nameBudget config + codeBudget config) :=
    ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    (refines config).resources (time_bound config) stored allNames random value valid before holds
      registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, result, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ := bounds between visited
  exact ⟨registerBound, bufferBound, wellFormed, by push_cast at memory; omega⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.HashMiss
