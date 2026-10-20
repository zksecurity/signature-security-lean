import Signatures.Runtime.Caliper.SchnorrROMForgeryHashSource

/-! Final hashing charges the lookup, complete forgery retention and all routed
words. Stored code, dense names and all visited memory belong to the same run. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ForgeryHash
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

theorem rawPrepare_time (value) : (rawPrepare config).time value ≤ 8 * (rawPrepared config).encoding.words := ByteRoute.time _ _ _ _ _ _ _ _ value
theorem finish_time (value) : (finish config).time value ≤ 8 * (output config).encoding.words := ByteRoute.time _ _ _ _ _ _ _ _ value
theorem rawPrepare_words : descriptionWords (rawPrepare config).code ≤ 26 * (rawPrepared config).encoding.words + 14 := ByteRoute.codeWords _ _ _ _ _ _ _ _
theorem finish_words : descriptionWords (finish config).code ≤ 26 * (output config).encoding.words + 14 := ByteRoute.codeWords _ _ _ _ _ _ _ _
theorem rawPrepare_buffers : (rawPrepare config).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
theorem finish_buffers : (finish config).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
theorem rawPrepare_names (slots : Nat) : NamesAccounted (rawPrepare config).code slots := ByteRoute.names _ _ _ _ _ _ _ _ slots
theorem finish_names (slots : Nat) : NamesAccounted (finish config).code slots := ByteRoute.names _ _ _ _ _ _ _ _ slots

variable [Zero F] [DecidableEq M] [DecidableEq G]

def timeBudget := FinalHash.timeBudget config + 8 * (rawPrepared config).encoding.words +
  8 * (FinalHash.input config).representation.encoding.words + 8 * (FinalHash.output config).representation.encoding.words +
  12 * (forgery config).representation.encoding.words + 8 * (output config).encoding.words
def codeBudget := FinalHash.codeBudget config + 26 * (rawPrepared config).encoding.words +
  26 * (FinalHash.input config).representation.encoding.words + 26 * (FinalHash.output config).representation.encoding.words +
  39 * (forgery config).representation.encoding.words + 26 * (output config).encoding.words + 73

theorem time_bound : Interactive.TimeBoundOn (ready config) (Fresh.port config.handler.sampler.tape) .unit
    (input config) (code config) (timeBudget config) := by
  have held := (Interactive.TimeBoundOn.retain (FinalHash.refines config) (FinalHash.time_bound config)
    (by decide) (forgery config).representation config.sampler.wordFits (prepared config).fits).mono
      (Interactive.retain_time_unit_le _ _ _ _ _)
  have converted := (Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
    (finish config) (8 * (output config).encoding.words) (finish_time config)).on (fun _ => True)
  have suffix := Interactive.TimeBoundOn.seq (retained_refines config) held converted (fun _ _ _ _ => trivial)
  have compiled := Interactive.TimeBoundOn.seq
    ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (prepare config)).on (fun _ => True))
    ((Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
      (prepare config) (8 * (rawPrepared config).encoding.words) (fun value => rawPrepare_time config value.val)).on (fun _ => True)) suffix (by
        intro value _ answer reached
        simp only [support_pure, Set.mem_singleton_iff] at reached
        subst answer
        exact request_ready config value.val value.property)
  have bounded := compiled.mono (larger := timeBudget config) (by unfold timeBudget; omega)
  intro tape value valid before holds finished reached
  exact bounded tape ⟨value, valid⟩ trivial before holds finished reached

theorem code_bound : ((code config).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤ codeBudget config := by
  have body := FinalHash.code_bound config
  have prepared := rawPrepare_words config
  have finished := finish_words config
  have held := Interactive.retain_descriptionWords_le (Fresh.port config.handler.sampler.tape) (FinalHash.code config)
    (Interactive.savedBuffer (Fresh.port config.handler.sampler.tape) (FinalHash.code config))
    (FinalHash.input config).representation.encoding.words (FinalHash.output config).representation.encoding.words
    (forgery config).representation.encoding.words
  change ((retained config).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤ _ at held
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names : WordIO.NamesAccounted ((code config).lower (Fresh.port config.handler.sampler.tape)) (HashCache.nameBudget config) :=
  (WordIO.NamesAccounted.compute (rawPrepare_names config _)).seq
    ((Interactive.retain_names (Fresh.port config.handler.sampler.tape) (FinalHash.names config)
      (FinalHash.input config).representation.encoding.words (FinalHash.output config).representation.encoding.words
      (forgery config).representation.encoding.words).seq (WordIO.NamesAccounted.compute (finish_names config _)))

theorem buffers : ((code config).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ 11 := by
  have prepared := rawPrepare_buffers config
  have finished := finish_buffers config
  have body := FinalHash.buffers config
  have held := Interactive.retain_buffers (Fresh.port config.handler.sampler.tape) (FinalHash.code config)
    (FinalHash.input config).representation.encoding.words (FinalHash.output config).representation.encoding.words
    (forgery config).representation.encoding.words
  change ((retained config).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ _ at held
  change max (rawPrepare config).code.memBound
    (max ((retained config).lower (Fresh.port config.handler.sampler.tape)).memBound (finish config).code.memBound) ≤ _
  omega

theorem descriptionFits : ((code config).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits := by
  have held := Interactive.retain_descriptionFits (Fresh.port config.handler.sampler.tape) (FinalHash.code config)
    (Interactive.savedBuffer (Fresh.port config.handler.sampler.tape) (FinalHash.code config))
    (FinalHash.input config).representation.encoding.words (FinalHash.output config).representation.encoding.words
    (forgery config).representation.encoding.words config.sampler.wordFits (FinalHash.descriptionFits config)
    (by have := FinalHash.buffers config; have := config.sampler.wordFits; unfold Interactive.savedBuffer; omega)
    (FinalHash.input config).representation.fits (forgery config).representation.fits (finished config).fits
  exact .seq config.sampler.wordFits (.compute (rawPrepare config).description_fits)
    (.seq config.sampler.wordFits held (.compute (finish config).description_fits))

theorem resources (random : RandomTape w) (value : Input config) (valid : ready config value)
    (before : State w) (holds : (input config).Holds value before)
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

end Signatures.Runtime.CaliperBackend.SchnorrROM.ForgeryHash
