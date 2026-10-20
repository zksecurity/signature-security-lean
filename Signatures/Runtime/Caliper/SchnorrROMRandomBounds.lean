import Signatures.Runtime.Caliper.SchnorrROMRandomSource

/-! Dynamic random queries charge raw replay, range decoding, retained caches
and every routing copy, including stored program and all visited memory. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Random
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} [Zero F] (config : Signing.Enumerated.Configuration w M F G)

def timeBudget := Caller.privateTime config.handler.sampler.tape trivial 26 + 8 * (prepared config).encoding.words +
  8 * (Caller.privateInput config.handler.sampler.tape).representation.encoding.words +
  8 * (Reply.privateOutput config.handler.sampler.tape).representation.encoding.words +
  12 * config.handler.caches.representation.encoding.words + 8 * (output config).representation.encoding.words
def codeBudget := Caller.privateWords config.handler.sampler.tape trivial 125 + 26 * (prepared config).encoding.words +
  26 * (Caller.privateInput config.handler.sampler.tape).representation.encoding.words +
  26 * (Reply.privateOutput config.handler.sampler.tape).representation.encoding.words +
  39 * config.handler.caches.representation.encoding.words + 26 * (output config).representation.encoding.words + 73
def nameBudget := Caller.nameSlots config.handler.sampler.tape trivial 125 3

theorem body_time : Interactive.TimeBound (Fresh.port config.handler.sampler.tape) .unit
    (Caller.privateInput config.handler.sampler.tape).representation (EnumeratedReplay.privateCode config.sampler)
      (Caller.privateTime config.handler.sampler.tape trivial 26) :=
  Caller.private_time config.handler.sampler.tape trivial (PrivateSampler.Enumerated.Direct.refines config.sampler)
    (PrivateSampler.Enumerated.Direct.time_bound config.sampler)

theorem time_bound : Interactive.TimeBound (Fresh.port config.handler.sampler.tape) .unit
    (input config).representation (code config) (timeBudget config) := by
  have held := ((body_time config).retain (body_refines config) (by decide) config.handler.caches.representation
    config.sampler.wordFits (prepared config).fits).mono (Interactive.retain_time_unit_le _ _ _ _ _)
  have finished := Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
    (finish config) (8 * (output config).representation.encoding.words) (finish_time config)
  have suffix := held.seq (retained_refines config) finished
  have compiled := (Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
    (prepare config) (8 * (prepared config).encoding.words) (prepare_time config)).seq
      (Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (prepare config)) suffix
  exact compiled.mono (by unfold timeBudget; omega)

theorem code_bound : ((code config).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤ codeBudget config := by
  have body := Caller.private_words config.handler.sampler.tape trivial (PrivateSampler.Enumerated.Direct.code config.sampler)
    (PrivateSampler.Enumerated.Direct.code_words config.sampler)
  have prepared := prepare_words config
  have finished := finish_words config
  have held := Interactive.retain_descriptionWords_le (Fresh.port config.handler.sampler.tape) (EnumeratedReplay.privateCode config.sampler)
    (Interactive.savedBuffer (Fresh.port config.handler.sampler.tape) (EnumeratedReplay.privateCode config.sampler))
    (Caller.privateInput config.handler.sampler.tape).representation.encoding.words
    (Reply.privateOutput config.handler.sampler.tape).representation.encoding.words config.handler.caches.representation.encoding.words
  change ((retained config).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤ _ at held
  change ((EnumeratedReplay.privateCode config.sampler).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤ _ at body
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names : WordIO.NamesAccounted ((code config).lower (Fresh.port config.handler.sampler.tape)) (nameBudget config) := by
  have body := Caller.private_names config.handler.sampler.tape trivial (PrivateSampler.Enumerated.Direct.code config.sampler)
    (PrivateSampler.Enumerated.Direct.code_words config.sampler) (PrivateSampler.Enumerated.Direct.names config.sampler)
  exact (WordIO.NamesAccounted.compute (prepare_names config _)).seq
    ((Interactive.retain_names (Fresh.port config.handler.sampler.tape) body
      (Caller.privateInput config.handler.sampler.tape).representation.encoding.words
      (Reply.privateOutput config.handler.sampler.tape).representation.encoding.words config.handler.caches.representation.encoding.words).seq
        (WordIO.NamesAccounted.compute (finish_names config _)))

theorem body_buffers : ((EnumeratedReplay.privateCode config.sampler).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ 8 := by
  have body := Caller.private_buffers config.handler.sampler.tape trivial (PrivateSampler.Enumerated.Direct.code config.sampler)
  have direct := PrivateSampler.Enumerated.Direct.buffers config.sampler
  change ((PrivateSampler.Enumerated.Direct.code config.sampler).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ 2 at direct
  exact body.trans (by omega)
theorem buffers : ((code config).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ 9 := by
  have prepared := prepare_buffers config
  have finished := finish_buffers config
  have body := body_buffers config
  have held := Interactive.retain_buffers (Fresh.port config.handler.sampler.tape) (EnumeratedReplay.privateCode config.sampler)
    (Caller.privateInput config.handler.sampler.tape).representation.encoding.words
    (Reply.privateOutput config.handler.sampler.tape).representation.encoding.words config.handler.caches.representation.encoding.words
  change ((retained config).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ _ at held
  change max (prepare config).code.memBound
    (max ((retained config).lower (Fresh.port config.handler.sampler.tape)).memBound (finish config).code.memBound) ≤ _
  omega

theorem descriptionFits : ((code config).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits := by
  have held := Interactive.retain_descriptionFits (Fresh.port config.handler.sampler.tape) (EnumeratedReplay.privateCode config.sampler)
    (Interactive.savedBuffer (Fresh.port config.handler.sampler.tape) (EnumeratedReplay.privateCode config.sampler))
    (Caller.privateInput config.handler.sampler.tape).representation.encoding.words
    (Reply.privateOutput config.handler.sampler.tape).representation.encoding.words config.handler.caches.representation.encoding.words
    config.sampler.wordFits (EnumeratedReplay.private_descriptionFits config.sampler)
    (by have := body_buffers config; have := config.sampler.wordFits; unfold Interactive.savedBuffer; omega)
    (Caller.privateInput config.handler.sampler.tape).representation.fits config.handler.caches.representation.fits (finished config).fits
  exact .seq config.sampler.wordFits (.compute (prepare config).description_fits)
    (.seq config.sampler.wordFits held (.compute (finish config).description_fits))

theorem resources (random : RandomTape w) (value : (input config).Value)
    (before : State w) (holds : (input config).representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code config).execute (Fresh.port config.handler.sampler.tape) .unit random before)) :
    finished.time ≤ timeBudget config ∧
      ∃ answer ∈ support (source config value), (output config).representation.Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit random ((code config).lower (Fresh.port config.handler.sampler.tape)) before finished.state
            finished.trace finished.time finished.net finished.peak,
          ∀ between, execution.Visits between →
            RegisterBound between (max registers ((code config).lower (Fresh.port config.handler.sampler.tape)).registerSlots) ∧
            between.SupportBound (max buffers ((code config).lower (Fresh.port config.handler.sampler.tape)).memBound) ∧ between.WellFormed ∧
            (((code config).lower (Fresh.port config.handler.sampler.tape)).staticWords registers buffers : Int) +
              between.liveMem (max buffers ((code config).lower (Fresh.port config.handler.sampler.tape)).memBound) ≤
                5 * codeBudget config + 4 * nameBudget config + registers + 3 * buffers + before.liveMem buffers + timeBudget config := by
  have stored := code_bound config
  have named := names config
  have allNames : WordIO.NamesBound ((code config).lower (Fresh.port config.handler.sampler.tape))
      (nameBudget config + codeBudget config) :=
    ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    ((refines config).on (fun _ => True)).resources ((time_bound config).on (fun _ => True)) stored allNames
      random value trivial before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, result, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ := bounds between visited
  exact ⟨registerBound, bufferBound, wellFormed, by push_cast at memory; omega⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.Random
