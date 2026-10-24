import Proofs.Runtime.Caliper.SchnorrROMHashSource

/-! Complete normal-hash resource bounds. Lookup, miss handling, copied state,
stored program, dense names and every intermediate memory state are charged. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Hash
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} [Zero F] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G)

def cacheTime := StatefulCacheRead.timeBudget (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar)
  (model config) (HashMiss.timeBudget config)
def cacheWords := StatefulCacheRead.codeBudget (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar)
  (model config) (HashMiss.codeBudget config)
def timeBudget := cacheTime config + 8 * (model config).input.encoding.words + 8 * (output config).representation.encoding.words
def codeBudget := cacheWords config + 26 * (model config).input.encoding.words + 26 * (output config).representation.encoding.words + 32
def nameBudget := max 5 (HashCache.nameBudget config)

theorem cache_time : Interactive.TimeBoundOn (cacheReady config) (Fresh.port config.handler.sampler.tape) .unit
    (model config).input (cacheCode config) (cacheTime config) :=
  StatefulCacheRead.time_bound_on_miss (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar)
    (Fresh.port config.handler.sampler.tape) (model config) (Signing.Cache.primitives F G M)
    Signing.Cache.comparison (Signing.Cache.comparison_correct F G M) (HashMiss.refines config) (HashMiss.time_bound config)

theorem time_bound : Interactive.TimeBoundOn (ready config) (Fresh.port config.handler.sampler.tape) .unit
    (input config).representation (code config) (timeBudget config) := by
  have finished := (Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
    (finish config) (8 * (output config).representation.encoding.words) (finish_time config)).on (fun _ => True)
  have suffix := Interactive.TimeBoundOn.seq (cache_refines config) (cache_time config) finished (by intros; trivial)
  have compiled := Interactive.TimeBoundOn.seq
    ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (prepare config)).on (ready config))
    ((Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
      (prepare config) (8 * (model config).input.encoding.words) (prepare_time config)).on (ready config)) suffix (by
        intro value valid answer reached
        simp only [support_pure, Set.mem_singleton_iff] at reached
        subst answer
        exact selected_ready config value valid)
  exact compiled.mono (by unfold timeBudget; omega)

theorem code_bound : ((code config).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤ codeBudget config := by
  have body := StatefulCacheRead.code_bound (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar)
    (Fresh.port config.handler.sampler.tape) (model config) (Signing.Cache.primitives F G M)
    Signing.Cache.comparison (Signing.Cache.comparison_correct F G M) (HashMiss.code config) (HashMiss.code_bound config)
  change ((cacheCode config).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤ cacheWords config at body
  have prepared := prepare_words config
  have finished := finish_words config
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names : WordIO.NamesAccounted ((code config).lower (Fresh.port config.handler.sampler.tape)) (nameBudget config) := by
  have selected := (StatefulCacheRead.select_names (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar)
    (Fresh.port config.handler.sampler.tape) (model config) (Signing.Cache.primitives F G M)
    Signing.Cache.comparison (Signing.Cache.comparison_correct F G M)).mono (Nat.le_max_left 5 (HashCache.nameBudget config))
  have branch := StatefulCacheRead.branch_names (model config) (Fresh.port config.handler.sampler.tape)
    (HashMiss.code config) ((HashMiss.names config).mono (Nat.le_max_right 5 (HashCache.nameBudget config)))
  exact (WordIO.NamesAccounted.compute (prepare_names config _)).seq
    ((selected.seq branch).seq (WordIO.NamesAccounted.compute (finish_names config _)))

theorem buffers : ((code config).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ 12 := by
  have prepared := prepare_buffers config
  have finished := finish_buffers config
  have body := StatefulCacheRead.buffers (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar)
    (Fresh.port config.handler.sampler.tape) (model config) (Signing.Cache.primitives F G M)
    Signing.Cache.comparison (Signing.Cache.comparison_correct F G M) (HashMiss.code config)
  have miss := HashMiss.buffers config
  change ((cacheCode config).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ _ at body
  change max (prepare config).code.memBound
    (max ((cacheCode config).lower (Fresh.port config.handler.sampler.tape)).memBound (finish config).code.memBound) ≤ _
  omega

theorem descriptionFits : ((code config).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits := by
  have body := (StatefulCacheRead.select_descriptionFits (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar)
    (Fresh.port config.handler.sampler.tape) (model config) (Signing.Cache.primitives F G M)
    Signing.Cache.comparison (Signing.Cache.comparison_correct F G M)).seq config.sampler.wordFits
      (StatefulCacheRead.branch_descriptionFits (model config) (Fresh.port config.handler.sampler.tape)
        (HashMiss.code config) (HashMiss.descriptionFits config)
        (by have := HashMiss.buffers config; have := config.sampler.wordFits; unfold Interactive.savedBuffer; omega))
  exact .seq config.sampler.wordFits (.compute (prepare config).description_fits)
    (.seq config.sampler.wordFits body (.compute (finish config).description_fits))

theorem resources (random : RandomTape w) (value : (input config).Value) (valid : ready config value)
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
    (refines config).resources (time_bound config) stored allNames random value valid before holds
      registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, result, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ := bounds between visited
  exact ⟨registerBound, bufferBound, wellFormed, by push_cast at memory; omega⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.Hash
