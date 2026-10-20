import Signatures.Runtime.Caliper.SchnorrROMReplayDraw
import Signatures.Runtime.Caliper.SchnorrROMEnumeratedSigning
import Signatures.Runtime.Caliper.StatefulCacheInvariant
import Signatures.Runtime.Caliper.StatefulCacheBuffers

/-! A hash cache with the constructed public replay draw on misses. Cache hits
leave both tapes untouched; misses insert the replayed or fresh scalar. The
cache and signing use the same scalar, key and table encodings. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.HashCache
open Caliper BoundedSource OracleComp OracleSpec SchnorrROMTape
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

def model : StatefulCacheRead.Layouts w (M × G) F (Read.tapes config.handler.sampler.tape).Value where
  cache := config.handler.core.cache
  saved := (Read.tapes config.handler.sampler.tape).representation
  storageFits := config.handler.fits_of_le (by
    change 8 * (1 + (config.capacityPred + 1) * (config.message.representation.encoding.words +
      config.point.representation.encoding.words + 1) + (config.message.representation.encoding.words +
      config.point.representation.encoding.words) + 1 + (Read.tapes config.handler.sampler.tape).representation.encoding.words + 1 + 1) ≤
      128 * (1 + (config.capacityPred + 1) * (config.message.representation.encoding.words +
      config.point.representation.encoding.words + 1) + 3 + 3 * config.point.representation.encoding.words +
      config.message.representation.encoding.words + (Read.tapes config.handler.sampler.tape).representation.encoding.words)
    omega)

variable [Zero F] [DecidableEq M] [DecidableEq G]

def ready (value : (model config).cache.input.Value × (Read.tapes config.handler.sampler.tape).Value) : Prop :=
  EnumeratedReplay.ready config.sampler value.2

def code := StatefulCacheRead.code (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar) (Fresh.port config.handler.sampler.tape) (model config)
  (Signing.Cache.primitives F G M) Signing.Cache.comparison (Signing.Cache.comparison_correct F G M)
  (EnumeratedReplay.scalarCode config.sampler)

def source := StatefulCacheRead.denote (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar) (model config)
  (Signing.Cache.primitives F G M) Signing.Cache.comparison (Signing.Cache.comparison_correct F G M)
  (EnumeratedReplay.drawSource config.sampler)

theorem refines : Interactive.RefinesOn (ready config) (Fresh.port config.handler.sampler.tape) .unit
    (model config).input (model config).output (source config) (code config) :=
  StatefulCacheRead.refines_on (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar) (Fresh.port config.handler.sampler.tape) (model config)
    (Signing.Cache.primitives F G M) Signing.Cache.comparison (Signing.Cache.comparison_correct F G M)
    (EnumeratedReplay.draw_refines config.sampler)

def timeBudget : Nat := StatefulCacheRead.timeBudget (base := cryptoBase F G Unit M M)
  (key := Signing.Cache.keyTy) (val := scalar) (model config) (Caller.scalarTime config.handler.sampler.tape trivial 26)
def codeBudget : Nat := StatefulCacheRead.codeBudget (base := cryptoBase F G Unit M M)
  (key := Signing.Cache.keyTy) (val := scalar) (model config) (Caller.scalarWords config.handler.sampler.tape trivial 125)
def nameBudget : Nat := max 5 (Caller.nameSlots config.handler.sampler.tape trivial 125 3 +
  Caller.scalarWords config.handler.sampler.tape trivial 125)

theorem time_bound : Interactive.TimeBoundOn (ready config) (Fresh.port config.handler.sampler.tape) .unit
    (model config).input (code config) (timeBudget config) :=
  StatefulCacheRead.time_bound_on (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar) (Fresh.port config.handler.sampler.tape) (model config)
    (Signing.Cache.primitives F G M) Signing.Cache.comparison (Signing.Cache.comparison_correct F G M)
    (EnumeratedReplay.draw_refines config.sampler) (EnumeratedReplay.draw_time config.sampler)

theorem code_bound : ((code config).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤ codeBudget config :=
  StatefulCacheRead.code_bound (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar) (Fresh.port config.handler.sampler.tape) (model config)
    (Signing.Cache.primitives F G M) Signing.Cache.comparison (Signing.Cache.comparison_correct F G M)
    (EnumeratedReplay.scalarCode config.sampler)
    (Caller.scalar_words config.handler.sampler.tape trivial (PrivateSampler.Enumerated.Direct.code config.sampler)
      (PrivateSampler.Enumerated.Direct.code_words config.sampler))

theorem names : WordIO.NamesAccounted ((code config).lower (Fresh.port config.handler.sampler.tape)) (nameBudget config) := by
  have stored := Caller.scalar_words config.handler.sampler.tape trivial (PrivateSampler.Enumerated.Direct.code config.sampler)
    (PrivateSampler.Enumerated.Direct.code_words config.sampler)
  have named := Caller.scalar_names config.handler.sampler.tape trivial (PrivateSampler.Enumerated.Direct.code config.sampler)
    (PrivateSampler.Enumerated.Direct.code_words config.sampler) (PrivateSampler.Enumerated.Direct.names config.sampler)
  exact StatefulCacheRead.names (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar) (Fresh.port config.handler.sampler.tape) (model config)
    (Signing.Cache.primitives F G M) Signing.Cache.comparison (Signing.Cache.comparison_correct F G M)
    (EnumeratedReplay.scalarCode config.sampler)
    ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩

omit [DecidableEq M] [DecidableEq G] in
theorem draw_buffers : ((EnumeratedReplay.scalarCode config.sampler).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ 7 := by
  have bound := Caller.scalar_buffers config.handler.sampler.tape trivial (PrivateSampler.Enumerated.Direct.code config.sampler)
  have localBound := PrivateSampler.Enumerated.Direct.buffers config.sampler
  change ((PrivateSampler.Enumerated.Direct.code config.sampler).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ 2 at localBound
  exact bound.trans (by omega)

theorem buffers : ((code config).lower (Fresh.port config.handler.sampler.tape)).memBound ≤ 9 := by
  have bound := StatefulCacheRead.buffers (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar) (Fresh.port config.handler.sampler.tape) (model config)
    (Signing.Cache.primitives F G M) Signing.Cache.comparison (Signing.Cache.comparison_correct F G M)
    (EnumeratedReplay.scalarCode config.sampler)
  have := draw_buffers config
  exact bound.trans (by omega)

theorem descriptionFits : ((code config).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  (StatefulCacheRead.select_descriptionFits (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar) (Fresh.port config.handler.sampler.tape) (model config)
    (Signing.Cache.primitives F G M) Signing.Cache.comparison (Signing.Cache.comparison_correct F G M)).seq config.sampler.wordFits
    (StatefulCacheRead.branch_descriptionFits (model config) (Fresh.port config.handler.sampler.tape)
      (EnumeratedReplay.scalarCode config.sampler) (EnumeratedReplay.scalar_descriptionFits config.sampler)
      (by have := draw_buffers config; have := config.sampler.wordFits; unfold Interactive.savedBuffer; omega))

/-- Stored code, initial memory and every intermediate state are charged for
the same supported cache execution. No sampler resource premise remains. -/
theorem resources (random : RandomTape w)
    (value : (model config).cache.input.Value × (Read.tapes config.handler.sampler.tape).Value)
    (valid : ready config value) (before : State w) (holds : (model config).input.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code config).execute (Fresh.port config.handler.sampler.tape) .unit random before)) :
    finished.time ≤ timeBudget config ∧
      ∃ answer ∈ support (source config value), (model config).output.Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit random ((code config).lower (Fresh.port config.handler.sampler.tape))
            before finished.state finished.trace finished.time finished.net finished.peak,
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

end Signatures.Runtime.CaliperBackend.SchnorrROM.HashCache
