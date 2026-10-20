import Signatures.Runtime.Caliper.SchnorrROMHashCacheSource

/-! The final verification hash reads LIVE, retaining the public configuration
and managed table. It shares the signing handler's store encoding. A full LIVE
table is admitted on a hit; a miss needs one insertion slot. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.FinalHash
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

theorem key_le : config.handler.core.key.representation.encoding.words ≤ config.handler.width := by
  have bound := config.handler.core.input_le
  rw [Signing.Layouts.input_words] at bound
  rw [Signing.Handler.Layouts.width_eq]
  change config.message.representation.encoding.words + config.point.representation.encoding.words ≤ _
  change 2 * 1 + 2 * config.point.representation.encoding.words + config.message.representation.encoding.words +
    config.handler.core.table.representation.encoding.words ≤ _ at bound
  omega

theorem context_le : config.handler.core.store.representation.encoding.words ≤ config.handler.width := by
  have bound := config.handler.core.output_le
  rw [Signing.Handler.Layouts.width_eq]
  change (_ + _) + config.handler.core.store.representation.encoding.words ≤ _ at bound
  omega

theorem store_le : config.handler.store.representation.encoding.words ≤ 3 * config.handler.width := by
  have context := context_le config
  have table := config.handler.table_le
  rw [Signing.Handler.Layouts.width_eq] at *
  change ((_ + _) + _) ≤ _ at context
  change ((_ + _) + (_ + _)) + _ ≤ _
  omega

def rawInput := config.handler.core.key.prod config.handler.store
  (config.handler.fits_of_le (by have := key_le config; have := store_le config; omega))

def output := config.handler.sampler.tape.scalar.prod config.handler.store
  (config.handler.fits_of_le (by
    have bound := store_le config
    change 1 + config.handler.store.representation.encoding.words ≤ _
    have positive : 0 < config.handler.width := by
      change 0 < 1 + _ + _ + _ + _ + _
      omega
    omega))

variable [Zero F] [DecidableEq M] [DecidableEq G]

def admissible (value : (M × G) × Schnorr.ListROM.Shared.Store F G M) : Prop :=
  config.handler.core.cache.admissible (value.1, 0, value.2.1.2.2, ())
instance (value : (M × G) × Schnorr.ListROM.Shared.Store F G M) : Decidable (admissible config value) :=
  inferInstanceAs (Decidable (config.handler.core.cache.admissible _))
def input := (rawInput config).restrict (admissible config)

omit [Zero F] in
theorem read_le : (HashCache.model config).input.encoding.words ≤ 3 * config.handler.width := by
  have key := key_le config
  have table := config.handler.table_le
  have tapeBound : (Read.tapes config.handler.sampler.tape).representation.encoding.words ≤ config.handler.width := by
    rw [Signing.Handler.Layouts.width_eq]
    omega
  have positive : 0 < config.handler.width := by change 0 < 1 + _ + _ + _ + _ + _; omega
  change (config.handler.core.key.representation.encoding.words + (1 + (config.handler.core.table.representation.encoding.words + 0))) +
    (Read.tapes config.handler.sampler.tape).representation.encoding.words ≤ _
  have core := config.handler.core.input_le
  rw [Signing.Layouts.input_words] at core
  rw [Signing.Handler.Layouts.width_eq] at *
  change config.message.representation.encoding.words + config.point.representation.encoding.words ≤ _ at key
  change ((config.message.representation.encoding.words + config.point.representation.encoding.words) + (1 + (_ + 0))) + _ ≤ _
  change 2 * 1 + 2 * config.point.representation.encoding.words + config.message.representation.encoding.words + _ ≤ _ at core
  omega

omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem readOutput_le : (HashCache.model config).output.encoding.words ≤ 3 * config.handler.width := by
  have table := config.handler.table_le
  have tapeBound : (Read.tapes config.handler.sampler.tape).representation.encoding.words ≤ config.handler.width := by
    rw [Signing.Handler.Layouts.width_eq]
    omega
  have positive : 0 < config.handler.width := by change 0 < 1 + _ + _ + _ + _ + _; omega
  change (1 + config.handler.core.table.representation.encoding.words) + (Read.tapes config.handler.sampler.tape).representation.encoding.words ≤ _
  omega

def prepared := (HashCache.model config).input.prod config.handler.core.store.representation
  (config.handler.fits_of_le (by have := read_le config; have := context_le config; omega))
def finished := (HashCache.model config).output.prod config.handler.core.store.representation
  (config.handler.fits_of_le (by have := readOutput_le config; have := context_le config; omega))

def request (value : (input config).Value) : (HashCache.model config).cache.input.Value :=
  ⟨(value.val.1, 0, value.val.2.1.2.2, ()),
    ⟨value.property.1.1, trivial, value.property.1.2.1.2.2, trivial⟩, value.property.2⟩
def tapes (value : (input config).Value) : (Read.tapes config.handler.sampler.tape).Value :=
  ⟨value.val.2.2, value.property.1.2.2⟩
def context (value : (input config).Value) : config.handler.core.store.Value :=
  ⟨(value.val.2.1.1, value.val.2.1.2.1), value.property.1.2.1.1, value.property.1.2.1.2.1⟩
def prepareValue (value : (input config).Value) := ((request config value, tapes config value), context config value)

def finishValue (value : ((CacheRead.output (HashCache.model config).cache).Value ×
    (Read.tapes config.handler.sampler.tape).Value) × config.handler.core.store.Value) : (output config).Value :=
  ⟨(value.1.1.val.1, (value.2.val.1, value.2.val.2, value.1.1.val.2), value.1.2.val),
    value.1.1.property.1, ⟨value.2.property.1, value.2.property.2, value.1.1.property.2⟩, value.1.2.property⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.FinalHash
