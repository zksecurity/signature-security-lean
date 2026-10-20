import Signatures.Runtime.Caliper.SchnorrROMHashMissBounds
import Signatures.Runtime.Caliper.StatefulCacheMissInvariant

/-! Normal hashing first reads the managed table. Its miss routine carries a
represented copy of the requested key and shared store into final hashing.
The returned managed table replaces that copy's old managed table. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Hash
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

def model : StatefulCacheRead.Layouts w (M × G) F (HashMiss.input config).Value where
  cache := config.handler.core.cache
  saved := (HashMiss.input config).representation
  storageFits := config.handler.fits_of_le (by
    have key := FinalHash.key_le config
    have saved := FinalHash.store_le config
    have table := config.handler.table_le
    have positive : 0 < config.handler.width := by change 0 < 1 + _ + _ + _ + _ + _; omega
    change 8 * ((config.handler.core.table.representation.encoding.words +
      config.handler.core.key.representation.encoding.words + 1) +
      (config.handler.core.key.representation.encoding.words + config.handler.store.representation.encoding.words) + 1 + 1) ≤ _
    omega)

abbrev output := FinalHash.output config
variable [Zero F] [DecidableEq M] [DecidableEq G]
def admissible (value : (M × G) × Schnorr.ListROM.Shared.Store F G M) : Prop :=
  config.handler.core.cache.admissible (value.1, 0, value.2.1.2.1, ())
instance (value : (M × G) × Schnorr.ListROM.Shared.Store F G M) : Decidable (admissible config value) :=
  inferInstanceAs (Decidable (config.handler.core.cache.admissible _))
def input := (HashMiss.input config).restrict (admissible config)

def request (value : (input config).Value) : (model config).cache.input.Value :=
  ⟨(value.val.1, 0, value.val.2.1.2.1, ()),
    ⟨value.property.1.1, trivial, value.property.1.2.1.2.1, trivial⟩, value.property.2⟩
def saved (value : (input config).Value) : (HashMiss.input config).Value := ⟨value.val, value.property.1⟩
def prepareValue (value : (input config).Value) := (request config value, saved config value)
def finishValue (value : (CacheRead.output (model config).cache).Value × (HashMiss.input config).Value) : (output config).Value :=
  ⟨(value.1.val.1, (value.2.val.2.1.1, value.1.val.2, value.2.val.2.1.2.2), value.2.val.2.2),
    value.1.property.1, ⟨value.2.property.2.1.1, value.1.property.2, value.2.property.2.1.2.2⟩, value.2.property.2.2⟩

/-- No LIVE or tape reservation is required on a managed hit. -/
def ready (value : (input config).Value) : Prop :=
  cacheMap value.val.2.1.2.1 value.val.1 = none → HashMiss.ready config (saved config value)

theorem selected_ready (value : (input config).Value) (valid : ready config value) :
    StatefulCacheRead.readyOnMiss (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar)
      (model config) (Signing.Cache.primitives F G M) Signing.Cache.comparison (HashMiss.ready config) (prepareValue config value) := by
  intro missing
  apply valid
  have looked := lookupExpr_value (val := scalar) (Signing.Cache.primitives F G M) Signing.Cache.comparison
    (Signing.Cache.comparison_correct F G M) value.val.1 (0 : F) value.val.2.1.2.1
  simp only [Expr.run_value] at looked
  change ((lookupExpr (val := scalar) Signing.Cache.comparison).denote (Signing.Cache.primitives F G M)
    (value.val.1, 0, value.val.2.1.2.1, ())).1 ≠ true at missing
  rw [looked, lookupValue_cacheMap] at missing
  cases found : cacheMap value.val.2.1.2.1 value.val.1 with
  | none => rfl
  | some challenge => simp only [found] at missing; exact False.elim (missing rfl)

end Signatures.Runtime.CaliperBackend.SchnorrROM.Hash
