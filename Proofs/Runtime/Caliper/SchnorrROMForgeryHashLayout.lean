import Proofs.Runtime.Caliper.SchnorrROMCallerResources

/-! Final-challenge lookup retains the complete forgery while hashing its
message/commitment key in LIVE. The same scalar, message, point and private-store
encodings are used by the caller, signing service and final hash. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ForgeryHash
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

def forgery : Layout w (M × G × F) := config.message.prod config.handler.core.reply
  (config.handler.fits_of_le (by
    have key := FinalHash.key_le config
    have positive := Random.positive config
    change config.message.representation.encoding.words + config.point.representation.encoding.words ≤ _ at key
    change config.message.representation.encoding.words + (config.point.representation.encoding.words + 1) ≤ _
    omega))
def width := 1 + 2 * (forgery config).representation.encoding.words + config.handler.store.representation.encoding.words
theorem width_fits : width config < 2 ^ w := by
  have key := FinalHash.key_le config
  have saved := FinalHash.store_le config
  have positive := Random.positive config
  apply config.handler.fits_of_le
  unfold width
  change config.message.representation.encoding.words + config.point.representation.encoding.words ≤ _ at key
  change 1 + 2 * (config.message.representation.encoding.words + (config.point.representation.encoding.words + 1)) +
    config.handler.store.representation.encoding.words ≤ _
  omega
theorem fits {words : Nat} (bound : words ≤ width config) : words < 2 ^ w := bound.trans_lt (width_fits config)

abbrev Input := (forgery config).Value × config.handler.store.Value
abbrev Output := ((forgery config).Value × config.handler.sampler.tape.scalar.Value) × config.handler.store.Value
def input : Representation w (Input config) := (forgery config).representation.prod config.handler.store.representation
  (fits config (by unfold width; omega))
def result := (forgery config).representation.prod config.handler.sampler.tape.scalar.representation
  (fits config (by change _ + 1 ≤ _; unfold width; omega))
def output : Representation w (Output config) := (result config).prod config.handler.store.representation
  (fits config (by change (_ + 1) + _ ≤ _; unfold width; omega))
def rawPrepared := (FinalHash.rawInput config).representation.prod (forgery config).representation
  (fits config (by
    change ((config.message.representation.encoding.words + config.point.representation.encoding.words) + _) + _ ≤ _
    unfold width
    change ((config.message.representation.encoding.words + config.point.representation.encoding.words) + _) +
      (config.message.representation.encoding.words + (config.point.representation.encoding.words + 1)) ≤
        1 + 2 * (config.message.representation.encoding.words + (config.point.representation.encoding.words + 1)) + _
    omega))
def finished := (FinalHash.output config).representation.prod (forgery config).representation
  (fits config (by change (1 + _) + _ ≤ _; unfold width; omega))

def key (value : (forgery config).Value) : M × G := (value.val.1, value.val.2.1)
def rawPrepareValue (value : Input config) : (FinalHash.rawInput config).Value × (forgery config).Value :=
  (⟨(key config value.1, value.2.val), ⟨value.1.property.1, value.1.property.2.1⟩, value.2.property⟩, value.1)
def finishValue (value : (FinalHash.output config).Value × (forgery config).Value) : Output config :=
  ((value.2, ⟨value.1.val.1, value.1.property.1⟩), ⟨value.1.val.2, value.1.property.2⟩)

variable [Zero F] [DecidableEq M] [DecidableEq G]
def ready (value : Input config) : Prop :=
  FinalHash.admissible config (key config value.1, value.2.val) ∧ value.2.val.2.1.length < config.sampler.capacity
instance : DecidablePred (ready config) := fun _ => inferInstanceAs (Decidable (_ ∧ _))
def admitted := (input config).restrict (ready config)
def prepared := (FinalHash.input config).representation.prod (forgery config).representation (rawPrepared config).fits
def request (value : Input config) (valid : ready config value) : (FinalHash.input config).Value :=
  ⟨(key config value.1, value.2.val), (rawPrepareValue config value).1.property, valid.1⟩
def prepareValue (value : {value : Input config // ready config value}) := (request config value.val value.property, value.val.1)

theorem request_ready (value : Input config) (valid : ready config value) : FinalHash.ready config (request config value valid) := valid.2
theorem reserved_ready (value : Input config) (room : Handler.Reserved config 0 value.2.val) : ready config value :=
  Handler.reserved_final config (key config value.1) value.2.val room

end Signatures.Runtime.CaliperBackend.SchnorrROM.ForgeryHash
