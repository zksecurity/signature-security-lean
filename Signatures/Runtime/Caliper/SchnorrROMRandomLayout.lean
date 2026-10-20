import Signatures.Runtime.Caliper.SchnorrROMFinalHashLayout

/-! The adversary's dynamic random-query range and the complete shared store.
The reply echoes the range and carries a bounded natural answer. Only the saved
replay tape reserves a slot; neither hash table requires insertion room. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Random
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

theorem caches_le : config.handler.caches.representation.encoding.words ≤ 3 * config.handler.width := by
  have bound := FinalHash.store_le config
  change config.handler.caches.representation.encoding.words + _ ≤ _ at bound
  omega
theorem tapes_le : (Read.tapes config.handler.sampler.tape).representation.encoding.words ≤ config.handler.width := by
  rw [Signing.Handler.Layouts.width_eq]
  omega
theorem positive : 0 < config.handler.width := by change 0 < 1 + _ + _ + _ + _ + _; omega

def rawInput := (Reply.range config.handler.sampler.tape).prod config.handler.store
  (config.handler.fits_of_le (by
    have := FinalHash.store_le config; have := positive config
    change 1 + _ ≤ _; omega))
def ready (value : Nat × Schnorr.ListROM.Shared.Store F G M) : Prop := value.2.2.1.length < config.sampler.capacity
instance (value : Nat × Schnorr.ListROM.Shared.Store F G M) : Decidable (ready config value) :=
  inferInstanceAs (Decidable (_ < _))
def input := (rawInput config).restrict (ready config)
def replyRaw := (Reply.range config.handler.sampler.tape).prod config.handler.sampler.tape.counter
  (by change 1 + 1 < _; have := config.sampler.wordFits; omega)
def reply := (replyRaw config).restrict (fun value => value.2 ≤ value.1)
def output := (reply config).prod config.handler.store
  (config.handler.fits_of_le (by
    have := FinalHash.store_le config; have := positive config
    change 2 + _ ≤ _; omega))
def prepared := (Caller.privateInput config.handler.sampler.tape).representation.prod config.handler.caches.representation
  (config.handler.fits_of_le (by
    have := caches_le config; have := tapes_le config; have := positive config
    change (1 + (Read.tapes config.handler.sampler.tape).representation.encoding.words) + _ ≤ _; omega))
def finished := (Reply.privateOutput config.handler.sampler.tape).representation.prod config.handler.caches.representation
  (config.handler.fits_of_le (by
    have := caches_le config; have := tapes_le config; have := positive config
    change (1 + (1 + (Read.tapes config.handler.sampler.tape).representation.encoding.words)) + _ ≤ _; omega))

def request (value : (input config).Value) : (Caller.privateInput config.handler.sampler.tape).Value :=
  ⟨(value.val.1, value.val.2.2), value.property.1.1,
    ⟨value.property.1.2.2.1, value.property.2⟩, value.property.1.2.2.2⟩
def context (value : (input config).Value) : config.handler.caches.Value :=
  ⟨value.val.2.1, value.property.1.2.1⟩
def prepareValue (value : (input config).Value) := (request config value, context config value)
def finishValue (value : (Reply.privateOutput config.handler.sampler.tape).Value × config.handler.caches.Value) :
    (output config).Value :=
  ⟨((value.1.val.1, value.1.val.2.1), value.2.val, value.1.val.2.2),
    ⟨⟨value.1.property.1.1, value.1.property.1.2.1⟩, value.1.property.2⟩,
    value.2.property, value.1.property.1.2.2⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.Random
