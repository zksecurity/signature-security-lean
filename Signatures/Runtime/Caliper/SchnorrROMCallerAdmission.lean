import Signatures.Runtime.Caliper.SchnorrROMCallerPackets

/-! Caller admission is a reachable-state condition. The service's bounded
input is a byte-identical view of the already executed packet conversion.
Remaining-call reservations establish every branch's capacity requirements. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.CallerPackets
open Caliper BoundedSource
variable {w : Nat} {M F G : Type} [Zero F] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G)

def ready (value : Packet config) : Prop :=
  match value.1 with
  | .inl (.inl _) => value.2.val.2.1.length < config.sampler.capacity
  | .inl (.inr key) => Hash.admissible config (key.val, value.2.val) ∧
      (cacheMap value.2.val.1.2.1 key.val = none →
        FinalHash.admissible config (key.val, value.2.val) ∧ value.2.val.2.1.length < config.sampler.capacity)
  | .inr _ => value.2.val.1.2.1.length ≤ config.capacityPred ∧ value.2.val.2.1.length + 3 ≤ config.sampler.capacity
instance : DecidablePred (ready config) := fun value => by
  rcases value with ⟨(range | key) | message, saved⟩ <;> dsimp [ready] <;> infer_instance

def serviceRequest (value : Packet config) (valid : ready config value) : Handler.Input config :=
  match value with
  | (.inl (.inl range), saved) => .inl (.inl ⟨(range.val, saved.val), ⟨range.property, saved.property⟩, valid⟩)
  | (.inl (.inr key), saved) => .inl (.inr ⟨(key.val, saved.val), ⟨key.property, saved.property⟩, valid.1⟩)
  | (.inr message, saved) => .inr ⟨(message.val, saved.val), ⟨message.property, saved.property⟩, valid.1⟩
theorem request_bytes (value : Packet config) (valid : ready config value) :
    (Handler.input config).encoding.encode (serviceRequest config value valid) =
      (raw config).encoding.encode (prepared config value) := by
  rcases value with ⟨(range | key) | message, saved⟩ <;> rfl
theorem service_ready (value : Packet config) (valid : ready config value) :
    Handler.ready config (serviceRequest config value valid) := by
  rcases value with ⟨(range | key) | message, saved⟩
  · trivial
  · exact valid.2
  · exact valid.2
theorem service_store (value : Packet config) (valid : ready config value) :
    Handler.initialStore config (serviceRequest config value valid) = value.2.val := by
  rcases value with ⟨(range | key) | message, saved⟩ <;> rfl

def admitted := (input config).restrict (ready config)
def prepareService : Realizer .unit (admitted config) (Handler.input config)
    (fun value => serviceRequest config value.val value.property) :=
  ((prepare config).viewInput (admitted config) Subtype.val (fun _ => rfl)).viewOutput (Handler.input config)
    (fun value => serviceRequest config value.val value.property) (fun value => request_bytes config value.val value.property)

theorem reserved_ready (remaining : Nat) (value : Packet config)
    (room : Handler.Reserved config (remaining + 1) value.2.val) : ready config value := by
  rcases value with ⟨(range | key) | message, saved⟩ <;>
    dsimp only [Handler.Reserved] at room <;> dsimp only [ready]
  · exact lt_of_lt_of_le (by omega) room.2.2
  · rcases room with ⟨managed, live, tape⟩
    constructor
    · intro _
      change saved.val.1.2.1.length ≤ config.capacityPred
      omega
    · intro _
      constructor
      · intro _
        change saved.val.1.2.2.length ≤ config.capacityPred
        omega
      · omega
  · rcases room with ⟨managed, _, tape⟩
    constructor <;> omega

end Signatures.Runtime.CaliperBackend.SchnorrROM.CallerPackets
