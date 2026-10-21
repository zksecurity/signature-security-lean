import Signatures.Runtime.Caliper.SchnorrROMCallerHandler

/-! Joint reply/state correspondence for independent caller packets. The pending
request supplies the dependent reply type. Reservations survive every supported
reply, so an adaptive caller can use the same service on its next step. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.CallerHandler
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec CallerPackets
section Layout
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

def query : CallerPackets.Request config → (Nat ⊕ (M × G)) ⊕ M
  | .inl (.inl range) => .inl (.inl range.val)
  | .inl (.inr key) => .inl (.inr key.val)
  | .inr message => .inr message.val
def replyValue : Reply config → Handler.Reply (F := F) (G := G)
  | .inl (.inl value) => .inl (.inl value.val)
  | .inl (.inr value) => .inl (.inr value.val)
  | .inr value => .inr value.val
def observed (value : Reply config × config.handler.store.Value) :
    Handler.Reply (F := F) (G := G) × Schnorr.ListROM.Shared.Store F G M :=
  (replyValue config value.1, value.2.val)
def representReply : (request : CallerPackets.Request config) → (FiatShamir.cmaOracleSpec M G F F).Range (query config request) →
    Handler.Reply (F := F) (G := G)
  | .inl (.inl range), answer => .inl (.inl (range.val, answer.val))
  | .inl (.inr _), answer => .inl (.inr answer)
  | .inr _, answer => .inr answer

theorem observed_finished (value : Handler.Output config) :
    observed config (finished config value) = Handler.observed config value := by
  rcases value with (value | value) | value <;> rfl

variable [Zero F] [DecidableEq M] [DecidableEq G] [SMul F G] [Sub G] (ops : Handler.Operations config)
theorem reserved_after (remaining : Nat) (value : Packet config)
    (room : Handler.Reserved config (remaining + 1) value.2.val)
    (answer : Reply config × config.handler.store.Value) (reached : answer ∈ support (source config ops value)) :
    answer.2.val.1.1 = value.2.val.1.1 ∧ Handler.Reserved config remaining answer.2.val := by
  have valid := reserved_ready config remaining value room
  simp only [source, dite_eq_left valid, support_map, Set.mem_image] at reached
  obtain ⟨result, supported, rfl⟩ := reached
  have after := Handler.reserved_after config ops remaining (serviceRequest config value valid)
    (by simpa only [service_store] using room) result supported
  rw [← observed_finished, service_store] at after
  exact after
end Layout

section Original
variable {w : Nat} {M F G : Type} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (ops : Handler.Operations config)
    (law : Handler.SigningLaw config ops.signing)

theorem source_original (value : Packet config) (valid : ready config value) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    observed config <$> source config ops value =
      (fun answer => (representReply config value.1 answer.1, answer.2)) <$>
        (Schnorr.ListROM.Shared.interpret
          (law.target (query config value.1))).run value.2.val := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have same := Handler.source_original config ops law
    (serviceRequest config value valid) (service_ready config value valid)
  simp only [source, dite_eq_left valid, Functor.map_map, observed_finished]
  rcases value with ⟨(range | key) | message, saved⟩ <;> convert same using 1 <;> rfl

theorem synchronizes (value : Packet config) (valid : ready config value) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    Synchronizes (fun represented original =>
      replyValue config represented.1 = representReply config value.1 original.1 ∧ represented.2.val = original.2)
      (source config ops value)
      ((Schnorr.ListROM.Shared.interpret
        (law.target (query config value.1))).run value.2.val) := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have joint := Synchronizes.of_map_eq (observed config)
    (fun answer : (FiatShamir.cmaOracleSpec M G F F).Range (query config value.1) × Schnorr.ListROM.Shared.Store F G M =>
      (representReply config value.1 answer.1, answer.2))
    (source_original config ops law value valid)
  exact joint.mono (fun _ _ equal => Prod.mk.inj equal)

theorem observe_original (random : RandomTape w) (value : Packet config) (valid : ready config value)
    (before : State w) (holds : (input config).Holds value before) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    (fun result => (Interactive.observe (output config) result).map (observed config)) <$>
        (code config ops).execute (Fresh.port config.handler.sampler.tape) .unit random before =
      (fun answer => some (representReply config value.1 answer.1, answer.2)) <$>
        (Schnorr.ListROM.Shared.interpret
          (law.target (query config value.1))).run value.2.val := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have executed := (refines config ops).observe random value valid before holds
  have erased := congrArg (Functor.map (Option.map (observed config))) executed
  simp only [Functor.map_map, Option.map_some] at erased
  have same := source_original config ops law value valid
  simpa only [Functor.map_map, Option.map_some] using erased.trans (by
    simpa only [Functor.map_map] using congrArg (Functor.map some) same)

end Original
end Signatures.Runtime.CaliperBackend.SchnorrROM.CallerHandler
