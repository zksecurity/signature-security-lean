import Proofs.Runtime.Caliper.SchnorrROMForgeryHash

/-! The returned forgery and final challenge have exactly the original LIVE
lookup law, jointly with both caches and tapes. Only one LIVE entry and saved
tape cell can be added by this terminal lookup. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ForgeryHash
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
section Layout
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)
def observed (value : Output config) : ((M × G × F) × F) × Schnorr.ListROM.Shared.Store F G M :=
  ((value.1.1.val, value.1.2.val), value.2.val)

variable [Zero F] [DecidableEq M] [DecidableEq G]
theorem growth (value : Input config) (valid : ready config value) (answer : Output config)
    (reached : answer ∈ support (source config value)) :
    answer.2.val.1.2.2.length ≤ value.2.val.1.2.2.length + 1 ∧
    answer.2.val.2.1.length ≤ value.2.val.2.1.length + 1 ∧ answer.2.val.2.2.length ≤ value.2.val.2.2.length := by
  simp only [source, dite_eq_left valid, support_map, Set.mem_image] at reached
  obtain ⟨hashed, supported, rfl⟩ := reached
  exact ⟨FinalHash.live_length config _ hashed supported,
    FinalHash.tape_lengths config _ (request_ready config value valid) hashed supported⟩
end Layout

section Original
variable {w : Nat} {M F G G₂ K : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]
    [DecidableEq M] [DecidableEq G] [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K]
    (config : Signing.Enumerated.Configuration w M F G)

theorem source_original (value : Input config) (valid : ready config value) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    observed config <$> source config value =
      (fun hashed => ((value.1.val, hashed.1), hashed.2)) <$>
        (Schnorr.ListROM.Shared.interpret
          (Schnorr.ListROM.finalHash (G₂ := G₂) (K := K) (key config value.1))).run value.2.val := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have same := FinalHash.source_original (G₂ := G₂) (K := K) config
    (request config value valid) (request_ready config value valid)
  have mapped := congrArg (Functor.map (fun hashed : F × Schnorr.ListROM.Shared.Store F G M =>
    ((value.1.val, hashed.1), hashed.2))) same
  simp only [source, dite_eq_left valid, Functor.map_map, observed, finishValue] at mapped ⊢
  convert mapped using 1
  rfl

theorem observe_original (random : RandomTape w) (value : Input config) (valid : ready config value)
    (before : State w) (holds : (input config).Holds value before) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    (fun result => (Interactive.observe (output config) result).map (observed config)) <$>
        (code config).execute (Fresh.port config.handler.sampler.tape) .unit random before =
      (fun hashed => some ((value.1.val, hashed.1), hashed.2)) <$>
        (Schnorr.ListROM.Shared.interpret
          (Schnorr.ListROM.finalHash (G₂ := G₂) (K := K) (key config value.1))).run value.2.val := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have executed := (refines config).observe random value valid before holds
  have erased := congrArg (Functor.map (Option.map (observed config))) executed
  simp only [Functor.map_map, Option.map_some] at erased
  have same := source_original (G₂ := G₂) (K := K) config value valid
  simpa only [Functor.map_map, Option.map_some] using erased.trans (by
    simpa only [Functor.map_map] using congrArg (Functor.map some) same)

end Original
end Signatures.Runtime.CaliperBackend.SchnorrROM.ForgeryHash
