import Signatures.Runtime.Caliper.SchnorrROMHandler
import Signatures.Runtime.Caliper.SynchronizesObservations

/-! The service's tagged reply and complete store agree with the original
dependent CMA query. The pending request supplies the reply's original type;
random replies also carry their requested range in the executed packet. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Handler
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
section Layout
variable {w : Nat} {M F G : Type} [Zero F] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G)

abbrev Reply := ((Nat × Nat) ⊕ F) ⊕ (G × F)
def query : Input config → (Nat ⊕ (M × G)) ⊕ M
  | .inl (.inl value) => .inl (.inl value.val.1)
  | .inl (.inr value) => .inl (.inr value.val.1)
  | .inr value => .inr value.val.1
def initialStore : Input config → Schnorr.ListROM.Shared.Store F G M
  | .inl (.inl value) => value.val.2
  | .inl (.inr value) => value.val.2
  | .inr value => value.val.2
def observed : Output config → Reply (F := F) (G := G) × Schnorr.ListROM.Shared.Store F G M
  | .inl (.inl value) => (.inl (.inl value.val.1), value.val.2)
  | .inl (.inr value) => (.inl (.inr value.val.1), value.val.2)
  | .inr value => (.inr value.val.1, value.val.2)
def representReply : (value : Input config) → (FiatShamir.cmaOracleSpec M G F F).Range (query config value) → Reply (F := F) (G := G)
  | .inl (.inl value), answer => .inl (.inl (value.val.1, answer.val))
  | .inl (.inr _), answer => .inl (.inr answer)
  | .inr _, answer => .inr answer

end Layout

section Original
variable {w : Nat} {M F G G₂ K : Type} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G]
    [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K]
    (config : Signing.Enumerated.Configuration w M F G) (ops : Operations config)

theorem source_original (value : Input config) (valid : ready config value) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    observed config <$> source config ops value =
      (fun answer => (representReply config value answer.1, answer.2)) <$>
        (Schnorr.ListROM.Shared.interpret
          (Schnorr.ListROM.handler (G₂ := G₂) (K := K) (query config value))).run (initialStore config value) := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  rcases value with (value | value) | value
  · have same := Random.source_original (G₂ := G₂) (K := K) config value
    have mapped := congrArg (Functor.map (fun answer : (Nat × Nat) × Schnorr.ListROM.Shared.Store F G M =>
      ((.inl (.inl answer.1) : Reply (F := F) (G := G)), answer.2))) same
    simp only [source, Sum.elim, randomSource, Functor.map_map, observed, representReply, query, initialStore] at mapped ⊢
    convert mapped using 1
  · have same := Hash.source_original (G₂ := G₂) (K := K) config value valid
    have mapped := congrArg (Functor.map (fun answer : F × Schnorr.ListROM.Shared.Store F G M =>
      ((.inl (.inr answer.1) : Reply (F := F) (G := G)), answer.2))) same
    simp only [source, Sum.elim, hashSource, Functor.map_map, observed, representReply, query, initialStore] at mapped ⊢
    convert mapped using 1
  · have same := Signing.Enumerated.source_original (G₂ := G₂) (K := K) config
      ops.scale ops.sub ops.scaleNames.buffers ops.subNames.buffers ops.reserve value valid
    have mapped := congrArg (Functor.map (fun answer : (G × F) × Schnorr.ListROM.Shared.Store F G M =>
      ((.inr answer.1 : Reply (F := F) (G := G)), answer.2))) same
    simp only [source, Sum.elim, signingSource, signSource, Functor.map_map, observed, representReply, query, initialStore] at mapped ⊢
    convert mapped using 1

theorem synchronizes (value : Input config) (valid : ready config value) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    Synchronizes (fun represented original =>
      (observed config represented).1 = representReply config value original.1 ∧
      (observed config represented).2 = original.2)
      (source config ops value)
      ((Schnorr.ListROM.Shared.interpret
        (Schnorr.ListROM.handler (G₂ := G₂) (K := K) (query config value))).run (initialStore config value)) := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have joint := Synchronizes.of_map_eq (observed config)
    (fun answer : (FiatShamir.cmaOracleSpec M G F F).Range (query config value) × Schnorr.ListROM.Shared.Store F G M =>
      (representReply config value answer.1, answer.2))
    (source_original (G₂ := G₂) (K := K) config ops value valid)
  exact joint.mono (fun _ _ equal => Prod.mk.inj equal)

theorem observe_original (random : RandomTape w) (value : Input config) (valid : ready config value)
    (before : State w) (holds : (input config).Holds value before) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    (fun result => (Interactive.observe (output config) result).map (observed config)) <$>
        (code config ops).execute (Fresh.port config.handler.sampler.tape) .unit random before =
      (fun answer => some (representReply config value answer.1, answer.2)) <$>
        (Schnorr.ListROM.Shared.interpret
          (Schnorr.ListROM.handler (G₂ := G₂) (K := K) (query config value))).run (initialStore config value) := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have executed := (refines config ops).observe random value valid before holds
  have erased := congrArg (Functor.map (Option.map (observed config))) executed
  simp only [Functor.map_map, Option.map_some] at erased
  have same := source_original (G₂ := G₂) (K := K) config ops value valid
  simpa only [Functor.map_map, Option.map_some] using erased.trans (by
    simpa only [Functor.map_map] using congrArg (Functor.map some) same)

end Original
end Signatures.Runtime.CaliperBackend.SchnorrROM.Handler
