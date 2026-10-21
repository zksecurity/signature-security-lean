import Signatures.Runtime.Caliper.SchnorrROMHandler
import Signatures.Runtime.Caliper.SynchronizesObservations
import Signatures.Runtime.SchnorrROMListPassWith

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
variable {w : Nat} {M F G : Type} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G)

/-- A signing branch's original semantics: a complete list-backend CMA handler
that agrees with the full-field handler on random and hash queries, and whose
signing query is exactly the branch's source. -/
structure SigningLaw {slots : Nat} (branch : SigningBranch config slots) where
  target : Schnorr.ListROM.Handler F G G M M
  shared : ∀ i, letI := PrivateSampler.Enumerated.sampleable config.sampler
    target (.inl i) = Schnorr.ListROM.handler (G₂ := G) (K := M) (.inl i)
  source_original : ∀ (value : config.handler.input.Value), Signing.Handler.ready config.handler 1 value →
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    Subtype.val <$> branch.source value = (Schnorr.ListROM.Shared.interpret (target (.inr value.val.1))).run value.val.2

def fullFieldLaw (scale : Implementation .unit config.handler.core.arithmetic.scaleArgs config.handler.core.point (fun value => value.1 • value.2))
    (sub : Implementation .unit config.handler.core.arithmetic.points config.handler.core.point (fun value => value.1 - value.2))
    {slots : Nat} (scaleNames : NamesBound scale.program.code slots) (subNames : NamesBound sub.program.code slots)
    (reserve : slots + 3 < 2 ^ w) {scaleTime subTime scaleWords subWords : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords) :
    SigningLaw config (fullField config scale sub scaleNames subNames reserve scaleBound subBound) where
  target := letI := PrivateSampler.Enumerated.sampleable config.sampler; Schnorr.ListROM.handler
  shared _ := rfl
  source_original value valid := Signing.Enumerated.source_original (G₂ := G) (K := M) config scale sub
    scaleNames.buffers subNames.buffers reserve value valid

variable (ops : Operations config) (law : SigningLaw config ops.signing)

theorem source_original (value : Input config) (valid : ready config value) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    observed config <$> source config ops value =
      (fun answer => (representReply config value answer.1, answer.2)) <$>
        (Schnorr.ListROM.Shared.interpret (law.target (query config value))).run (initialStore config value) := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  rcases value with (value | value) | value
  · have same := Random.source_original (G₂ := G) (K := M) config value
    have mapped := congrArg (Functor.map (fun answer : (Nat × Nat) × Schnorr.ListROM.Shared.Store F G M =>
      ((.inl (.inl answer.1) : Reply (F := F) (G := G)), answer.2))) same
    simp only [source, Sum.elim, randomSource, Functor.map_map, observed, representReply, query, initialStore, law.shared] at mapped ⊢
    convert mapped using 1
  · have same := Hash.source_original (G₂ := G) (K := M) config value valid
    have mapped := congrArg (Functor.map (fun answer : F × Schnorr.ListROM.Shared.Store F G M =>
      ((.inl (.inr answer.1) : Reply (F := F) (G := G)), answer.2))) same
    simp only [source, Sum.elim, hashSource, Functor.map_map, observed, representReply, query, initialStore, law.shared] at mapped ⊢
    convert mapped using 1
  · have same := law.source_original value valid
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
      ((Schnorr.ListROM.Shared.interpret (law.target (query config value))).run (initialStore config value)) := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have joint := Synchronizes.of_map_eq (observed config)
    (fun answer : (FiatShamir.cmaOracleSpec M G F F).Range (query config value) × Schnorr.ListROM.Shared.Store F G M =>
      (representReply config value answer.1, answer.2))
    (source_original config ops law value valid)
  exact joint.mono (fun _ _ equal => Prod.mk.inj equal)

theorem observe_original (random : RandomTape w) (value : Input config) (valid : ready config value)
    (before : State w) (holds : (input config).Holds value before) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    (fun result => (Interactive.observe (output config) result).map (observed config)) <$>
        (code config ops).execute (Fresh.port config.handler.sampler.tape) .unit random before =
      (fun answer => some (representReply config value answer.1, answer.2)) <$>
        (Schnorr.ListROM.Shared.interpret (law.target (query config value))).run (initialStore config value) := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have executed := (refines config ops).observe random value valid before holds
  have erased := congrArg (Functor.map (Option.map (observed config))) executed
  simp only [Functor.map_map, Option.map_some] at erased
  have same := source_original config ops law value valid
  simpa only [Functor.map_map, Option.map_some] using erased.trans (by
    simpa only [Functor.map_map] using congrArg (Functor.map some) same)

end Original
end Signatures.Runtime.CaliperBackend.SchnorrROM.Handler
