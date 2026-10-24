import Proofs.Runtime.Caliper.SchnorrROMHash

/-! Normal hashing agrees with the original shared-tape hash handler, including
the joint returned scalar, distinct managed/LIVE tables and both replay tapes. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Hash
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} [Zero F] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G)

def resultValue (read : (F × Signing.Table M F G) × (HashMiss.input config).Value) :=
  (read.1.1, (read.2.val.2.1.1, read.1.2, read.2.val.2.1.2.2), read.2.val.2.2)
def insertedValue (value : (input config).Value) (answer : (FinalHash.output config).Value) :=
  (answer.val.1, (answer.val.2.1.1, (value.val.1, answer.val.1) :: value.val.2.1.2.1,
    answer.val.2.1.2.2), answer.val.2.2)

theorem source_value (value : (input config).Value) (valid : ready config value) :
    Subtype.val <$> source config value =
      if missing : cacheMap value.val.2.1.2.1 value.val.1 = none then
        insertedValue config value <$> FinalHash.source config (HashMiss.admitted config (saved config value) (valid missing).1)
      else pure ((cacheMap value.val.2.1.2.1 value.val.1).getD 0, value.val.2) := by
  have reduced := StatefulCacheRead.denote_value (base := cryptoBase F G Unit M M) (key := Signing.Cache.keyTy) (val := scalar)
    (model config) (Signing.Cache.primitives F G M) Signing.Cache.comparison (Signing.Cache.comparison_correct F G M)
    (HashMiss.source config) (prepareValue config value)
  have erased := congrArg (Functor.map (resultValue config)) reduced
  have first := (PFunctor.FreeM.comp_map Subtype.val (finishValue config)
    (cacheSource config (prepareValue config value))).symm
  have second := PFunctor.FreeM.comp_map (resultValue config)
    (fun read : (CacheRead.output (model config).cache).Value × (HashMiss.input config).Value => (read.1.val, read.2))
    (cacheSource config (prepareValue config value))
  have joint := first.trans (second.trans erased)
  have looked := lookupExpr_value (val := scalar) (Signing.Cache.primitives F G M) Signing.Cache.comparison
    (Signing.Cache.comparison_correct F G M) value.val.1 (0 : F) value.val.2.1.2.1
  simp only [Expr.run_value] at looked
  change Subtype.val <$> source config value =
    resultValue config <$> (if ((lookupExpr (val := scalar) Signing.Cache.comparison).denote
      (Signing.Cache.primitives F G M) (value.val.1, 0, value.val.2.1.2.1, ())).1 = true then
      pure ((((lookupExpr (val := scalar) Signing.Cache.comparison).denote (Signing.Cache.primitives F G M)
        (value.val.1, 0, value.val.2.1.2.1, ())).2, value.val.2.1.2.1), saved config value)
      else (fun fresh => ((fresh.1.val, (value.val.1, fresh.1.val) :: value.val.2.1.2.1), fresh.2)) <$>
        HashMiss.source config (saved config value)) at joint
  rw [looked, lookupValue_cacheMap] at joint
  refine joint.trans ?_
  by_cases missing : cacheMap value.val.2.1.2.1 value.val.1 = none
  · rw [dite_eq_left missing]
    simp only [missing, Bool.false_eq_true, ite_false]
    rw [HashMiss.source, HashMiss.innerSource, dite_eq_left (valid missing).1]
    simp only [Functor.map_map]
    rfl
  · rw [dite_eq_right missing]
    cases found : cacheMap value.val.2.1.2.1 value.val.1 with
    | none => exact False.elim (missing found)
    | some challenge =>
      simp only [ite_true, map_pure, Option.getD_some]
      rfl

theorem postcondition (value : (input config).Value) (valid : ready config value)
    (answer : (output config).Value) (reached : answer ∈ support (source config value)) :
    answer.val.2.1.1 = value.val.2.1.1 ∧
      answer.val.2.1.2.1.length ≤ value.val.2.1.2.1.length + 1 ∧
      answer.val.2.1.2.2.length ≤ value.val.2.1.2.2.length + 1 := by
  have erased : answer.val ∈ support (Subtype.val <$> source config value) := by
    rw [support_map]
    exact ⟨answer, reached, rfl⟩
  rw [source_value config value valid] at erased
  by_cases missing : cacheMap value.val.2.1.2.1 value.val.1 = none
  · rw [dite_eq_left missing] at erased
    simp only [support_map, Set.mem_image] at erased
    obtain ⟨read, supported, same⟩ := erased
    rw [← same]
    have cfg := FinalHash.preserves_config config (HashMiss.admitted config (saved config value) (valid missing).1) read supported
    have live := FinalHash.live_length config (HashMiss.admitted config (saved config value) (valid missing).1) read supported
    exact ⟨cfg, by simp only [insertedValue, List.length_cons]; exact Nat.le_refl _, live⟩
  · rw [dite_eq_right missing] at erased
    simp only [support_pure, Set.mem_singleton_iff] at erased
    rw [erased]
    exact ⟨rfl, Nat.le_succ _, Nat.le_succ _⟩

theorem reserved_after (reserve : Nat) (value : (input config).Value) (valid : ready config value)
    (managedRoom : value.val.2.1.2.1.length + (reserve + 1) ≤ config.capacityPred + 1)
    (liveRoom : value.val.2.1.2.2.length + (reserve + 1) ≤ config.capacityPred + 1)
    (answer : (output config).Value) (reached : answer ∈ support (source config value)) :
    answer.val.2.1.2.1.length + reserve ≤ config.capacityPred + 1 ∧
      answer.val.2.1.2.2.length + reserve ≤ config.capacityPred + 1 := by
  have growth := postcondition config value valid answer reached
  constructor <;> omega

theorem tape_lengths (value : (input config).Value) (valid : ready config value)
    (answer : (output config).Value) (reached : answer ∈ support (source config value)) :
    answer.val.2.2.1.length ≤ value.val.2.2.1.length + 1 ∧
      answer.val.2.2.2.length ≤ value.val.2.2.2.length := by
  have erased : answer.val ∈ support (Subtype.val <$> source config value) := by
    rw [support_map]
    exact ⟨answer, reached, rfl⟩
  rw [source_value config value valid] at erased
  by_cases missing : cacheMap value.val.2.1.2.1 value.val.1 = none
  · rw [dite_eq_left missing] at erased
    simp only [support_map, Set.mem_image] at erased
    obtain ⟨read, supported, same⟩ := erased
    rw [← same]
    exact FinalHash.tape_lengths config (HashMiss.admitted config (saved config value) (valid missing).1)
      (valid missing).2 read supported
  · rw [dite_eq_right missing] at erased
    simp only [support_pure, Set.mem_singleton_iff] at erased
    rw [erased]
    exact ⟨Nat.le_succ _, le_rfl⟩

theorem tape_reserved_after (reserve : Nat) (value : (input config).Value) (valid : ready config value)
    (room : value.val.2.2.1.length + (reserve + 1) ≤ config.sampler.capacity)
    (answer : (output config).Value) (reached : answer ∈ support (source config value)) :
    answer.val.2.2.1.length + reserve ≤ config.sampler.capacity := by
  have growth := tape_lengths config value valid answer reached
  omega

section Original
variable {w : Nat} {M F G G₂ K : Type} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G] [DecidableEq M]
    [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K]
    (config : Signing.Enumerated.Configuration w M F G)

theorem source_original (value : (input config).Value) (valid : ready config value) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    Subtype.val <$> source config value =
      (Schnorr.ListROM.Shared.interpret
        (Schnorr.ListROM.handler (G₂ := G₂) (K := K) (.inl (.inr value.val.1)))).run value.val.2 := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  rw [source_value config value valid, Schnorr.ListROM.Shared.hash_run]
  by_cases managed : cacheMap value.val.2.1.2.1 value.val.1 = none
  · rw [dite_eq_left managed, managed]
    have final := FinalHash.source_value config (HashMiss.admitted config (saved config value) (valid managed).1) (valid managed).2
    let insert : F × Schnorr.ListROM.Shared.Store F G M → F × Schnorr.ListROM.Shared.Store F G M :=
      fun answer => (answer.1, (answer.2.1.1, (value.val.1, answer.1) :: value.val.2.1.2.1, answer.2.1.2.2), answer.2.2)
    have mapped := congrArg (Functor.map insert) final
    have combined := (PFunctor.FreeM.comp_map insert Subtype.val
      (FinalHash.source config (HashMiss.admitted config (saved config value) (valid managed).1))).trans mapped
    refine combined.trans ?_
    dsimp only [HashMiss.admitted, saved]
    cases live : cacheMap value.val.2.1.2.2 value.val.1
    · simp only [Schnorr.ListROM.Shared.tapeRun, simulateQ_spec_query, Functor.map_map]
      rfl
    · simp only [map_pure]
      rfl
  · rw [dite_eq_right managed]
    cases found : cacheMap value.val.2.1.2.1 value.val.1 with
    | none => exact False.elim (managed found)
    | some challenge => rfl

theorem observe_original (random : RandomTape w) (value : (input config).Value) (valid : ready config value)
    (before : State w) (holds : (input config).representation.Holds value before) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    (fun result => (Interactive.observe (output config).representation result).map Subtype.val) <$>
        (code config).execute (Fresh.port config.handler.sampler.tape) .unit random before =
      some <$> (Schnorr.ListROM.Shared.interpret
        (Schnorr.ListROM.handler (G₂ := G₂) (K := K) (.inl (.inr value.val.1)))).run value.val.2 := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have observed := (refines config).observe random value valid before holds
  have erased := congrArg (Functor.map (Option.map Subtype.val)) observed
  simp only [Functor.map_map, Option.map_some] at erased
  have same := source_original (G₂ := G₂) (K := K) config value valid
  simpa only [Functor.map_map, Option.map_some] using erased.trans (by
    simpa only [Functor.map_map] using congrArg (Functor.map some) same)

end Original
end Signatures.Runtime.CaliperBackend.SchnorrROM.Hash
