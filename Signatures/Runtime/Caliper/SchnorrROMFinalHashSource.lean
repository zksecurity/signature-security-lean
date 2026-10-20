import Signatures.Runtime.Caliper.SchnorrROMFinalHash
import Signatures.Runtime.SchnorrRawTapeBounds

/-! Final hashing is the original shared-tape final verification lookup. The
source equality preserves the complete joint reply, both tables and both tapes. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.FinalHash
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} [Zero F] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G)

def resultValue (value : (input config).Value) (read : (F × Signing.Table M F G) × Schnorr.ListROM.Shared.Tape F) :=
  (read.1.1, (value.val.2.1.1, value.val.2.1.2.1, read.1.2), read.2)

theorem source_value (value : (input config).Value) (valid : ready config value) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    Subtype.val <$> source config value =
      match cacheMap value.val.2.1.2.2 value.val.1 with
      | some challenge => pure (challenge, value.val.2)
      | none => (fun fresh => (fresh.1, (value.val.2.1.1, value.val.2.1.2.1,
          (value.val.1, fresh.1) :: value.val.2.1.2.2), fresh.2)) <$>
          (Caller.scalarResult <$> simulateQ _root_.Schnorr.LazyROM.sample
            ((Schnorr.RawTape.oracle (.inr ())).run ⟨value.val.2.2.1, value.val.2.2.2⟩)) := by
  have original := congrArg (Functor.map (resultValue config value))
    (HashCache.source_original config (request config value, tapes config value) valid)
  have first := (PFunctor.FreeM.comp_map Subtype.val
    (fun read => finishValue config (read, context config value))
    (HashCache.source config (request config value, tapes config value))).symm
  have second := PFunctor.FreeM.comp_map (resultValue config value)
    (fun read : (CacheRead.output (HashCache.model config).cache).Value × (Read.tapes config.handler.sampler.tape).Value =>
      (read.1.val, read.2.val)) (HashCache.source config (request config value, tapes config value))
  have joint := first.trans (second.trans original)
  refine joint.trans ?_
  dsimp only [request, tapes]
  cases found : cacheMap value.val.2.1.2.2 value.val.1 <;> simp only [map_pure]
  · exact (PFunctor.FreeM.comp_map _ _ _).symm
  · rfl

theorem tape_lengths (value : (input config).Value) (valid : ready config value)
    (answer : (output config).Value) (reached : answer ∈ support (source config value)) :
    answer.val.2.2.1.length ≤ value.val.2.2.1.length + 1 ∧
      answer.val.2.2.2.length ≤ value.val.2.2.2.length := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have erased : answer.val ∈ support (Subtype.val <$> source config value) := by
    rw [support_map]
    exact ⟨answer, reached, rfl⟩
  rw [source_value config value valid] at erased
  cases found : cacheMap value.val.2.1.2.2 value.val.1 with
  | none =>
    simp only [found, Functor.map_map, support_map, Set.mem_image] at erased
    obtain ⟨read, supported, same⟩ := erased
    rw [← same]
    exact Schnorr.RawTape.oracle_lengths _root_.Schnorr.LazyROM.sample (.inr ())
      ⟨value.val.2.2.1, value.val.2.2.2⟩ read supported
  | some challenge =>
    simp only [found, support_pure, Set.mem_singleton_iff] at erased
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
      (Schnorr.ListROM.Shared.interpret (Schnorr.ListROM.finalHash (G₂ := G₂) (K := K) value.val.1)).run value.val.2 := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  rw [source_value config value valid, Schnorr.ListROM.Shared.finalHash_run]
  cases found : cacheMap value.val.2.1.2.2 value.val.1
  · simp only [Schnorr.ListROM.Shared.tapeRun, simulateQ_spec_query]
    rfl
  · rfl

theorem observe_original (random : RandomTape w) (value : (input config).Value) (valid : ready config value)
    (before : State w) (holds : (input config).representation.Holds value before) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    (fun result => (Interactive.observe (output config).representation result).map Subtype.val) <$>
        (code config).execute (Fresh.port config.handler.sampler.tape) .unit random before =
      some <$> (Schnorr.ListROM.Shared.interpret
        (Schnorr.ListROM.finalHash (G₂ := G₂) (K := K) value.val.1)).run value.val.2 := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have observed := (refines config).observe random value valid before holds
  have erased := congrArg (Functor.map (Option.map Subtype.val)) observed
  simp only [Functor.map_map, Option.map_some] at erased
  have same := source_original (G₂ := G₂) (K := K) config value valid
  simpa only [Functor.map_map, Option.map_some] using erased.trans (by
    simpa only [Functor.map_map] using congrArg (Functor.map some) same)

end Original
end Signatures.Runtime.CaliperBackend.SchnorrROM.FinalHash
