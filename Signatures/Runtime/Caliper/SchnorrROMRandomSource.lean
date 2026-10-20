import Signatures.Runtime.Caliper.SchnorrROMRandom
import Signatures.Runtime.SchnorrRawTapeBounds

/-! The dynamic random handler matches the original private query of the
shared-tape CMA service. The retained range and complete store are observed
jointly; the decoded natural answer represents the original finite reply. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Random
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} [Zero F] (config : Signing.Enumerated.Configuration w M F G)

def rawResult (value : (input config).Value) (answer : Fin (value.val.1 + 1) × Schnorr.RawTape.State F) :=
  ((value.val.1, answer.1.val), value.val.2.1, answer.2.saved, answer.2.remaining)
def joinResult (value : (input config).Value) (answer : Nat × Nat × Schnorr.ListROM.Shared.Tape F) :=
  ((answer.1, answer.2.1), value.val.2.1, answer.2.2)

theorem source_value (value : (input config).Value) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    Subtype.val <$> source config value = rawResult config value <$>
      simulateQ _root_.Schnorr.LazyROM.sample
        ((Schnorr.RawTape.oracle (.inl value.val.1)).run ⟨value.val.2.2.1, value.val.2.2.2⟩) := by
  have original := EnumeratedReplay.private_source config.sampler value.val.1
    ⟨value.val.2.2.1, value.val.2.2.2⟩ (request config value).property
  have mapped := congrArg (Functor.map (joinResult config value)) original
  have first := (PFunctor.FreeM.comp_map Subtype.val (fun read => finishValue config (read, context config value))
    (bodySource config (request config value))).symm
  have second := PFunctor.FreeM.comp_map (joinResult config value) Subtype.val (bodySource config (request config value))
  have joint := first.trans (second.trans mapped)
  exact joint.trans (PFunctor.FreeM.comp_map _ _ _).symm

theorem preserves_range (value : (input config).Value) (answer : (output config).Value)
    (reached : answer ∈ support (source config value)) : answer.val.1.1 = value.val.1 := by
  have erased : answer.val ∈ support (Subtype.val <$> source config value) := by
    rw [support_map]
    exact ⟨answer, reached, rfl⟩
  rw [source_value] at erased
  simp only [support_map, Set.mem_image] at erased
  obtain ⟨read, _, same⟩ := erased
  exact (congrArg (fun result => result.1.1) same).symm

theorem tape_lengths (value : (input config).Value) (answer : (output config).Value)
    (reached : answer ∈ support (source config value)) :
    answer.val.2.2.1.length ≤ value.val.2.2.1.length + 1 ∧
      answer.val.2.2.2.length ≤ value.val.2.2.2.length := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have erased : answer.val ∈ support (Subtype.val <$> source config value) := by
    rw [support_map]
    exact ⟨answer, reached, rfl⟩
  rw [source_value] at erased
  simp only [support_map, Set.mem_image] at erased
  obtain ⟨read, supported, same⟩ := erased
  rw [← same]
  exact Schnorr.RawTape.oracle_lengths _root_.Schnorr.LazyROM.sample (.inl value.val.1)
    ⟨value.val.2.2.1, value.val.2.2.2⟩ read supported

theorem reserved_after (reserve : Nat) (value : (input config).Value)
    (room : value.val.2.2.1.length + (reserve + 1) ≤ config.sampler.capacity)
    (answer : (output config).Value) (reached : answer ∈ support (source config value)) :
    answer.val.2.2.1.length + reserve ≤ config.sampler.capacity := by
  have growth := tape_lengths config value answer reached
  omega

section Original
variable {w : Nat} {M F G G₂ K : Type} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G] [DecidableEq M]
    [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K]
    (config : Signing.Enumerated.Configuration w M F G)

theorem source_original (value : (input config).Value) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    Subtype.val <$> source config value =
      (fun answer => ((value.val.1, answer.1.val), answer.2)) <$>
        (Schnorr.ListROM.Shared.interpret
          (Schnorr.ListROM.handler (G₂ := G₂) (K := K) (.inl (.inl value.val.1)))).run value.val.2 := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  rw [source_value]
  simp only [Schnorr.ListROM.Shared.interpret, Schnorr.ListROM.handler, Schnorr.ListROM.Shared.tapeRun,
    simulateQ_map, simulateQ_spec_query, StateT.run, Functor.map_map]
  dsimp only [Ty.Value, cryptoBase, OracleSpec.Range, FiatShamir.cmaOracleSpec,
    FiatShamir.fsRoSpec, OracleSpec.add_apply_inl, unifSpec, OracleSpec.ofFn]
  have mapped : (((fun r : Fin (value.val.1 + 1) => (r, value.val.2.1)) <$>
      Schnorr.RawTape.oracle (.inl value.val.1)).run ⟨value.val.2.2.1, value.val.2.2.2⟩) =
      (fun p => ((p.1, value.val.2.1), p.2)) <$>
        ((Schnorr.RawTape.oracle (.inl value.val.1)).run ⟨value.val.2.2.1, value.val.2.2.2⟩) :=
    StateT.run_map _ _ _
  simp only [StateT.run] at mapped
  rw [mapped]
  simp only [simulateQ_map, Functor.map_map]
  rfl

theorem observe_original (random : RandomTape w) (value : (input config).Value)
    (before : State w) (holds : (input config).representation.Holds value before) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    (fun result => (Interactive.observe (output config).representation result).map Subtype.val) <$>
        (code config).execute (Fresh.port config.handler.sampler.tape) .unit random before =
      (fun answer => some ((value.val.1, answer.1.val), answer.2)) <$>
        (Schnorr.ListROM.Shared.interpret
          (Schnorr.ListROM.handler (G₂ := G₂) (K := K) (.inl (.inl value.val.1)))).run value.val.2 := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  have observed := (refines config).observe random value before holds
  have erased := congrArg (Functor.map (Option.map Subtype.val)) observed
  simp only [Functor.map_map, Option.map_some] at erased
  have same := source_original (G₂ := G₂) (K := K) config value
  simpa only [Functor.map_map, Option.map_some] using erased.trans (by
    simpa only [Functor.map_map] using congrArg (Functor.map some) same)

end Original
end Signatures.Runtime.CaliperBackend.SchnorrROM.Random
