import Proofs.Runtime.Caliper.SchnorrROMFinalHashRoute

/-! Execute final hashing against LIVE while preserving the public configuration
and the separate managed table. All retained state is copied by Caliper code. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.FinalHash
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} [Zero F] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G)

def retained := Interactive.retain (HashCache.code config)
  (Interactive.savedBuffer (Fresh.port config.handler.sampler.tape) (HashCache.code config))
  (HashCache.model config).input.encoding.words (HashCache.model config).output.encoding.words
  config.handler.core.store.representation.encoding.words
def code : Interactive.Code w := .seq (.compute (prepare config).code)
  (.seq (retained config) (.compute (finish config).code))
def ready (value : (input config).Value) := HashCache.ready config (request config value, tapes config value)
def source (value : (input config).Value) : ProbComp (output config).Value :=
  (fun read => finishValue config (read, context config value)) <$> HashCache.source config (request config value, tapes config value)

theorem retained_refines : Interactive.RefinesOn (fun value => HashCache.ready config value.1)
    (Fresh.port config.handler.sampler.tape) .unit (prepared config) (finished config)
    (fun value => (fun read => (read, value.2)) <$> HashCache.source config value.1) (retained config) :=
  (HashCache.refines config).retain (by decide) config.handler.core.store.representation
    config.sampler.wordFits (prepared config).fits (finished config).fits

theorem refines : Interactive.RefinesOn (ready config) (Fresh.port config.handler.sampler.tape) .unit
    (input config).representation (output config).representation (source config) (code config) := by
  have suffix := (retained_refines config).seq
    ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (finish config)).on (fun _ => True))
    (by intros; trivial)
  have compiled := ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (prepare config)).on (ready config)).seq
    suffix (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact valid)
  convert compiled using 1
  · funext value
    simp only [source, pure_bind, bind_pure_comp, Functor.map_map]
    rfl
  · rfl

theorem preserves_config (value : (input config).Value) (answer : (output config).Value)
    (reached : answer ∈ support (source config value)) : answer.val.2.1.1 = value.val.2.1.1 := by
  simp only [source, support_map, Set.mem_image] at reached
  obtain ⟨read, _, rfl⟩ := reached
  rfl

theorem preserves_managed (value : (input config).Value) (answer : (output config).Value)
    (reached : answer ∈ support (source config value)) : answer.val.2.1.2.1 = value.val.2.1.2.1 := by
  simp only [source, support_map, Set.mem_image] at reached
  obtain ⟨read, _, rfl⟩ := reached
  rfl

theorem live_length (value : (input config).Value) (answer : (output config).Value)
    (reached : answer ∈ support (source config value)) :
    answer.val.2.1.2.2.length ≤ value.val.2.1.2.2.length + 1 := by
  simp only [source, support_map, Set.mem_image] at reached
  obtain ⟨read, reached, rfl⟩ := reached
  have erased : (read.1.val, read.2.val) ∈ support
      ((fun result => (result.1.val, result.2.val)) <$> HashCache.source config (request config value, tapes config value)) := by
    rw [support_map]
    exact ⟨read, reached, rfl⟩
  rw [HashCache.source_value] at erased
  dsimp only [request, tapes] at erased
  change read.1.val.2.length ≤ value.val.2.1.2.2.length + 1
  cases found : cacheMap value.val.2.1.2.2 value.val.1 with
  | none =>
    simp only [found, support_map, Set.mem_image] at erased
    obtain ⟨fresh, _, same⟩ := erased
    have length := congrArg (fun result : (F × Signing.Table M F G) × Schnorr.ListROM.Shared.Tape F => result.1.2.length) same
    simp only [List.length_cons] at length
    omega
  | some challenge =>
    simp only [found, support_pure, Set.mem_singleton_iff] at erased
    have length := congrArg (fun result : (F × Signing.Table M F G) × Schnorr.ListROM.Shared.Tape F => result.1.2.length) erased
    change read.1.val.2.length = value.val.2.1.2.2.length at length
    omega

theorem reserved_after (reserve : Nat) (value : (input config).Value)
    (room : value.val.2.1.2.2.length + (reserve + 1) ≤ config.capacityPred + 1)
    (answer : (output config).Value) (reached : answer ∈ support (source config value)) :
    answer.val.2.1.2.2.length + reserve ≤ config.capacityPred + 1 := by
  have growth := live_length config value answer reached
  omega

end Signatures.Runtime.CaliperBackend.SchnorrROM.FinalHash
