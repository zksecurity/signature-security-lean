import Proofs.Runtime.Caliper.SchnorrROMHashMissRoute

/-! The fresh-entry routine for the managed cache. It reads LIVE through the
complete final-hash handler and returns the key with its updated shared store.
Its reservation applies only when the enclosing managed read misses. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.HashMiss
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} [Zero F] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G)

def ready (value : (input config).Value) : Prop :=
  FinalHash.admissible config value.val ∧ value.val.2.2.1.length < config.sampler.capacity
def admitted (value : (input config).Value) (valid : FinalHash.admissible config value.val) : (FinalHash.input config).Value :=
  ⟨value.val, value.property, valid⟩
def innerSource (value : (input config).Value) : ProbComp (FinalHash.output config).Value :=
  if valid : FinalHash.admissible config value.val then FinalHash.source config (admitted config value valid)
  else pure ⟨(0, value.val.2), trivial, value.property.2⟩

theorem inner_refines : Interactive.RefinesOn (ready config) (Fresh.port config.handler.sampler.tape) .unit
    (input config).representation (FinalHash.output config).representation (innerSource config) (FinalHash.code config) := by
  intro random value valid before holds
  rw [innerSource, dite_eq_left valid.1]
  exact FinalHash.refines config random (admitted config value valid.1) valid.2 before holds

def retained := Interactive.retain (FinalHash.code config)
  (Interactive.savedBuffer (Fresh.port config.handler.sampler.tape) (FinalHash.code config))
  (input config).representation.encoding.words (FinalHash.output config).representation.encoding.words
  config.handler.core.key.representation.encoding.words
def code : Interactive.Code w := .seq (.compute (prepare config).code)
  (.seq (retained config) (.compute (finish config).code))
def source (value : (input config).Value) : ProbComp (config.handler.sampler.tape.scalar.Value × (input config).Value) :=
  (fun answer => finishValue config (answer, ⟨value.val.1, value.property.1⟩)) <$> innerSource config value

theorem retained_refines : Interactive.RefinesOn (fun value => ready config value.1)
    (Fresh.port config.handler.sampler.tape) .unit (prepared config) (finished config)
    (fun value => (fun answer => (answer, value.2)) <$> innerSource config value.1) (retained config) :=
  (inner_refines config).retain (by decide) config.handler.core.key.representation
    config.sampler.wordFits (prepared config).fits (finished config).fits

theorem refines : Interactive.RefinesOn (ready config) (Fresh.port config.handler.sampler.tape) .unit
    (input config).representation (output config) (source config) (code config) := by
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

theorem source_finalHash (value : (input config).Value) (valid : ready config value) :
    (fun answer => (answer.1.val, answer.2.val)) <$> source config value =
      (fun answer => (answer.val.1, value.val.1, answer.val.2)) <$>
        FinalHash.source config (admitted config value valid.1) := by
  simp only [source, innerSource, dite_eq_left valid.1, Functor.map_map]
  rfl

theorem preserves_key (value : (input config).Value)
    (answer : config.handler.sampler.tape.scalar.Value × (input config).Value)
    (reached : answer ∈ support (source config value)) : answer.2.val.1 = value.val.1 := by
  simp only [source, support_map, Set.mem_image] at reached
  obtain ⟨read, _, rfl⟩ := reached
  rfl

end Signatures.Runtime.CaliperBackend.SchnorrROM.HashMiss
