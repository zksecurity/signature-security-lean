import Proofs.Runtime.Caliper.SchnorrROMForgeryHashRoute

/-! Execute final hashing while retaining the complete forgery in a fresh
buffer. The source extension outside admission has no execution claim. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ForgeryHash
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} [Zero F] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G)

def retained := Interactive.retain (FinalHash.code config)
  (Interactive.savedBuffer (Fresh.port config.handler.sampler.tape) (FinalHash.code config))
  (FinalHash.input config).representation.encoding.words (FinalHash.output config).representation.encoding.words
  (forgery config).representation.encoding.words
def code : Interactive.Code w := .seq (.compute (rawPrepare config).code)
  (.seq (retained config) (.compute (finish config).code))
def source (value : Input config) : ProbComp (Output config) :=
  if valid : ready config value then
    (fun hashed => finishValue config (hashed, value.1)) <$> FinalHash.source config (request config value valid)
  else pure ((value.1, ⟨0, trivial⟩), value.2)

theorem retained_refines : Interactive.RefinesOn (fun value => FinalHash.ready config value.1)
    (Fresh.port config.handler.sampler.tape) .unit (prepared config) (finished config)
    (fun value => (fun hashed => (hashed, value.2)) <$> FinalHash.source config value.1) (retained config) :=
  (FinalHash.refines config).retain (by decide) (forgery config).representation
    config.sampler.wordFits (prepared config).fits (finished config).fits

theorem refines : Interactive.RefinesOn (ready config) (Fresh.port config.handler.sampler.tape) .unit
    (input config) (output config) (source config) (code config) := by
  have suffix := (retained_refines config).seq
    ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (finish config)).on (fun _ => True))
    (fun _ _ _ _ => trivial)
  have combined := ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (prepare config)).on (fun _ => True)).seq
    suffix (by
      intro value _ answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact request_ready config value.val value.property)
  intro tape value valid before holds
  have checked := combined tape ⟨value, valid⟩ trivial before holds
  simpa only [source, dite_eq_left valid, pure_bind, bind_pure_comp, Functor.map_map, code,
    prepare, prepareValue, Realizer.viewInput, Realizer.viewOutput] using checked

theorem preserves_forgery (value : Input config) (answer : Output config)
    (reached : answer ∈ support (source config value)) : answer.1.1 = value.1 := by
  unfold source at reached
  split at reached
  · simp only [support_map, Set.mem_image] at reached
    obtain ⟨hashed, _, rfl⟩ := reached
    rfl
  · obtain rfl := (mem_support_pure_iff _ _).mp reached
    rfl

theorem preserves_config (value : Input config) (answer : Output config)
    (reached : answer ∈ support (source config value)) : answer.2.val.1.1 = value.2.val.1.1 := by
  unfold source at reached
  split at reached
  · simp only [support_map, Set.mem_image] at reached
    obtain ⟨hashed, supported, rfl⟩ := reached
    exact FinalHash.preserves_config config _ hashed supported
  · obtain rfl := (mem_support_pure_iff _ _).mp reached
    rfl

theorem preserves_managed (value : Input config) (answer : Output config)
    (reached : answer ∈ support (source config value)) : answer.2.val.1.2.1 = value.2.val.1.2.1 := by
  unfold source at reached
  split at reached
  · simp only [support_map, Set.mem_image] at reached
    obtain ⟨hashed, supported, rfl⟩ := reached
    exact FinalHash.preserves_managed config _ hashed supported
  · obtain rfl := (mem_support_pure_iff _ _).mp reached
    rfl

end Signatures.Runtime.CaliperBackend.SchnorrROM.ForgeryHash
