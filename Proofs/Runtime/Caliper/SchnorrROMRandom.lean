import Proofs.Runtime.Caliper.SchnorrROMRandomRoute

/-! The complete adversary-randomness handler preserves both hash tables and
the public configuration while executing the dynamic-range raw replay query. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Random
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} [Zero F] (config : Signing.Enumerated.Configuration w M F G)

def bodySource := Caller.privateDenote config.handler.sampler.tape trivial (PrivateSampler.Enumerated.Direct.source config.sampler)
theorem body_refines : Interactive.Refines (Fresh.port config.handler.sampler.tape) .unit
    (Caller.privateInput config.handler.sampler.tape).representation (Reply.privateOutput config.handler.sampler.tape).representation
    (bodySource config) (EnumeratedReplay.privateCode config.sampler) :=
  Caller.private_refines config.handler.sampler.tape trivial (PrivateSampler.Enumerated.Direct.refines config.sampler)

def retained := Interactive.retain (EnumeratedReplay.privateCode config.sampler)
  (Interactive.savedBuffer (Fresh.port config.handler.sampler.tape) (EnumeratedReplay.privateCode config.sampler))
  (Caller.privateInput config.handler.sampler.tape).representation.encoding.words
  (Reply.privateOutput config.handler.sampler.tape).representation.encoding.words config.handler.caches.representation.encoding.words
def code : Interactive.Code w := .seq (.compute (prepare config).code)
  (.seq (retained config) (.compute (finish config).code))
def source (value : (input config).Value) : ProbComp (output config).Value :=
  (fun read => finishValue config (read, context config value)) <$> bodySource config (request config value)

theorem retained_refines : Interactive.Refines (Fresh.port config.handler.sampler.tape) .unit (prepared config) (finished config)
    (fun value => (fun read => (read, value.2)) <$> bodySource config value.1) (retained config) :=
  (body_refines config).retain (by decide) config.handler.caches.representation
    config.sampler.wordFits (prepared config).fits (finished config).fits

theorem refines : Interactive.Refines (Fresh.port config.handler.sampler.tape) .unit
    (input config).representation (output config).representation (source config) (code config) := by
  have compiled := (Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (prepare config)).seq
    ((retained_refines config).seq (Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (finish config)))
  convert compiled using 1
  · funext value
    simp only [source, pure_bind, bind_pure_comp, Functor.map_map]
    rfl
  · rfl

theorem preserves_caches (value : (input config).Value) (answer : (output config).Value)
    (reached : answer ∈ support (source config value)) : answer.val.2.1 = value.val.2.1 := by
  simp only [source, support_map, Set.mem_image] at reached
  obtain ⟨read, _, rfl⟩ := reached
  rfl

end Signatures.Runtime.CaliperBackend.SchnorrROM.Random
