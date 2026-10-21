import Signatures.Runtime.Caliper.SchnorrROMReplayExtractClassify
import Signatures.Runtime.Caliper.SchnorrROMEnumeratedReplay

/-! The interactive fork extractor. After the executed classifier writes the
choice tag, stored-tag dispatch either runs the charged uniform scalar draw
`PrivateSampler.Enumerated.Direct` (one fresh oracle call on the replay port) or
keeps the computed quotient. No failure path returns a fixed scalar. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Extract
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

def keep := Realizer.identity (cost := .unit) (width_pos config.sampler.wordFits) config.handler.sampler.tape.scalar.representation
def draw : Interactive.Code w := PrivateSampler.Enumerated.Direct.code config.sampler
def select : Interactive.Code w :=
  Interactive.dispatch (draw config) (.compute (keep config).code)
    config.handler.sampler.tape.unit.representation.encoding.words config.handler.sampler.tape.scalar.representation.encoding.words

/-- The uniform fallback, or the represented quotient. -/
def finish : Choice config → ProbComp config.handler.sampler.tape.scalar.Value :=
  Sum.elim (fun _ => PrivateSampler.Enumerated.Direct.source config.sampler) (fun scalar => pure scalar)

theorem select_refines : Interactive.Refines (Fresh.port config.handler.sampler.tape) .unit (choice config)
    config.handler.sampler.tape.scalar.representation (finish config) (select config) :=
  Interactive.Refines.dispatch config.handler.sampler.tape.unit.representation config.handler.sampler.tape.scalar.representation
    config.handler.sampler.tape.scalar.representation (PrivateSampler.Enumerated.Direct.refines config.sampler)
    (Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (keep config))
    (width_pos config.sampler.wordFits) (choiceFits config)

section Code
variable [DecidableEq F] [DecidableEq G] [Sub F] [Div F] (arith : Arithmetic config)

def code : Interactive.Code w := .seq (.compute (classifier config arith).code) (select config)
/-- The extractor's source: classification is deterministic, the fallback is the
uniform scalar draw. It does not depend on the arithmetic implementation. -/
def source (value : Result config) : ProbComp config.handler.sampler.tape.scalar.Value :=
  finish config (classifyChoice config value)

theorem refines : Interactive.Refines (Fresh.port config.handler.sampler.tape) .unit (output config)
    config.handler.sampler.tape.scalar.representation (source config) (code config arith) := by
  have joined := (Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit
    (classifier config arith)).seq (select_refines config)
  intro tape value before holds
  have step := joined tape value before holds
  simp only [pure_bind] at step
  exact step

theorem observe (tape : RandomTape w) (value : Result config) (before : State w)
    (holds : (output config).Holds value before) :
    Interactive.observe config.handler.sampler.tape.scalar.representation <$>
        (code config arith).execute (Fresh.port config.handler.sampler.tape) .unit tape before =
      some <$> source config value :=
  (refines config arith).observe tape value before holds

end Code
end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Extract
