import Signatures.Runtime.Caliper.SchnorrROMReplaySetup

/-! The conditional fork starts from runtime public points alone. Empty tapes
are constructed and charged before either pass executes. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Initialized
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} [Zero F] [SMul F G] [Sub G]
    [DecidableEq M] [DecidableEq G] [DecidableEq F]
    (config : Signing.Enumerated.Configuration w M F G) (caller : Pass.Caller config A)
    (ops : Handler.Operations config) (qH : Nat) (indexFits : qH + 1 < 2 ^ w)

def program (fuel : Nat) : Interactive.Code w :=
  .seq (.compute (Setup.realizer config).code) (ReplayFork.program config caller ops qH indexFits fuel)
def source (fuel : Nat) (tables : fuel + 1 ≤ config.capacityPred + 1)
    (tapes : 4 * fuel + 3 ≤ config.sampler.capacity) (value : (Pass.Initialization.points config).Value) :
    ProbComp (Result config) :=
  ReplayFork.source config caller ops qH indexFits fuel (Setup.start config fuel tables tapes value)

theorem refines (fuel : Nat) (tables : fuel + 1 ≤ config.capacityPred + 1)
    (tapes : 4 * fuel + 3 ≤ config.sampler.capacity) :
    Interactive.Refines (Fresh.port config.handler.sampler.tape) .unit (Setup.input config) (output config)
      (source config caller ops qH indexFits fuel tables tapes) (program config caller ops qH indexFits fuel) := by
  have joined := (Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit
    (Setup.prepared config fuel tables tapes)).seq (ReplayFork.refines config caller ops qH indexFits fuel)
  intro tape value before holds
  exact joined tape value before holds

theorem names (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted caller.continuation.code slots)
    (initialNames : NamesAccounted caller.initialization.code slots) (fuel : Nat) :
    WordIO.NamesAccounted ((program config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape))
      (ReplayFork.nameBudget config ops slots) :=
  (WordIO.NamesAccounted.compute (Setup.names config _)).seq
    (ReplayFork.names config caller ops qH indexFits slots handlerRoom localNames initialNames fuel)
theorem buffers (fuel : Nat) :
    ((program config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).memBound ≤
      Pass.bufferBudget config caller ops + 1 :=
  max_le ((Setup.buffers config).trans (by unfold Pass.bufferBudget; omega))
    (ReplayFork.buffers config caller ops qH indexFits fuel)
theorem descriptionFits (room : Pass.replayNameRoom config caller ops) (fuel : Nat) :
    ((program config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  .seq config.sampler.wordFits (.compute (Setup.realizer config).description_fits)
    (ReplayFork.descriptionFits config caller ops qH indexFits room fuel)

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Initialized
