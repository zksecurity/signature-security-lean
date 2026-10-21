import Signatures.Runtime.Caliper.SchnorrROMReplayInitialized

/-! The initialized fork's resource account includes the executed construction
of both empty tapes, the original public inputs and the complete controller. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Initialized
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} [Zero F] [SMul F G] [Sub G]
    [DecidableEq M] [DecidableEq G] [DecidableEq F]
    (config : Signing.Enumerated.Configuration w M F G) (caller : Pass.Caller config A)
    (ops : Handler.Operations config) (qH : Nat) (indexFits : qH + 1 < 2 ^ w)
    (budget : Handler.Budget config ops)
    (localBudget : SchnorrROM.Caller.LocalBudget config (caller.routines config))

def timeBudget (fuel : Nat) := 8 * (Pass.Initialization.input config).encoding.words +
  ReplayFork.timeBudget config caller ops qH indexFits budget localBudget fuel
def codeBudget (fuel : Nat) := 26 * (Pass.Initialization.input config).encoding.words + 16 +
  ReplayFork.codeBudget config caller ops qH indexFits budget localBudget fuel

theorem time (fuel : Nat) (tables : fuel + 1 ≤ config.capacityPred + 1)
    (tapes : 4 * fuel + 3 ≤ config.sampler.capacity) :
    Interactive.TimeBound (Fresh.port config.handler.sampler.tape) .unit (Setup.input config)
      (program config caller ops qH indexFits fuel) (timeBudget config caller ops qH indexFits budget localBudget fuel) :=
  Interactive.TimeBound.seq
    (Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (Setup.prepared config fuel tables tapes))
    (Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
      (Setup.prepared config fuel tables tapes) _ (Setup.time config))
    (ReplayFork.time config caller ops qH indexFits budget localBudget fuel)
theorem words (fuel : Nat) :
    ((program config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤
      codeBudget config caller ops qH indexFits budget localBudget fuel := by
  have setup := Setup.words config
  have fork := ReplayFork.words config caller ops qH indexFits budget localBudget fuel
  change (WordIO.Code.seq (.compute (Setup.realizer config).code)
    ((ReplayFork.program config caller ops qH indexFits fuel).lower _)).descriptionWords ≤ _
  rw [WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem resources (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted caller.continuation.code slots)
    (initialNames : NamesAccounted caller.initialization.code slots)
    (fuel : Nat) (tables : fuel + 1 ≤ config.capacityPred + 1)
    (tapes : 4 * fuel + 3 ≤ config.sampler.capacity)
    (tape : RandomTape w) (value : (Pass.Initialization.points config).Value)
    (before : State w) (holds : (Setup.input config).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers)
    (initialBuffers : before.SupportBound buffers) (finished : WordIO.Result w)
    (reached : some finished ∈ support ((program config caller ops qH indexFits fuel).execute
      (Fresh.port config.handler.sampler.tape) .unit tape before)) :
    let code := (program config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)
    let stored := codeBudget config caller ops qH indexFits budget localBudget fuel
    let elapsed := timeBudget config caller ops qH indexFits budget localBudget fuel
    finished.time ≤ elapsed ∧ ∃ answer ∈ support (source config caller ops qH indexFits fuel tables tapes value),
      (output config).Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape code before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers code.registerSlots) ∧ between.SupportBound (max buffers code.memBound) ∧ between.WellFormed ∧
          (code.staticWords registers buffers : Int) + between.liveMem (max buffers code.memBound) ≤
            stored + 4 * (ReplayFork.nameBudget config ops slots + stored) + registers + 3 * buffers + before.liveMem buffers + elapsed := by
  have stored := words config caller ops qH indexFits budget localBudget fuel
  have named := names config caller ops qH indexFits slots handlerRoom localNames initialNames fuel
  exact (refines config caller ops qH indexFits fuel tables tapes).resources
    (time config caller ops qH indexFits budget localBudget fuel tables tapes) stored
    ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
    tape value before holds registers buffers initialRegisters initialBuffers finished reached

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Initialized
