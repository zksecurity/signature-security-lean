import Proofs.Runtime.Caliper.SchnorrROMReplaySecondSelection

/-! The composed second branch has one execution accounting for the reset,
second adversary call, selector, comparison and retained first result. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplaySecond.Selected
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (caller : Pass.Caller config A) (ops : Handler.Operations config)
    (qH : Nat) (indexFits : qH + 1 < 2 ^ w) (budget : Handler.Budget config ops)
    (localBudget : SchnorrROM.Caller.LocalBudget config (caller.routines config))

def timeBudget (fuel : Nat) := ReplaySecond.timeBudget config caller ops budget localBudget fuel +
  ReplayMatch.timeBudget config ops qH indexFits budget
def codeBudget (fuel : Nat) := ReplaySecond.codeBudget config caller ops budget localBudget fuel +
  ReplayMatch.codeBudget config ops qH indexFits budget + 2
omit [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G] in
def nameBudget (slots : Nat) := max (Pass.nameBudget config slots) (max 3 ops.slots)

theorem time (fuel : Nat) : Interactive.TimeBound (Fresh.port config.handler.sampler.tape) .unit
    (input config fuel) (program config caller ops qH indexFits fuel) (timeBudget config caller ops qH indexFits budget localBudget fuel) := by
  have matching : Interactive.TimeBound (Fresh.port config.handler.sampler.tape) .unit
      (ReplaySecond.output config) (.compute (ReplayMatch.realizer config ops qH indexFits).code)
      (ReplayMatch.timeBudget config ops qH indexFits budget) :=
    Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
      (ReplayMatch.realizer config ops qH indexFits) _ (ReplayMatch.time config ops qH indexFits budget)
  exact Interactive.TimeBound.seq (ReplaySecond.refines config caller ops fuel)
    (ReplaySecond.time config caller ops budget localBudget fuel) matching

theorem words (fuel : Nat) : ((program config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤
    codeBudget config caller ops qH indexFits budget localBudget fuel := by
  have second := ReplaySecond.words config caller ops budget localBudget fuel
  have matching := ReplayMatch.words config ops qH indexFits budget
  change (WordIO.Code.seq ((ReplaySecond.program config caller ops fuel).lower _)
    (.compute (ReplayMatch.realizer config ops qH indexFits).code)).descriptionWords ≤ _
  rw [WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted caller.continuation.code slots) (initialNames : NamesAccounted caller.initialization.code slots)
    (fuel : Nat) : WordIO.NamesAccounted ((program config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape))
      (nameBudget config ops slots) :=
  ((ReplaySecond.names config caller ops slots handlerRoom localNames initialNames fuel).mono (Nat.le_max_left _ _)).seq
    ((WordIO.NamesAccounted.compute (ReplayMatch.names config ops qH indexFits)).mono (Nat.le_max_right _ _))

theorem resources (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted caller.continuation.code slots) (initialNames : NamesAccounted caller.initialization.code slots)
    (fuel : Nat) (tape : RandomTape w) (value : {value : Request config // ready config fuel value})
    (before : State w) (holds : (input config fuel).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((program config caller ops qH indexFits fuel).execute (Fresh.port config.handler.sampler.tape) .unit tape before)) :
    let code := (program config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)
    let stored := codeBudget config caller ops qH indexFits budget localBudget fuel
    let elapsed := timeBudget config caller ops qH indexFits budget localBudget fuel
    finished.time ≤ elapsed ∧ ∃ answer ∈ support (source config caller ops qH fuel value),
      (ReplayMatch.output config).Holds answer finished.state ∧ answer.2.2 = value.val ∧
      ∃ execution : WordIO.Exec .unit tape code before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers code.registerSlots) ∧ between.SupportBound (max buffers code.memBound) ∧ between.WellFormed ∧
          (code.staticWords registers buffers : Int) + between.liveMem (max buffers code.memBound) ≤
            stored + 4 * (nameBudget config ops slots + stored) + registers + 3 * buffers + before.liveMem buffers + elapsed := by
  have stored := words config caller ops qH indexFits budget localBudget fuel
  have named := names config caller ops qH indexFits slots handlerRoom localNames initialNames fuel
  obtain ⟨elapsed, answer, supported, represented, execution, memory⟩ :=
    (refines config caller ops qH indexFits fuel).resources (time config caller ops qH indexFits budget localBudget fuel) stored
      ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
      tape value before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, answer, supported, represented, retained_first config caller ops qH fuel value answer supported, execution, memory⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplaySecond.Selected
