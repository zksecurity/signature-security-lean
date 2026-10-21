import Signatures.Runtime.Caliper.SchnorrROMReplayForkBounds

/-! Names, description validity and all visited memory for the complete fork.
The account covers both stored branches and the single executed branch. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G] [DecidableEq F]
    (config : Signing.Enumerated.Configuration w M F G) (caller : Pass.Caller config A) (ops : Handler.Operations config)
    (qH : Nat) (indexFits : qH + 1 < 2 ^ w)

def nameBudget (slots : Nat) := ReplayFirst.nameBudget config ops slots

omit [DecidableEq F] in
theorem second_names (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted caller.continuation.code slots) (initialNames : NamesAccounted caller.initialization.code slots)
    (fuel : Nat) : WordIO.NamesAccounted ((secondCode config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)) (nameBudget config ops slots) :=
  (ReplaySecond.Selected.names config caller ops qH indexFits slots handlerRoom localNames initialNames fuel).seq
    (WordIO.NamesAccounted.compute (finish_names config _))
omit [DecidableEq F] in
theorem guard_names (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted caller.continuation.code slots) (initialNames : NamesAccounted caller.initialization.code slots)
    (fuel : Nat) : WordIO.NamesAccounted ((guardCode config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)) (nameBudget config ops slots) :=
  Interactive.dispatch_names («left» := secondCode config caller ops qH indexFits fuel)
    («right» := .compute (reject config (ReplaySecond.rawInput config)).code) (Fresh.port config.handler.sampler.tape)
    (second_names config caller ops qH indexFits slots handlerRoom localNames initialNames fuel)
    (WordIO.NamesAccounted.compute (reject_names config (ReplaySecond.rawInput config) (nameBudget config ops slots))) _ _

theorem after_names (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted caller.continuation.code slots) (initialNames : NamesAccounted caller.initialization.code slots)
    (fuel : Nat) : WordIO.NamesAccounted ((afterCode config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)) (nameBudget config ops slots) :=
  ((ReplayChallenge.Checked.names config).mono (by unfold nameBudget ReplayFirst.nameBudget; omega)).seq
    (guard_names config caller ops qH indexFits slots handlerRoom localNames initialNames fuel)
theorem branch_names (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted caller.continuation.code slots) (initialNames : NamesAccounted caller.initialization.code slots)
    (fuel : Nat) : WordIO.NamesAccounted ((branchCode config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)) (nameBudget config ops slots) :=
  Interactive.dispatch_names («left» := .compute (reject config (ReplayChallenge.input config)).code)
    («right» := afterCode config caller ops qH indexFits fuel) (Fresh.port config.handler.sampler.tape)
    (WordIO.NamesAccounted.compute (reject_names config (ReplayChallenge.input config) (nameBudget config ops slots)))
    (after_names config caller ops qH indexFits slots handlerRoom localNames initialNames fuel) _ _
theorem names (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted caller.continuation.code slots) (initialNames : NamesAccounted caller.initialization.code slots)
    (fuel : Nat) : WordIO.NamesAccounted ((program config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)) (nameBudget config ops slots) :=
  (ReplayFirst.names config caller ops qH indexFits slots handlerRoom localNames initialNames fuel).seq
    (branch_names config caller ops qH indexFits slots handlerRoom localNames initialNames fuel)

omit [DecidableEq F] in
theorem second_buffers (fuel : Nat) : ((secondCode config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).memBound ≤
    Pass.bufferBudget config caller ops + 1 :=
  max_le (ReplaySecond.Selected.buffers config caller ops qH indexFits fuel)
    ((finish_buffers config).trans (by unfold Pass.bufferBudget; omega))
omit [DecidableEq F] in
theorem guard_buffers (fuel : Nat) : ((guardCode config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).memBound ≤
    Pass.bufferBudget config caller ops + 1 := by
  have continued := second_buffers config caller ops qH indexFits fuel
  have rejected := reject_buffers config (ReplaySecond.rawInput config)
  have branch := Interactive.dispatch_buffers (Fresh.port config.handler.sampler.tape)
    (secondCode config caller ops qH indexFits fuel) (.compute (reject config (ReplaySecond.rawInput config)).code)
      (ReplaySecond.rawInput config).encoding.words (ReplaySecond.rawInput config).encoding.words
  change ((guardCode config caller ops qH indexFits fuel).lower _).memBound ≤ max 2
    (max ((secondCode config caller ops qH indexFits fuel).lower _).memBound (reject config (ReplaySecond.rawInput config)).code.memBound) at branch
  unfold Pass.bufferBudget at *
  omega

theorem after_buffers (fuel : Nat) : ((afterCode config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).memBound ≤
    Pass.bufferBudget config caller ops + 1 :=
  max_le ((ReplayChallenge.Checked.buffers config).trans (by unfold Pass.bufferBudget; omega))
    (guard_buffers config caller ops qH indexFits fuel)
theorem branch_buffers (fuel : Nat) : ((branchCode config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).memBound ≤
    Pass.bufferBudget config caller ops + 1 := by
  have continued := after_buffers config caller ops qH indexFits fuel
  have rejected := reject_buffers config (ReplayChallenge.input config)
  have branch := Interactive.dispatch_buffers (Fresh.port config.handler.sampler.tape)
    (.compute (reject config (ReplayChallenge.input config)).code) (afterCode config caller ops qH indexFits fuel)
      (ReplayChallenge.input config).encoding.words (ReplayChallenge.input config).encoding.words
  change ((branchCode config caller ops qH indexFits fuel).lower _).memBound ≤ max 2
    (max (reject config (ReplayChallenge.input config)).code.memBound ((afterCode config caller ops qH indexFits fuel).lower _).memBound) at branch
  unfold Pass.bufferBudget at *
  omega

theorem buffers (fuel : Nat) : ((program config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).memBound ≤
    Pass.bufferBudget config caller ops + 1 :=
  max_le (ReplayFirst.buffers config caller ops qH indexFits fuel) (branch_buffers config caller ops qH indexFits fuel)

omit [DecidableEq F] in
theorem second_descriptionFits (room : Pass.replayNameRoom config caller ops) (fuel : Nat) :
    ((secondCode config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  .seq config.sampler.wordFits (ReplaySecond.Selected.descriptionFits config caller ops qH indexFits room fuel) (.compute (finish config).description_fits)
omit [DecidableEq F] in
theorem guard_descriptionFits (room : Pass.replayNameRoom config caller ops) (fuel : Nat) :
    ((guardCode config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  Interactive.dispatch_descriptionFits (Fresh.port config.handler.sampler.tape) _ _ _ _ config.sampler.wordFits
    (second_descriptionFits config caller ops qH indexFits room fuel) (.compute (reject config (ReplaySecond.rawInput config)).description_fits)
    (ReplaySecond.rawInput config).fits (ReplaySecond.rawInput config).fits

theorem after_descriptionFits (room : Pass.replayNameRoom config caller ops) (fuel : Nat) :
    ((afterCode config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  .seq config.sampler.wordFits (ReplayChallenge.Checked.descriptionFits config) (guard_descriptionFits config caller ops qH indexFits room fuel)
theorem branch_descriptionFits (room : Pass.replayNameRoom config caller ops) (fuel : Nat) :
    ((branchCode config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  Interactive.dispatch_descriptionFits (Fresh.port config.handler.sampler.tape) _ _ _ _ config.sampler.wordFits
    (.compute (reject config (ReplayChallenge.input config)).description_fits) (after_descriptionFits config caller ops qH indexFits room fuel)
    (ReplayChallenge.input config).fits (ReplayChallenge.input config).fits

theorem descriptionFits (room : Pass.replayNameRoom config caller ops) (fuel : Nat) :
    ((program config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  .seq config.sampler.wordFits (ReplayFirst.descriptionFits config caller ops qH indexFits fuel) (branch_descriptionFits config caller ops qH indexFits room fuel)

variable (budget : Handler.Budget config ops) (localBudget : SchnorrROM.Caller.LocalBudget config (caller.routines config))

theorem resources (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted caller.continuation.code slots) (initialNames : NamesAccounted caller.initialization.code slots)
    (fuel : Nat) (tape : RandomTape w) (value : {value : Pass.Initialization.Input config // Pass.Replay.ready config fuel value})
    (before : State w) (holds : (ReplayFirst.input config fuel).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((program config caller ops qH indexFits fuel).execute (Fresh.port config.handler.sampler.tape) .unit tape before)) :
    let code := (program config caller ops qH indexFits fuel).lower (Fresh.port config.handler.sampler.tape)
    let stored := codeBudget config caller ops qH indexFits budget localBudget fuel
    let elapsed := timeBudget config caller ops qH indexFits budget localBudget fuel
    finished.time ≤ elapsed ∧ ∃ answer ∈ support (source config caller ops qH indexFits fuel value),
      (output config).Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape code before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers code.registerSlots) ∧ between.SupportBound (max buffers code.memBound) ∧ between.WellFormed ∧
          (code.staticWords registers buffers : Int) + between.liveMem (max buffers code.memBound) ≤
            stored + 4 * (nameBudget config ops slots + stored) + registers + 3 * buffers + before.liveMem buffers + elapsed := by
  have stored := words config caller ops qH indexFits budget localBudget fuel
  have named := names config caller ops qH indexFits slots handlerRoom localNames initialNames fuel
  exact (refines config caller ops qH indexFits fuel).resources (time config caller ops qH indexFits budget localBudget fuel) stored
    ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
    tape value before holds registers buffers initialRegisters initialBuffers finished reached

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
