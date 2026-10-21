import Signatures.Runtime.Caliper.SchnorrROMPassCaller

/-! The caller and terminal share one execution, with additive time/code bounds
and all visited memory charged. Final hashing uses the caller's proved reserve. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Pass
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (caller : Caller config A) (ops : Handler.Operations config)
    (budget : Handler.Budget config ops) (localBudget : SchnorrROM.Caller.LocalBudget config (caller.routines config))

def finishTime (fuel : Nat) := SchnorrROM.Caller.timeBudget config (caller.routines config) ops budget localBudget fuel +
  Terminal.timeBudget config (caller.pending config)
def finishWords (fuel : Nat) := SchnorrROM.Caller.codeBudget config (caller.routines config) ops budget localBudget fuel +
  Terminal.codeBudget config (caller.pending config) + 1

theorem finish_time (fuel : Nat) : Interactive.TimeBoundOn (SchnorrROM.Caller.admitted config fuel)
    (Fresh.port config.handler.sampler.tape) .unit (callerInput config caller)
    (finishCode config caller ops fuel) (finishTime config caller ops budget localBudget fuel) :=
  Interactive.TimeBoundOn.seq (SchnorrROM.Caller.refines config (caller.routines config) ops fuel)
    (SchnorrROM.Caller.time config (caller.routines config) ops budget localBudget fuel)
    (Terminal.time_bound config (caller.pending config) (caller.terminalRoom config)) (called_ready config caller ops fuel)

theorem finish_words (fuel : Nat) : ((finishCode config caller ops fuel).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤
    finishWords config caller ops budget localBudget fuel := by
  have one := SchnorrROM.Caller.words config (caller.routines config) ops budget localBudget fuel
  have two := Terminal.code_bound config (caller.pending config) (caller.terminalRoom config)
  change (WordIO.Code.seq ((SchnorrROM.Caller.program config (caller.routines config) ops fuel).lower (Fresh.port config.handler.sampler.tape))
    ((Terminal.code config (caller.pending config) (caller.terminalRoom config)).lower (Fresh.port config.handler.sampler.tape))).descriptionWords ≤ _
  rw [WordIO.Code.descriptionWords_seq]
  unfold finishWords
  omega

def nameBudget (slots : Nat) := max slots (Terminal.nameBudget config)

theorem finish_names (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted caller.continuation.code slots) (initialNames : NamesAccounted caller.initialization.code slots)
    (fuel : Nat) : WordIO.NamesAccounted ((finishCode config caller ops fuel).lower (Fresh.port config.handler.sampler.tape))
      (nameBudget config slots) :=
  ((SchnorrROM.Caller.names config (caller.routines config) ops slots handlerRoom localNames initialNames fuel).mono
    (Nat.le_max_left _ _)).seq
    ((Terminal.names config (caller.pending config) (caller.terminalRoom config)).mono (Nat.le_max_right _ _))

theorem finish_descriptionFits (fuel : Nat) : ((finishCode config caller ops fuel).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  .seq config.sampler.wordFits (SchnorrROM.Caller.descriptionFits config (caller.routines config) ops fuel)
    (Terminal.descriptionFits config (caller.pending config) (caller.terminalRoom config))

theorem finish_resources (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted caller.continuation.code slots) (initialNames : NamesAccounted caller.initialization.code slots)
    (fuel : Nat) (tape : RandomTape w) (value : config.point.Value × config.handler.store.Value)
    (room : SchnorrROM.Caller.admitted config fuel value) (before : State w) (holds : (callerInput config caller).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((finishCode config caller ops fuel).execute (Fresh.port config.handler.sampler.tape) .unit tape before)) :
    let code := (finishCode config caller ops fuel).lower (Fresh.port config.handler.sampler.tape)
    let stored := finishWords config caller ops budget localBudget fuel
    let elapsed := finishTime config caller ops budget localBudget fuel
    finished.time ≤ elapsed ∧ ∃ answer ∈ support (finishSource config caller ops fuel value),
      (output config caller).Holds answer finished.state ∧ answer.2.val.1.1 = value.2.val.1.1 ∧
      ∃ execution : WordIO.Exec .unit tape code before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers code.registerSlots) ∧ between.SupportBound (max buffers code.memBound) ∧ between.WellFormed ∧
          (code.staticWords registers buffers : Int) + between.liveMem (max buffers code.memBound) ≤
            stored + 4 * (nameBudget config slots + stored) + registers + 3 * buffers + before.liveMem buffers + elapsed := by
  have stored := finish_words config caller ops budget localBudget fuel
  have named := finish_names config caller ops slots handlerRoom localNames initialNames fuel
  obtain ⟨elapsed, answer, supported, represented, execution, memory⟩ :=
    (finish_refines config caller ops fuel).resources (finish_time config caller ops budget localBudget fuel) stored
      ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
      tape value room before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, answer, supported, represented, finish_preserves_config config caller ops fuel value room answer supported, execution, memory⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.Pass
