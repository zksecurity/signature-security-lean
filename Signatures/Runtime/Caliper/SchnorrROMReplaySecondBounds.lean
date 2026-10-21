import Signatures.Runtime.Caliper.SchnorrROMReplaySecond

/-! Resource bounds for the executed restart and second pass, including the
first result retained throughout the call and all copies used to return it. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplaySecond
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (caller : Pass.Caller config A) (ops : Handler.Operations config)
    (budget : Handler.Budget config ops) (localBudget : SchnorrROM.Caller.LocalBudget config (caller.routines config))

def timeBudget (fuel : Nat) := initializationTime config +
  (Pass.timeBudget config caller ops budget localBudget fuel +
    8 * (Pass.Initialization.input config).encoding.words + 8 * (first config).encoding.words + 12 * (rawInput config).encoding.words)
def codeBudget (fuel : Nat) := initializationWords config +
  Pass.codeBudget config caller ops budget localBudget fuel +
    26 * (Pass.Initialization.input config).encoding.words + 26 * (first config).encoding.words + 39 * (rawInput config).encoding.words + 43

theorem time (fuel : Nat) : Interactive.TimeBound (Fresh.port config.handler.sampler.tape) .unit
    (input config fuel) (program config caller ops fuel) (timeBudget config caller ops budget localBudget fuel) := by
  have retained := (Interactive.TimeBoundOn.retain (pass_refines config caller ops fuel)
    (Pass.time config caller ops budget localBudget fuel) (by decide) (rawInput config)
    config.sampler.wordFits (secondInput config).fits).mono
      (Interactive.retain_time_unit_le _ _ _ _ _)
  have prepared := (Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit
    (initializeReplay config fuel)).on (fun _ => True)
  have preparing := (Interactive.TimeBound.compute (port := Fresh.port config.handler.sampler.tape) (cost := .unit)
    (initializeReplay config fuel) _ (initialization_time config fuel)).on (fun _ => True)
  have joined := Interactive.TimeBoundOn.seq prepared preparing retained (by
    intro value _ answer reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst answer
    exact next_ready config fuel value)
  intro tape value before holds
  exact joined tape value trivial before holds

theorem words (fuel : Nat) : ((program config caller ops fuel).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤
    codeBudget config caller ops budget localBudget fuel := by
  have retained := Interactive.retain_descriptionWords_le (Fresh.port config.handler.sampler.tape)
    (Pass.program config caller ops fuel) (Interactive.savedBuffer (Fresh.port config.handler.sampler.tape) (Pass.program config caller ops fuel))
    (Pass.Initialization.input config).encoding.words (first config).encoding.words (rawInput config).encoding.words
  have body := Pass.words config caller ops budget localBudget fuel
  have prepared := initialization_words config fuel
  change ((retainedPass config caller ops fuel).lower _).descriptionWords ≤ _ at retained
  change (WordIO.Code.seq (.compute (initializeReplay config fuel).code)
    ((retainedPass config caller ops fuel).lower _)).descriptionWords ≤ _
  rw [WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted caller.continuation.code slots) (initialNames : NamesAccounted caller.initialization.code slots)
    (fuel : Nat) : WordIO.NamesAccounted ((program config caller ops fuel).lower (Fresh.port config.handler.sampler.tape))
      (Pass.nameBudget config slots) :=
  (WordIO.NamesAccounted.compute (initialization_names config fuel _)).seq
    (Interactive.retain_names (Fresh.port config.handler.sampler.tape)
      (Pass.names config caller ops slots handlerRoom localNames initialNames fuel) _ _ _)

theorem resources (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted caller.continuation.code slots) (initialNames : NamesAccounted caller.initialization.code slots)
    (fuel : Nat) (tape : RandomTape w) (value : {value : Request config // ready config fuel value})
    (before : State w) (holds : (input config fuel).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((program config caller ops fuel).execute (Fresh.port config.handler.sampler.tape) .unit tape before)) :
    let code := (program config caller ops fuel).lower (Fresh.port config.handler.sampler.tape)
    let stored := codeBudget config caller ops budget localBudget fuel
    let elapsed := timeBudget config caller ops budget localBudget fuel
    finished.time ≤ elapsed ∧ ∃ answer ∈ support (source config caller ops fuel value),
      (output config).Holds answer finished.state ∧ answer.2 = value.val ∧
      ∃ execution : WordIO.Exec .unit tape code before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers code.registerSlots) ∧ between.SupportBound (max buffers code.memBound) ∧ between.WellFormed ∧
          (code.staticWords registers buffers : Int) + between.liveMem (max buffers code.memBound) ≤
            stored + 4 * (Pass.nameBudget config slots + stored) + registers + 3 * buffers + before.liveMem buffers + elapsed := by
  have stored := words config caller ops budget localBudget fuel
  have named := names config caller ops slots handlerRoom localNames initialNames fuel
  obtain ⟨elapsed, answer, supported, represented, execution, memory⟩ :=
    (refines config caller ops fuel).resources (time config caller ops budget localBudget fuel) stored
      ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
      tape value before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, answer, supported, represented, retained_first config caller ops fuel value answer supported, execution, memory⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplaySecond
