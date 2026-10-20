import Signatures.Runtime.Caliper.SchnorrROMCallerExecution

/-! Time, complete stored code and memory of the generated adaptive caller.
Each unrolled body and every retention copy is charged. Primitive and local
caller costs are explicit bounds on their actual Caliper implementations. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Caller
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A B U : Type} (config : Signing.Enumerated.Configuration w M F G)
    (routines : Routines config A B U)

structure LocalBudget where
  localTime : Nat
  initialTime : Nat
  localWords : Nat
  initialWords : Nat
  local_time : ∀ value, routines.continuation.time value ≤ localTime
  initial_time : ∀ value, routines.initialization.time value ≤ initialTime
  local_words : descriptionWords routines.continuation.code ≤ localWords
  initial_words : descriptionWords routines.initialization.code ≤ initialWords

variable [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (ops : Handler.Operations config) (budget : Handler.Budget config ops) (localBudget : LocalBudget config routines)

def timeBudget (fuel : Nat) := CallerControl.timeBudget routines.input.encoding.words
  (CallerStep.width (routines.layout config)) (CallerHandler.timeBudget config ops budget)
  localBudget.localTime localBudget.initialTime fuel
def codeBudget (fuel : Nat) := localBudget.initialWords + 26 * routines.input.encoding.words +
  507 * CallerStep.width (routines.layout config) + 286 +
  fuel * (CallerHandler.codeBudget config ops budget + localBudget.localWords + 742 * CallerStep.width (routines.layout config) + 389)

theorem time (fuel : Nat) : Interactive.TimeBoundOn (admitted config fuel) (Fresh.port config.handler.sampler.tape) .unit
    (routines.inputLayout config) (program config routines ops fuel) (timeBudget config routines ops budget localBudget fuel) :=
  CallerControl.program_time (routines.layout config) (Fresh.port config.handler.sampler.tape)
    routines.advance routines.continuation routines.localNameFits (Invariant config) (CallerPackets.ready config)
    (CallerHandler.refines config ops) (available config) (CallerHandler.time_bound config ops budget)
    localBudget.local_time (preserves config routines ops)
    routines.input routines.initial routines.initialization routines.initialNameFits routines.inputFits fuel
    (admitted config fuel) (initial_invariant config routines fuel) localBudget.initialTime localBudget.initial_time

theorem words (fuel : Nat) : ((program config routines ops fuel).lower (Fresh.port config.handler.sampler.tape)).descriptionWords ≤
    codeBudget config routines ops budget localBudget fuel := by
  have generated := CallerControl.program_words (routines.layout config) (Fresh.port config.handler.sampler.tape)
    routines.advance routines.continuation routines.localNameFits (CallerHandler.code config ops)
    routines.input routines.initial routines.initialization routines.initialNameFits routines.inputFits fuel
  have handler := CallerHandler.code_bound config ops budget
  apply generated.trans
  unfold CallerControl.programWords CallerControl.iterationWords codeBudget
  have := localBudget.local_words
  have := localBudget.initial_words
  exact Nat.add_le_add (by omega) (Nat.mul_le_mul_left fuel (by omega))

theorem names (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted routines.continuation.code slots) (initialNames : NamesAccounted routines.initialization.code slots)
    (fuel : Nat) : WordIO.NamesAccounted ((program config routines ops fuel).lower (Fresh.port config.handler.sampler.tape)) slots :=
  CallerControl.program_names (routines.layout config) (Fresh.port config.handler.sampler.tape)
    routines.advance routines.continuation routines.localNameFits (CallerHandler.code config ops)
    routines.input routines.initial routines.initialization routines.initialNameFits routines.inputFits
    (by unfold Handler.nameBudget at handlerRoom; omega) ((CallerHandler.names config ops).mono handlerRoom) localNames initialNames fuel

/-- The fresh retention buffer has an encodable index under the primitive's
existing reserve. The handler's fixed scratch floor is below the word bound. -/
theorem handlerNameFits : Interactive.savedBuffer (Fresh.port config.handler.sampler.tape) (CallerHandler.code config ops) < 2 ^ w := by
  have bounded := CallerHandler.buffers config ops
  have room := ops.reserve
  have width := config.sampler.wordFits
  unfold Interactive.savedBuffer
  omega

theorem descriptionFits (fuel : Nat) : ((program config routines ops fuel).lower (Fresh.port config.handler.sampler.tape)).DescriptionFits :=
  CallerControl.program_descriptionFits (routines.layout config) (Fresh.port config.handler.sampler.tape)
    routines.advance routines.continuation routines.localNameFits (CallerHandler.code config ops)
    routines.input routines.initial routines.initialization routines.initialNameFits routines.inputFits
    (CallerHandler.descriptionFits config ops) (handlerNameFits config ops) fuel

theorem resources (slots : Nat) (handlerRoom : Handler.nameBudget config ops ≤ slots)
    (localNames : NamesAccounted routines.continuation.code slots) (initialNames : NamesAccounted routines.initialization.code slots)
    (fuel : Nat) (tape : RandomTape w) (value : U × config.handler.store.Value) (room : admitted config fuel value)
    (before : State w) (holds : (routines.inputLayout config).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((program config routines ops fuel).execute (Fresh.port config.handler.sampler.tape) .unit tape before)) :
    let code := (program config routines ops fuel).lower (Fresh.port config.handler.sampler.tape)
    let stored := codeBudget config routines ops budget localBudget fuel
    let elapsed := timeBudget config routines ops budget localBudget fuel
    finished.time ≤ elapsed ∧ ∃ answer ∈ support (source config routines ops fuel value),
      (routines.outputLayout config).Holds answer finished.state ∧ Postcondition config value.2 answer.2 ∧
      ∃ execution : WordIO.Exec .unit tape code before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers code.registerSlots) ∧ between.SupportBound (max buffers code.memBound) ∧ between.WellFormed ∧
          (code.staticWords registers buffers : Int) + between.liveMem (max buffers code.memBound) ≤
            stored + 4 * (slots + stored) + registers + 3 * buffers + before.liveMem buffers + elapsed := by
  have refined := refines config routines ops fuel
  have bounded := time config routines ops budget localBudget fuel
  have stored := words config routines ops budget localBudget fuel
  have named := names config routines ops slots handlerRoom localNames initialNames fuel
  obtain ⟨elapsed, answer, supported, output, execution, memory⟩ := refined.resources bounded stored
    ⟨named.registers.trans (Nat.add_le_add_left stored slots), named.buffers.trans (Nat.add_le_add_left stored slots)⟩
    tape value room before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, answer, supported, output,
    start_postcondition config routines ops fuel (routines.initial value.1, value.2) room answer supported, execution, memory⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.Caller
