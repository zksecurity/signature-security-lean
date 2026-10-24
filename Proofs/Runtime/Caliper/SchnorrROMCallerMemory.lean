import Proofs.Runtime.Caliper.SchnorrROMCallerSource

/-! Joint correctness, time, static storage and memory at every visited state
for the executed caller-facing ROM service, including packet conversion. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.CallerHandler
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec CallerPackets
variable {w : Nat} {M F G : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (ops : Handler.Operations config)

theorem resources (budget : Handler.Budget config ops) (random : RandomTape w) (value : Packet config) (valid : ready config value)
    (before : State w) (holds : (input config).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code config ops).execute (Fresh.port config.handler.sampler.tape) .unit random before)) :
    finished.time ≤ timeBudget config ops budget ∧
      ∃ answer ∈ support (source config ops value), (output config).Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit random ((code config ops).lower (Fresh.port config.handler.sampler.tape)) before finished.state
            finished.trace finished.time finished.net finished.peak,
          ∀ between, execution.Visits between →
            RegisterBound between (max registers ((code config ops).lower (Fresh.port config.handler.sampler.tape)).registerSlots) ∧
            between.SupportBound (max buffers ((code config ops).lower (Fresh.port config.handler.sampler.tape)).memBound) ∧ between.WellFormed ∧
            (((code config ops).lower (Fresh.port config.handler.sampler.tape)).staticWords registers buffers : Int) +
              between.liveMem (max buffers ((code config ops).lower (Fresh.port config.handler.sampler.tape)).memBound) ≤
                5 * codeBudget config ops budget + 4 * Handler.nameBudget config ops + registers + 3 * buffers +
                  before.liveMem buffers + timeBudget config ops budget := by
  have stored := code_bound config ops budget
  have named := names config ops
  have allNames : WordIO.NamesBound ((code config ops).lower (Fresh.port config.handler.sampler.tape))
      (Handler.nameBudget config ops + codeBudget config ops budget) :=
    ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    (refines config ops).resources (time_bound config ops budget) stored allNames
      random value valid before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, result, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ := bounds between visited
  exact ⟨registerBound, bufferBound, wellFormed, by push_cast at memory; omega⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.CallerHandler
