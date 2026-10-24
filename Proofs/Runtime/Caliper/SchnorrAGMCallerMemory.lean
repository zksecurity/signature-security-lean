import Proofs.Runtime.Caliper.SchnorrAGMCallerSource

/-! The complete caller-facing service has charged packet conversion, stored code,
request copies, configuration, descriptors and all pre-existing caller memory. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerHandler
open Caliper BoundedSource OracleComp OracleSpec CallerPackets
variable {w qH qS randomBound : Nat} {M F G : Type}
    [Zero F] [Mul F] [Add F] [Neg F] [SMul F G] [Sub G]
    [DecidableEq F] [DecidableEq M] [DecidableEq G]
    (layout : Handler.Layouts w M F G qH qS randomBound) (ops : Handler.Operations layout) (budget : Handler.Budget layout ops)

theorem resources {sampleSource : ProbComp layout.scheme.scalar.Value} {sampler : Interactive.Code w}
    (sampleCorrect : Interactive.Refines layout.random.port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => sampleSource) sampler) {sampleTime sampleWords sampleSlots : Nat}
    (sampleBound : Interactive.TimeBound layout.random.port .unit (PairSampling.input w).representation sampler sampleTime)
    (sampleStored : (sampler.lower layout.random.port).descriptionWords ≤ sampleWords)
    (sampleNames : WordIO.NamesBound (sampler.lower layout.random.port) sampleSlots)
    (tape : RandomTape w) (args : Packet layout) (valid : ready layout args) (before : State w)
    (holds : (input layout).Holds args before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout ops sampler).execute layout.random.port .unit tape before)) :
    finished.time ≤ timeBudget layout ops budget sampleTime ∧
      ∃ answer ∈ support (source layout ops sampleSource args),
        (output layout).Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit tape ((code layout ops sampler).lower layout.random.port)
            before finished.state finished.trace finished.time finished.net finished.peak,
          ∀ between, execution.Visits between →
            RegisterBound between (max registers ((code layout ops sampler).lower layout.random.port).registerSlots) ∧
            between.SupportBound (max buffers ((code layout ops sampler).lower layout.random.port).memBound) ∧ between.WellFormed ∧
            (((code layout ops sampler).lower layout.random.port).staticWords registers buffers : Int) +
              between.liveMem (max buffers ((code layout ops sampler).lower layout.random.port).memBound) ≤
                5 * codeBudget layout ops budget sampleWords + 4 * Handler.nameBudget layout ops sampleSlots +
                  registers + 3 * buffers + before.liveMem buffers + timeBudget layout ops budget sampleTime := by
  have refined := refines layout ops sampleCorrect
  have timed := time_bound layout ops sampleCorrect budget sampleBound
  have stored := code_bound layout ops budget sampleStored
  have named := names layout ops sampleNames
  have allNames : WordIO.NamesBound ((code layout ops sampler).lower layout.random.port)
      (Handler.nameBudget layout ops sampleSlots + codeBudget layout ops budget sampleWords) :=
    ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    refined.resources timed stored allNames tape args valid before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, result, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ := bounds between visited
  exact ⟨registerBound, bufferBound, wellFormed, by omega⟩

end Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerHandler
