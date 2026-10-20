import Signatures.Runtime.Caliper.SchnorrAGMHandlerHashBounds
import Signatures.Runtime.Caliper.SchnorrAGMHandlerHashSource

/-! Total memory for the same source-correct hash execution includes the saved
configuration, stored program, caller memory and every intermediate state. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.HashComponent
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS randomBound : Nat} {M F G I : Type}
    [Zero F] [Mul F] [Add F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    {spec : OracleSpec I} (layout : Handler.Layouts w M F G qH qS randomBound)
    (zeroValid : layout.scheme.scalar.valid 0)
    (mul : Implementation .unit layout.scheme.affine layout.scheme.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.scheme.affine layout.scheme.scalar (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w) (port : Interactive.Port w spec)

theorem resources {sampleSource : OracleComp spec layout.scheme.scalar.Value} {sampler : Interactive.Code w}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => sampleSource) sampler) {mulTime mulWords addTime addWords sampleTime sampleWords sampleSlots : Nat}
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime)
    (sampleStored : (sampler.lower port).descriptionWords ≤ sampleWords)
    (mulNames : NamesBound mul.program.code slots) (addNames : NamesBound add.program.code slots)
    (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots)
    (tape : RandomTape w) (args : layout.hashInput.Value) (before : State w)
    (holds : layout.hashInput.representation.Holds args before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).execute port .unit tape before)) :
    finished.time ≤ timeBudget layout mulTime addTime sampleTime ∧
      ∃ answer ∈ support (source layout zeroValid mul add mulBuffers addBuffers reserve sampleSource args),
        layout.scalarOutput.representation.Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit tape ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port)
            before finished.state finished.trace finished.time finished.net finished.peak,
          ∀ between, execution.Visits between →
            RegisterBound between (max registers ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).registerSlots) ∧
            between.SupportBound (max buffers ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).memBound) ∧ between.WellFormed ∧
            (((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).staticWords registers buffers : Int) +
              between.liveMem (max buffers ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port).memBound) ≤
                5 * codeBudget layout mulWords addWords sampleWords + 4 * max 5 (Fresh.nameBudget slots sampleSlots) +
                  registers + 3 * buffers + before.liveMem buffers + timeBudget layout mulTime addTime sampleTime := by
  have refined := refines layout zeroValid mul add mulBuffers addBuffers reserve port sampleCorrect
  have timed := time_bound layout zeroValid mul add mulBuffers addBuffers reserve port sampleCorrect mulBound addBound sampleBound
  have stored := code_bound layout zeroValid mul add mulBuffers addBuffers reserve port sampler mulBound addBound sampleStored
  have named := names layout zeroValid mul add mulBuffers addBuffers reserve port sampler mulNames addNames sampleNames
  have allNames : WordIO.NamesBound ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).lower port)
      (max 5 (Fresh.nameBudget slots sampleSlots) + codeBudget layout mulWords addWords sampleWords) :=
    ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    refined.resources timed stored allNames tape args before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, result, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ := bounds between visited
  exact ⟨registerBound, bufferBound, wellFormed, by omega⟩

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.HashComponent
