import Proofs.Runtime.Caliper.SchnorrAGMHashDispatchBounds
import Proofs.Runtime.Caliper.SchnorrAGMHashDispatchSource

/-! Stored code and all live memory are bounded along the same execution that
returns the original all-shape hash result. The bound includes the caller's initial state,
request-shape tests, retained coefficients and metadata, register descriptors and temporary buffers. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.HashDispatch
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS : Nat} {M F G I : Type} [Zero F] [Mul F] [Add F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    {spec : OracleSpec I} (layout : Layouts w M F G qH qS) (zeroValid : layout.hash.scheme.scalar.valid 0)
    (mul : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.hash.scheme.affine layout.hash.scheme.scalar (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w) (port : Interactive.Port w spec)

theorem resources {sampleSource : OracleComp spec layout.hash.scheme.scalar.Value} {sampler : Interactive.Code w}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.hash.scheme.scalar.representation
      (fun _ => sampleSource) sampler) {mulTime mulWords addTime addWords sampleTime sampleWords sampleSlots : Nat}
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime)
    (sampleStored : (sampler.lower port).descriptionWords ≤ sampleWords)
    (mulNames : NamesBound mul.program.code slots) (addNames : NamesBound add.program.code slots)
    (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots)
    (tape : RandomTape w) (value : layout.input.Value) (before : State w)
    (holds : layout.input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout zeroValid mul add mulBuffers addBuffers reserve port sampler).execute port .unit tape before)) :
    finished.time ≤ timeBudget layout mulTime addTime sampleTime ∧
      ∃ answer ∈ support (source layout zeroValid mul add mulBuffers addBuffers reserve sampleSource value),
        (Read.output layout.hash.scheme).representation.Holds answer finished.state ∧
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
    refined.resources timed stored allNames tape value before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, result, execution, ?_⟩
  intro between visited
  have bounded := bounds between visited
  refine ⟨bounded.1, bounded.2.1, bounded.2.2.1, ?_⟩
  have := bounded.2.2.2
  omega

end Signatures.Runtime.CaliperBackend.SchnorrAGM.HashDispatch
