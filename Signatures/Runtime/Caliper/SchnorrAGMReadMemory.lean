import Signatures.Runtime.Caliper.SchnorrAGMReadBounds
import Signatures.Runtime.Caliper.SchnorrAGMReadSource

/-! Complete code-plus-live-memory bounds for the same execution that returns
the source read result. Initial caller memory, all retained metadata, temporary
copies, register descriptors and buffer capacities are included. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Read
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS : Nat} {M F G I : Type} [Zero F] [Add F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    {spec : OracleSpec I} (layout : Layouts w M F G qH qS) (zeroValid : layout.scalar.valid 0)
    (add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2))
    {slots : Nat} (addBuffers : add.program.code.memBound ≤ slots) (slotsFit : slots < 2 ^ w)
    (port : Interactive.Port w spec)

theorem resources {sampleSource : OracleComp spec layout.scalar.Value} {sampler : Interactive.Code w}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scalar.representation
      (fun _ => sampleSource) sampler) {addTime addWords sampleTime sampleWords sampleSlots : Nat}
    (addBound : add.BoundedBy addTime addWords)
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime)
    (sampleStored : (sampler.lower port).descriptionWords ≤ sampleWords)
    (addNames : NamesBound add.program.code slots) (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots)
    (tape : RandomTape w) (value : (input layout).Value) (before : State w)
    (holds : (input layout).representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout zeroValid add addBuffers slotsFit port sampler).execute port .unit tape before)) :
    finished.time ≤ timeBudget layout addTime sampleTime ∧
      ∃ answer ∈ support (source layout zeroValid sampleSource value), (output layout).representation.Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit tape ((code layout zeroValid add addBuffers slotsFit port sampler).lower port)
            before finished.state finished.trace finished.time finished.net finished.peak,
          ∀ between, execution.Visits between →
            RegisterBound between (max registers ((code layout zeroValid add addBuffers slotsFit port sampler).lower port).registerSlots) ∧
            between.SupportBound (max buffers ((code layout zeroValid add addBuffers slotsFit port sampler).lower port).memBound) ∧ between.WellFormed ∧
            (((code layout zeroValid add addBuffers slotsFit port sampler).lower port).staticWords registers buffers : Int) +
              between.liveMem (max buffers ((code layout zeroValid add addBuffers slotsFit port sampler).lower port).memBound) ≤
                5 * codeBudget layout addWords sampleWords + 4 * max 5 (Fresh.nameBudget slots sampleSlots) +
                  registers + 3 * buffers + before.liveMem buffers + timeBudget layout addTime sampleTime := by
  have refined := refines layout zeroValid add addBuffers slotsFit port sampleCorrect
  have timed := time_bound layout zeroValid add addBuffers slotsFit port sampleCorrect addBound.time_le sampleBound
  have stored := code_bound layout zeroValid add addBuffers slotsFit port sampler addBound.code_le sampleStored
  have named := names layout zeroValid add addBuffers slotsFit port sampler addNames sampleNames
  have allNames : WordIO.NamesBound ((code layout zeroValid add addBuffers slotsFit port sampler).lower port)
      (max 5 (Fresh.nameBudget slots sampleSlots) + codeBudget layout addWords sampleWords) :=
    ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    refined.resources timed stored allNames tape value before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, result, execution, ?_⟩
  intro between visited
  have bounded := bounds between visited
  refine ⟨bounded.1, bounded.2.1, bounded.2.2.1, ?_⟩
  have := bounded.2.2.2
  omega

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Read
