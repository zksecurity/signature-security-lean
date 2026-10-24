import Proofs.Runtime.Caliper.SchnorrAGMCache

/-! One derived complete resource account for the constructed Schnorr cache.
The returned entry/table/state, time and intermediate memory belong to the same
execution. The caller supplies budgets only for scalar sampling and addition. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Cache
open Caliper BoundedSource OracleComp OracleSpec
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS : Nat} {M F G I : Type} [Zero F] [Add F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    {spec : OracleSpec I} (layout : Layouts w M F G qH qS)
    (zeroValid : layout.scalar.valid 0)
    (add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2))
    {slots : Nat} (addBuffers : add.program.code.memBound ≤ slots) (slotsFit : slots < 2 ^ w)
    (port : Interactive.Port w spec)

theorem resources {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scalar.representation
      (fun _ => sampleSource) sampler) {addTime addWords sampleTime sampleWords sampleSlots : Nat}
    (addBound : add.BoundedBy addTime addWords)
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime)
    (sampleStored : (sampler.lower port).descriptionWords ≤ sampleWords)
    (addNames : NamesBound add.program.code slots) (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots)
    (tape : RandomTape w) (value : layout.cache.input.Value × (saved layout).Value) (before : State w)
    (holds : (model layout).input.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout zeroValid add addBuffers slotsFit port sampler).execute port .unit tape before)) :
    finished.time ≤ timeBudget layout addTime sampleTime ∧
      ∃ answer ∈ support (source layout sampleSource value), (model layout).output.Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit tape ((code layout zeroValid add addBuffers slotsFit port sampler).lower port)
            before finished.state finished.trace finished.time finished.net finished.peak,
          ∀ between, execution.Visits between →
            RegisterBound between (max registers ((code layout zeroValid add addBuffers slotsFit port sampler).lower port).registerSlots) ∧
            between.SupportBound (max buffers ((code layout zeroValid add addBuffers slotsFit port sampler).lower port).memBound) ∧ between.WellFormed ∧
            (((code layout zeroValid add addBuffers slotsFit port sampler).lower port).staticWords registers buffers : Int) +
              between.liveMem (max buffers ((code layout zeroValid add addBuffers slotsFit port sampler).lower port).memBound) ≤
                5 * codeBudget layout addWords sampleWords + 4 * max 5 (Fresh.nameBudget slots sampleSlots) +
                  registers + 3 * buffers + before.liveMem buffers + timeBudget layout addTime sampleTime :=
  StatefulCacheRead.resources (base := cryptoBase F G Unit M M) (key := cacheKeyTy) (val := entryTy)
    port (model layout) (primitives F G M) comparison (comparison_correct F G M)
    (Fresh.denote layout sampleSource) (Fresh.code layout zeroValid add addBuffers slotsFit port sampler)
    (Fresh.refines layout zeroValid add addBuffers slotsFit port sampleCorrect)
    (Fresh.time_bound layout zeroValid add addBuffers slotsFit port sampleCorrect addBound.time_le sampleBound)
    (Fresh.code_bound layout zeroValid add addBuffers slotsFit port sampler addBound.code_le sampleStored)
    (Fresh.names layout zeroValid add addBuffers slotsFit port sampler addNames sampleNames)
    tape value before holds registers buffers initialRegisters initialBuffers finished reached

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Cache
