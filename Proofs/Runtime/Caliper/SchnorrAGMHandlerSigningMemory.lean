import Proofs.Runtime.Caliper.SchnorrAGMHandlerSigningBounds
import Proofs.Runtime.Caliper.SchnorrAGMHandlerSigningSource

/-! Total memory covers the same source-correct signing execution, including
the saved configuration, both draws, complete stored code and caller memory. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.SigningComponent
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS randomBound : Nat} {M F G I : Type}
    [Zero F] [SMul F G] [Sub G] [Neg F] [DecidableEq M] [DecidableEq G]
    {spec : OracleSpec I} (layout : Handler.Layouts w M F G qH qS randomBound)
    (zeroValid : layout.scheme.scalar.valid 0)
    (scale : Implementation .unit layout.arithmetic.arithmetic.scaleArgs layout.scheme.point (fun args => args.1 • args.2))
    (sub : Implementation .unit layout.arithmetic.arithmetic.points layout.scheme.point (fun args => args.1 - args.2))
    (negate : Implementation .unit layout.scheme.scalar layout.scheme.scalar Neg.neg)
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots)
    (subBuffers : sub.program.code.memBound ≤ slots) (negateBuffers : negate.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w) (port : Interactive.Port w spec)

theorem resources {sampleSource : OracleComp spec layout.scheme.scalar.Value} {sampler : Interactive.Code w}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => sampleSource) sampler) {scaleTime scaleWords subTime subWords negateTime negateWords sampleTime sampleWords primitiveNames sampleSlots : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords)
    (negateBound : negate.BoundedBy negateTime negateWords)
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime)
    (sampleStored : (sampler.lower port).descriptionWords ≤ sampleWords)
    (scaleNames : NamesAccounted scale.program.code primitiveNames) (subNames : NamesAccounted sub.program.code primitiveNames)
    (negateNames : NamesAccounted negate.program.code primitiveNames)
    (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots)
    (tape : RandomTape w) (args : layout.signingInput.Value) (before : State w)
    (holds : layout.signingInput.representation.Holds args before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).execute port .unit tape before)) :
    finished.time ≤ timeBudget layout scaleTime subTime negateTime sampleTime ∧
      ∃ answer ∈ support (source layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampleSource args),
        layout.scalarOutput.representation.Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit tape ((code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port)
            before finished.state finished.trace finished.time finished.net finished.peak,
          ∀ between, execution.Visits between →
            RegisterBound between (max registers ((code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port).registerSlots) ∧
            between.SupportBound (max buffers ((code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port).memBound) ∧ between.WellFormed ∧
            (((code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port).staticWords registers buffers : Int) +
              between.liveMem (max buffers ((code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port).memBound) ≤
                5 * codeBudget layout scaleWords subWords negateWords sampleWords + 4 * Signing.Sampling.nameBudget primitiveNames sampleSlots +
                  registers + 3 * buffers + before.liveMem buffers + timeBudget layout scaleTime subTime negateTime sampleTime := by
  have refined := refines layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampleCorrect
  have timed := time_bound layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampleCorrect
    scaleBound subBound negateBound sampleBound
  have stored := code_bound layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler
    scaleBound subBound negateBound sampleStored
  have named := names layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler
    scaleNames subNames negateNames sampleNames
  have allNames : WordIO.NamesBound ((code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port)
      (Signing.Sampling.nameBudget primitiveNames sampleSlots + codeBudget layout scaleWords subWords negateWords sampleWords) :=
    ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    refined.resources timed stored allNames tape args before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, result, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ := bounds between visited
  exact ⟨registerBound, bufferBound, wellFormed, by omega⟩

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.SigningComponent
