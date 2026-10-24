import Proofs.Runtime.Caliper.SchnorrROMSigningHandlerBounds

/-! The signing output, elapsed time, stored program and all visited memory
refer to the same supported machine execution, including retained LIVE/tapes. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Handler
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G C : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (layout : Layouts w M F G C) (zeroValid : layout.sampler.tape.scalar.valid 0)
    (scale : Implementation .unit layout.core.arithmetic.scaleArgs layout.core.point (fun value => value.1 • value.2))
    (sub : Implementation .unit layout.core.arithmetic.points layout.core.point (fun value => value.1 - value.2))
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (subBuffers : sub.program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w) (caller : PrivateSampler.Caller layout.sampler)

theorem resources (fuel localTime initialTime localNames primitiveNames : Nat)
    (localBound : ∀ value, caller.continuation.time value ≤ localTime) (initialBound : ∀ value, caller.initialCode.time value ≤ initialTime)
    (localNamed : NamesAccounted caller.continuation.code localNames) (initialNamed : NamesAccounted caller.initialCode.code localNames)
    {scaleTime subTime scaleWords subWords : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords)
    (scaleNamed : NamesAccounted scale.program.code primitiveNames) (subNamed : NamesAccounted sub.program.code primitiveNames)
    (tape : RandomTape w) (input : layout.input.Value) (valid : ready layout fuel input)
    (before : State w) (holds : layout.input.representation.Holds input before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel).execute
      (Fresh.port layout.sampler.tape) .unit tape before)) :
    finished.time ≤ timeBudget layout zeroValid localTime initialTime fuel scaleTime subTime ∧
    ∃ answer ∈ support (source layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel input),
      layout.output.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape
          ((code layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel).lower (Fresh.port layout.sampler.tape)) before
          finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers
            ((code layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel).lower (Fresh.port layout.sampler.tape)).registerSlots) ∧
          between.SupportBound (max buffers
            ((code layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel).lower (Fresh.port layout.sampler.tape)).memBound) ∧
          between.WellFormed ∧
          (((code layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel).lower (Fresh.port layout.sampler.tape)).staticWords registers buffers : Int) +
            between.liveMem (max buffers
              ((code layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel).lower (Fresh.port layout.sampler.tape)).memBound) ≤
              5 * codeBudget layout zeroValid caller fuel scaleWords subWords + 4 * nameBudget layout zeroValid localNames primitiveNames +
                registers + 3 * buffers + before.liveMem buffers + timeBudget layout zeroValid localTime initialTime fuel scaleTime subTime := by
  have words := code_bound layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel scaleBound subBound
  have named := names layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel localNames primitiveNames
    localNamed initialNamed scaleNamed subNamed
  have reserved : WordIO.NamesBound
      ((code layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel).lower (Fresh.port layout.sampler.tape))
      (nameBudget layout zeroValid localNames primitiveNames + codeBudget layout zeroValid caller fuel scaleWords subWords) :=
    ⟨named.registers.trans (Nat.add_le_add_left words _), named.buffers.trans (Nat.add_le_add_left words _)⟩
  have checked := (refines layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel).resources
    (time_bound layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel localTime initialTime localBound initialBound scaleBound subBound)
    words reserved tape input valid before holds registers buffers initialRegisters initialBuffers finished reached
  obtain ⟨elapsed, answer, supported, output, execution, visitedBound⟩ := checked
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ := visitedBound between visited
  exact ⟨registerBound, bufferBound, wellFormed, by push_cast at memory; omega⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Handler
