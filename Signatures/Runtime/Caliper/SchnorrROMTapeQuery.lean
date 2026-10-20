import Signatures.Runtime.Caliper.SchnorrROMTapeFreshMemory
import Signatures.Runtime.Caliper.SchnorrROMTapeFreshSource

/-! Complete constructed raw replay-cell queries. All tape operations, private
uniform draws and reply-cell construction are derived Caliper code. The only
supplied sampling routine draws a represented scalar. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Query
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F : Type} [Zero F] (layout : Layouts w F) (zeroValid : layout.scalar.valid 0)

def code (sampler : Interactive.Code w) := Read.code layout (Fresh.port layout) (Fresh.code layout zeroValid sampler)
def denote (scalarSource : ProbComp layout.scalar.Value) := Read.denote layout (Fresh.denote layout zeroValid scalarSource)
def timeBudget (samplerTime : Nat) := Read.timeBudget layout (Fresh.timeBudget layout zeroValid samplerTime)
def codeBudget (samplerWords : Nat) := Read.codeBudget layout (Fresh.codeBudget layout zeroValid samplerWords)

variable {scalarSource : ProbComp layout.scalar.Value} {sampler : Interactive.Code w}
    (scalarCorrect : Interactive.Refines (Fresh.port layout) .unit layout.unit.representation layout.scalar.representation
      (fun _ => scalarSource) sampler)

include scalarCorrect in
theorem refines : Interactive.Refines (Fresh.port layout) .unit (Read.input layout).representation (Read.output layout).representation
    (denote layout zeroValid scalarSource) (code layout zeroValid sampler) :=
  Read.refines (Fresh.refines layout zeroValid scalarCorrect)

include scalarCorrect in
theorem time_bound {samplerTime : Nat}
    (scalarBound : Interactive.TimeBound (Fresh.port layout) .unit layout.unit.representation sampler samplerTime) :
    Interactive.TimeBound (Fresh.port layout) .unit (Read.input layout).representation
      (code layout zeroValid sampler) (timeBudget layout zeroValid samplerTime) :=
  Read.time_bound layout (Fresh.port layout) (Fresh.refines layout zeroValid scalarCorrect)
    (Fresh.time_bound layout zeroValid scalarCorrect scalarBound)

theorem code_bound (sampler : Interactive.Code w) {samplerWords : Nat}
    (scalarBound : (sampler.lower (Fresh.port layout)).descriptionWords ≤ samplerWords) :
    ((code layout zeroValid sampler).lower (Fresh.port layout)).descriptionWords ≤ codeBudget layout zeroValid samplerWords :=
  Read.code_bound layout (Fresh.port layout) (Fresh.code layout zeroValid sampler)
    (Fresh.code_bound layout zeroValid sampler scalarBound)

theorem buffers (sampler : Interactive.Code w) :
    ((code layout zeroValid sampler).lower (Fresh.port layout)).memBound ≤ max 7 ((sampler.lower (Fresh.port layout)).memBound + 1) := by
  have drawn := Fresh.buffers layout zeroValid sampler
  have outer := Read.buffers layout (Fresh.port layout) (Fresh.code layout zeroValid sampler)
  change ((code layout zeroValid sampler).lower (Fresh.port layout)).memBound ≤ _ at outer
  omega

theorem descriptionFits (sampler : Interactive.Code w)
    (scalarFits : (sampler.lower (Fresh.port layout)).DescriptionFits)
    (bufferFits : (sampler.lower (Fresh.port layout)).memBound < 2 ^ w) :
    ((code layout zeroValid sampler).lower (Fresh.port layout)).DescriptionFits := by
  apply Read.descriptionFits_of_buffers layout (Fresh.port layout) (Fresh.code layout zeroValid sampler)
    (Fresh.descriptionFits layout zeroValid sampler scalarFits)
  have bounded := Fresh.buffers layout zeroValid sampler
  have width := layout.wordFits
  omega

include scalarCorrect in
/-- Complete machine observation recovers the original raw oracle, including
its entire state, with no assumed complete-handler correctness premise. -/
theorem observe_rawOracle (i : (Schnorr.RawTape.Spec F).Domain) (state : Schnorr.RawTape.State F)
    (valid : (Read.input layout).valid (Read.rawInput i state))
    (tape : RandomTape w) (before : State w)
    (holds : (Read.input layout).representation.Holds ⟨Read.rawInput i state, valid⟩ before) :
    (fun result => (Interactive.observe (Read.output layout).representation result).map (fun value => Read.rawOutput i value.val)) <$>
        (code layout zeroValid sampler).execute (Fresh.port layout) .unit tape before =
      some <$> simulateQ (Fresh.sample layout scalarSource) ((Schnorr.RawTape.oracle i).run state) :=
  Read.observe_rawOracle layout (Fresh.port layout) (Fresh.code layout zeroValid sampler)
    (Fresh.denote layout zeroValid scalarSource) (Fresh.refines layout zeroValid scalarCorrect)
    (Fresh.sample layout scalarSource) i state valid (Fresh.rawDraw layout zeroValid scalarSource i valid.1) tape before holds

include scalarCorrect in
theorem resources {samplerTime samplerWords slots : Nat}
    (scalarTimeBound : Interactive.TimeBound (Fresh.port layout) .unit layout.unit.representation sampler samplerTime)
    (scalarWordsBound : (sampler.lower (Fresh.port layout)).descriptionWords ≤ samplerWords)
    (scalarNames : WordIO.NamesBound (sampler.lower (Fresh.port layout)) slots)
    (tape : RandomTape w) (value : (Read.input layout).Value) (before : State w)
    (holds : (Read.input layout).representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w) (reached : some finished ∈ support ((code layout zeroValid sampler).execute (Fresh.port layout) .unit tape before)) :
    finished.time ≤ timeBudget layout zeroValid samplerTime ∧
    ∃ answer ∈ support (denote layout zeroValid scalarSource value), (Read.output layout).representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape ((code layout zeroValid sampler).lower (Fresh.port layout)) before finished.state
          finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers ((code layout zeroValid sampler).lower (Fresh.port layout)).registerSlots) ∧
          between.SupportBound (max buffers ((code layout zeroValid sampler).lower (Fresh.port layout)).memBound) ∧ between.WellFormed ∧
          (((code layout zeroValid sampler).lower (Fresh.port layout)).staticWords registers buffers : Int) +
            between.liveMem (max buffers ((code layout zeroValid sampler).lower (Fresh.port layout)).memBound) ≤
              5 * codeBudget layout zeroValid samplerWords + 4 * Fresh.codeBudget layout zeroValid samplerWords +
                4 * max 3 slots + registers + 3 * buffers + before.liveMem buffers + timeBudget layout zeroValid samplerTime := by
  have stored := Fresh.code_bound layout zeroValid sampler scalarWordsBound
  have accounted := Fresh.names layout zeroValid sampler scalarNames
  have reserved : WordIO.NamesBound ((Fresh.code layout zeroValid sampler).lower (Fresh.port layout))
      (max 3 slots + Fresh.codeBudget layout zeroValid samplerWords) :=
    ⟨accounted.registers.trans (Nat.add_le_add_left stored _), accounted.buffers.trans (Nat.add_le_add_left stored _)⟩
  have result := Read.resources layout (Fresh.port layout) (Fresh.code layout zeroValid sampler)
    (Fresh.refines layout zeroValid scalarCorrect) (Fresh.time_bound layout zeroValid scalarCorrect scalarTimeBound)
    stored reserved tape value before holds registers buffers initialRegisters initialBuffers finished reached
  obtain ⟨elapsed, answer, supported, output, execution, visitedBound⟩ := result
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ := visitedBound between visited
  refine ⟨registerBound, bufferBound, wellFormed, ?_⟩
  push_cast at memory
  dsimp only [code, codeBudget, timeBudget]
  omega

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Query
