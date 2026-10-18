import Signatures.Runtime.Caliper.PairSamplingBounds
import Signatures.Runtime.Caliper.WordFrames

/-! Complete pair-sampler memory bounds, including component code, dense names,
initial caller capacity and every intermediate state of the actual execution. -/

namespace Signatures.Runtime.CaliperBackend.PairSampling

open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {A B I : Type} {spec : OracleSpec I}
    (left : Layout w A) (right : Layout w B) (hw : 16 < 2 ^ w)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w)
    (port : Interactive.Port w spec) (first second : Interactive.Code w)

theorem memoryBound {firstSource : OracleComp spec left.Value} {secondSource : OracleComp spec right.Value}
    (firstCorrect : Interactive.Refines port .unit (input w).representation left.representation
      (fun _ => firstSource) first)
    (secondCorrect : Interactive.Refines port .unit (input w).representation right.representation
      (fun _ => secondSource) second)
    {firstTime secondTime firstWords secondWords firstSlots secondSlots : Nat}
    (firstTimeBound : Interactive.TimeBound port .unit (input w).representation first firstTime)
    (secondTimeBound : Interactive.TimeBound port .unit (input w).representation second secondTime)
    (firstWordsBound : (first.lower port).descriptionWords ≤ firstWords)
    (secondWordsBound : (second.lower port).descriptionWords ≤ secondWords)
    (firstNames : WordIO.NamesBound (first.lower port) firstSlots)
    (secondNames : WordIO.NamesBound (second.lower port) secondSlots)
    (tape : RandomTape w) (value : (input w).Value) (before : State w)
    (holds : (input w).representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code left right hw fits port first second).execute port .unit tape before)) :
    finished.time ≤ timeBudget left right firstTime secondTime ∧
    ∃ execution : WordIO.Exec .unit tape ((code left right hw fits port first second).lower port) before finished.state
        finished.trace finished.time finished.net finished.peak,
      ∀ between, execution.Visits between →
        RegisterBound between (max registers ((code left right hw fits port first second).lower port).registerSlots) ∧
        between.SupportBound (max buffers ((code left right hw fits port first second).lower port).memBound) ∧ between.WellFormed ∧
        (((code left right hw fits port first second).lower port).staticWords registers buffers : Int) +
          between.liveMem (max buffers ((code left right hw fits port first second).lower port).memBound) ≤
            codeBudget left right firstWords secondWords + 4 * slots firstSlots secondSlots + registers + 3 * buffers +
              before.liveMem buffers + timeBudget left right firstTime secondTime := by
  have refined := refines (hw := hw) (fits := fits) firstCorrect secondCorrect
  have bounded := time_bound (hw := hw) (fits := fits) firstCorrect secondCorrect firstTimeBound secondTimeBound
  have time := bounded tape value before holds finished reached
  have peak := bounded.bufferPeak refined (by decide) tape value before holds finished reached
  obtain ⟨answer, _, result, equal, _, _, execution⟩ := (refined tape value before holds).right_support reached
  cases Option.some.inj equal
  refine ⟨time, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ :=
    visited.total_memory_bound registers buffers initialRegisters initialBuffers holds.2.2.1
  refine ⟨registerBound, bufferBound, wellFormed, ?_⟩
  have staticBound := staticMemory left right hw fits port first second firstWordsBound secondWordsBound firstNames secondNames registers buffers
  have initialMemory := liveMem_eq_of_supportBound initialBuffers
    (Nat.le_max_left buffers ((code left right hw fits port first second).lower port).memBound)
  omega

end Signatures.Runtime.CaliperBackend.PairSampling
