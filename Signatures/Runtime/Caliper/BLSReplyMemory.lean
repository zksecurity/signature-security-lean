import Signatures.Runtime.Caliper.BLSReplyBounds

/-! Complete memory for the same execution that returns the source reply and
updated state. Initial memory includes every caller-owned buffer capacity. -/

namespace Signatures.Runtime.CaliperBackend.BLSReply
open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {C G : Type}
    [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) (val.Value base) C G)
    (default : layout.cache.value.Value) (signing : Bool)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op) (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (port : Interactive.Port w unifSpec) (draw : Interactive.Code w)
    {respond : val.Value base × C → G} (response : Implementation .unit layout.responseInput layout.point respond)
    {slots : Nat} (responseBuffers : response.program.code.memBound ≤ slots) (reserve : slots + 3 < 2 ^ w)
    {drawTime drawWords responseTime responseWords drawSlots responseSlots : Nat}
    (drawCodeBound : (draw.lower port).descriptionWords ≤ drawWords)
    (drawNames : WordIO.NamesBound (draw.lower port) drawSlots)
    (responseBound : response.BoundedBy responseTime responseWords)
    (responseNames : NamesAccounted response.program.code responseSlots)

include drawCodeBound drawNames responseBound responseNames in
theorem staticMemory (registers buffers : Nat) :
    ((code layout default signing P comparison correct port draw response responseBuffers reserve).lower port).staticWords registers buffers ≤
      5 * codeBudget layout drawWords responseWords + 4 * max (max 5 drawSlots) responseSlots + registers + 3 * buffers := by
  have codeBound := code_bound layout default signing P comparison correct port draw drawCodeBound response responseBuffers reserve responseBound
  have nameBound := names layout default signing P comparison correct port draw response responseBuffers reserve drawNames responseNames
  rcases nameBound with ⟨registerBound, bufferBound⟩
  unfold WordIO.Code.staticWords
  omega

include drawCodeBound drawNames responseBound responseNames in
theorem memoryBound {drawSource : ProbComp layout.cache.value.Value}
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation layout.cache.value.representation
      (fun _ => drawSource) draw)
    (drawBound : Interactive.TimeBound port .unit layout.cache.lookup.unit.representation draw drawTime)
    (tape : RandomTape w) (value : (layout.input default.val signing).Value) (before : State w)
    (holds : (layout.input default.val signing).representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout default signing P comparison correct port draw response responseBuffers reserve).execute port .unit tape before)) :
    finished.time ≤ timeBudget layout drawTime responseTime ∧
    ∃ answer ∈ support (denote layout default signing P comparison correct response responseBuffers reserve drawSource value),
      layout.output.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape ((code layout default signing P comparison correct port draw response responseBuffers reserve).lower port)
          before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers ((code layout default signing P comparison correct port draw response responseBuffers reserve).lower port).registerSlots) ∧
          between.SupportBound (max buffers ((code layout default signing P comparison correct port draw response responseBuffers reserve).lower port).memBound) ∧
          between.WellFormed ∧
          (((code layout default signing P comparison correct port draw response responseBuffers reserve).lower port).staticWords registers buffers : Int) +
            between.liveMem (max buffers ((code layout default signing P comparison correct port draw response responseBuffers reserve).lower port).memBound) ≤
              5 * codeBudget layout drawWords responseWords + 4 * max (max 5 drawSlots) responseSlots + registers + 3 * buffers +
                before.liveMem buffers + timeBudget layout drawTime responseTime := by
  have refined := refines layout default signing P comparison correct port draw response responseBuffers reserve drawSource drawCorrect
  have bounded := time_bound layout default signing P comparison correct port draw drawCorrect drawBound response responseBuffers reserve responseBound
  have time := bounded tape value before holds finished reached
  have peak := bounded.bufferPeak refined (by decide) tape value before holds finished reached
  obtain ⟨answer, supported, result, equal, output, _, execution⟩ := (refined tape value before holds).right_support reached
  cases Option.some.inj equal
  refine ⟨time, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ :=
    visited.total_memory_bound registers buffers initialRegisters initialBuffers holds.2.2.1
  refine ⟨registerBound, bufferBound, wellFormed, ?_⟩
  have staticBound := staticMemory layout default signing P comparison correct port draw response responseBuffers reserve
    drawCodeBound drawNames responseBound responseNames registers buffers
  have initialMemory := liveMem_eq_of_supportBound initialBuffers
    (Nat.le_max_left buffers ((code layout default signing P comparison correct port draw response responseBuffers reserve).lower port).memBound)
  omega

end Signatures.Runtime.CaliperBackend.BLSReply
