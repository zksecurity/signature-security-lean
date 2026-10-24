import Proofs.Runtime.Caliper.BLSOracleBounds
import Proofs.Runtime.Caliper.InteractiveMemory

/-! Complete memory for the full random/hash/sign service, including initial
caller capacity and all three stored query branches. -/

namespace Signatures.Runtime.CaliperBackend.BLSOracle
open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {C G : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)]
    (layout : BLSReply.Layouts w (key.Value base) (val.Value base) C G)
    (default : layout.cache.value.Value) (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op) (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit layout.responseInput layout.point (respond signing))
    {slots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w) (draw : Interactive.Code w)
    {drawSource : ProbComp layout.cache.value.Value}
    (drawCorrect : Interactive.Refines (UniformQuery.port randomBound layout.cache.wordFits randomFits) .unit
      layout.cache.lookup.unit.representation layout.cache.value.representation (fun _ => drawSource) draw)
    {drawTime drawWords drawSlots responseSlots : Nat} {responseTime responseWords : Bool → Nat}
    (drawTimeBound : Interactive.TimeBound (UniformQuery.port randomBound layout.cache.wordFits randomFits) .unit
      layout.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower (UniformQuery.port randomBound layout.cache.wordFits randomFits)).descriptionWords ≤ drawWords)
    (responseBound : ∀ signing, (response signing).BoundedBy (responseTime signing) (responseWords signing))
    (drawNames : WordIO.NamesBound (draw.lower (UniformQuery.port randomBound layout.cache.wordFits randomFits)) drawSlots)
    (responseNames : ∀ signing, NamesAccounted (response signing).program.code responseSlots)

include drawWordsBound responseBound drawNames responseNames in
theorem resource_names : WordIO.NamesBound
    ((code layout default randomBound randomFits P comparison correct response responseBuffers reserve draw).lower
      (UniformQuery.port randomBound layout.cache.wordFits randomFits))
    (max (max 5 drawSlots) responseSlots + codeBudget layout (BLSDispatch.codeBudget layout drawWords responseWords)) := by
  have stored := code_bound layout default randomBound randomFits P comparison correct response responseBuffers reserve draw drawWordsBound responseBound
  have named := names layout default randomBound randomFits P comparison correct response responseBuffers reserve draw drawNames responseNames
  exact ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩

include drawCorrect drawTimeBound drawWordsBound responseBound drawNames responseNames in
theorem memoryBound (tape : RandomTape w)
    (value : (Fin (randomBound + 1) × layout.store.Value) ⊕ (BLSDispatch.input layout default).Value)
    (before : State w) (holds : (input layout default randomBound randomFits).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout default randomBound randomFits P comparison correct response responseBuffers reserve draw).execute
      (UniformQuery.port randomBound layout.cache.wordFits randomFits) .unit tape before)) :
    finished.time ≤ timeBudget layout (BLSDispatch.timeBudget layout drawTime responseTime) ∧
    ∃ answer ∈ support (denote layout default randomBound P comparison correct response responseBuffers reserve drawSource value),
      (output layout randomBound randomFits).Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape
          ((code layout default randomBound randomFits P comparison correct response responseBuffers reserve draw).lower
            (UniformQuery.port randomBound layout.cache.wordFits randomFits)) before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers ((code layout default randomBound randomFits P comparison correct response responseBuffers reserve draw).lower
            (UniformQuery.port randomBound layout.cache.wordFits randomFits)).registerSlots) ∧
          between.SupportBound (max buffers ((code layout default randomBound randomFits P comparison correct response responseBuffers reserve draw).lower
            (UniformQuery.port randomBound layout.cache.wordFits randomFits)).memBound) ∧ between.WellFormed ∧
          (((code layout default randomBound randomFits P comparison correct response responseBuffers reserve draw).lower
            (UniformQuery.port randomBound layout.cache.wordFits randomFits)).staticWords registers buffers : Int) +
            between.liveMem (max buffers ((code layout default randomBound randomFits P comparison correct response responseBuffers reserve draw).lower
              (UniformQuery.port randomBound layout.cache.wordFits randomFits)).memBound) ≤
            codeBudget layout (BLSDispatch.codeBudget layout drawWords responseWords) +
              4 * (max (max 5 drawSlots) responseSlots + codeBudget layout (BLSDispatch.codeBudget layout drawWords responseWords)) +
              registers + 3 * buffers + before.liveMem buffers + timeBudget layout (BLSDispatch.timeBudget layout drawTime responseTime) :=
  (refines layout default randomBound randomFits P comparison correct response responseBuffers reserve draw drawSource drawCorrect).resources
    (time_bound layout default randomBound randomFits P comparison correct response responseBuffers reserve draw drawCorrect drawTimeBound responseBound)
    (code_bound layout default randomBound randomFits P comparison correct response responseBuffers reserve draw drawWordsBound responseBound)
    (resource_names layout default randomBound randomFits P comparison correct response responseBuffers reserve draw drawWordsBound responseBound drawNames responseNames)
    tape value before holds registers buffers initialRegisters initialBuffers finished reached

end Signatures.Runtime.CaliperBackend.BLSOracle
