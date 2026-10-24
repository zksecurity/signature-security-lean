import Proofs.Runtime.Caliper.RowFoldSource

/-! Whole-loop memory accounting for the same actual execution as the source
and time claims. Stored unrolling, caller capacity and all visited states count. -/
namespace Signatures.Runtime.CaliperBackend.RowFold
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {G F : Type}
    [DecidableEq (key.Value base)] (layout : RowRequest.Layouts w (key.Value base) G F (val.Value base))
    (default : layout.accumulation.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.accumulation.combine layout.accumulation.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    {source : OracleComp spec layout.accumulation.cache.value.Value} {draw : Interactive.Code w}

theorem resources
    (drawCorrect : Interactive.Refines port .unit layout.accumulation.cache.lookup.unit.representation
      layout.accumulation.cache.value.representation (fun _ => source) draw)
    {drawTime drawWords updateTime updateWords drawNames updateNames : Nat}
    (drawTimeBound : Interactive.TimeBound port .unit layout.accumulation.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords) (updateBound : update.BoundedBy updateTime updateWords)
    (drawNamesBound : WordIO.NamesBound (draw.lower port) drawNames) (updateNamesBound : NamesAccounted update.program.code updateNames)
    (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * layout.row.representation.encoding.words + layout.state.representation.encoding.words < 2 ^ w)
    (tape : RandomTape w) (value : Input layout capacity) (admitted : valid layout value) (before : State w)
    (holds : (input layout capacity countFits storageFits).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout default P comparison correct update updateBuffers reserve capacity port draw).execute port .unit tape before)) :
    finished.time ≤ timeBudget layout capacity drawTime updateTime ∧
    ∃ answer ∈ support (denote layout default P comparison correct update updateBuffers reserve source value),
      layout.state.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape ((code layout default P comparison correct update updateBuffers reserve capacity port draw).lower port)
          before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers ((code layout default P comparison correct update updateBuffers reserve capacity port draw).lower port).registerSlots) ∧
          between.SupportBound (max buffers ((code layout default P comparison correct update updateBuffers reserve capacity port draw).lower port).memBound) ∧ between.WellFormed ∧
          (((code layout default P comparison correct update updateBuffers reserve capacity port draw).lower port).staticWords registers buffers : Int) +
            between.liveMem (max buffers ((code layout default P comparison correct update updateBuffers reserve capacity port draw).lower port).memBound) ≤
              5 * codeBudget layout capacity drawWords updateWords + 4 * max (max 5 drawNames) updateNames + registers + 3 * buffers +
                before.liveMem buffers + timeBudget layout capacity drawTime updateTime :=
  InteractiveFold.resources port _ layout.row.representation layout.state.representation layout.accumulation.cache.wordFits
    layout.raw.representation.fits (RowEvaluation.room layout)
    (fun remaining tape value valid before holds =>
      RowEvaluation.refines layout default P comparison correct update updateBuffers reserve port drawCorrect
        tape value (RowEvaluation.ready_of_room layout remaining value valid) before holds)
    (RowEvaluation.preserves layout default P comparison correct update updateBuffers reserve)
    (fun remaining tape value valid before holds finished reached =>
      RowEvaluation.time_bound layout default P comparison correct update updateBuffers reserve port drawCorrect drawTimeBound updateBound
        tape value (RowEvaluation.ready_of_room layout remaining value valid) before holds finished reached)
    (RowEvaluation.code_bound layout default P comparison correct update updateBuffers reserve port draw drawWordsBound updateBound)
    (RowEvaluation.names layout default P comparison correct update updateBuffers reserve port draw drawNamesBound updateNamesBound)
    capacity countFits storageFits tape value admitted before holds registers buffers initialRegisters initialBuffers finished reached

end Signatures.Runtime.CaliperBackend.RowFold
