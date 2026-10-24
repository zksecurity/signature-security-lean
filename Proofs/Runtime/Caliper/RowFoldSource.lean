import Proofs.Runtime.Caliper.RowFold

/-! Erasing the bounded row representation preserves the entire ordered lazy
cache computation, including its final cache. No message-space enumeration is
introduced by the executed streaming fold. -/
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
    {I : Type} {spec : OracleSpec I}

def sourceStep (sample : OracleComp spec (val.Value base))
    (state : val.Value base × List (key.Value base × val.Value base)) (row : (key.Value base × G) × F) :
    OracleComp spec (val.Value base × List (key.Value base × val.Value base)) :=
  (fun result => (combine (row.2, result.1, state.1), result.2)) <$>
    (QueryImpl.ListCache.handler (fun _ => sample) row.1.1).run state.2

theorem fold_listCache (source : OracleComp spec layout.accumulation.cache.value.Value)
    (rows : List layout.row.Value) (state : layout.state.Value)
    (valid : RowEvaluation.room layout rows.length state) :
    Subtype.val <$> rows.foldlM
      (fun accumulator row => RowEvaluation.denote layout default P comparison correct update updateBuffers reserve source (row, accumulator)) state =
      (rows.map Subtype.val).foldlM (sourceStep (combine := combine) (Subtype.val <$> source)) state.val := by
  induction rows generalizing state with
  | nil => simp only [List.foldlM_nil, List.map_nil, map_pure]
  | cons row rows ih =>
    have ready := RowEvaluation.ready_of_room layout rows.length (row, state) valid
    have step := RowEvaluation.listCache layout default P comparison correct update updateBuffers reserve (source := source) (row, state) ready
    change Subtype.val <$> RowEvaluation.denote layout default P comparison correct update updateBuffers reserve source (row, state) =
      sourceStep (combine := combine) (Subtype.val <$> source) state.val row.val at step
    rw [List.foldlM_cons, List.map_cons, List.foldlM_cons, map_bind, ← step, bind_map_left]
    apply bind_congr_of_forall_mem_support
    intro answer reached
    exact ih answer (RowEvaluation.preserves layout default P comparison correct update updateBuffers reserve
      rows.length (row, state) valid answer reached)

theorem listCache (source : OracleComp spec layout.accumulation.cache.value.Value) {capacity : Nat}
    (value : Input layout capacity) (admitted : valid layout value) :
    Subtype.val <$> denote layout default P comparison correct update updateBuffers reserve source value =
      (value.1.val.map Subtype.val).foldlM (sourceStep (combine := combine) (Subtype.val <$> source)) value.2.val :=
  fold_listCache layout default P comparison correct update updateBuffers reserve source value.1.val value.2 admitted

end Signatures.Runtime.CaliperBackend.RowFold
