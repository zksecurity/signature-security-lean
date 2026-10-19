import Signatures.Runtime.Caliper.RowFoldMemory

/-! A row fold adds at most one private-cache entry per occupied row. This
postcondition leaves the remaining extraction reservation available for later
folds and the final target lookup; allocated padding consumes no cache entries. -/
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
    (source : OracleComp spec layout.accumulation.cache.value.Value)

theorem fold_cache_growth (rows : List layout.row.Value) (state : layout.state.Value)
    (valid : RowEvaluation.room layout rows.length state) (answer : layout.state.Value)
    (reached : answer ∈ support (rows.foldlM
      (fun accumulator row => RowEvaluation.denote layout default P comparison correct update updateBuffers reserve source (row, accumulator)) state)) :
    answer.val.2.length ≤ state.val.2.length + rows.length := by
  induction rows generalizing state with
  | nil =>
    simp only [List.foldlM_nil, support_pure, Set.mem_singleton_iff] at reached
    subst answer
    omega
  | cons row rows ih =>
    rw [List.foldlM_cons, mem_support_bind_iff] at reached
    obtain ⟨middle, step, tail⟩ := reached
    have continued := RowEvaluation.preserves layout default P comparison correct update updateBuffers reserve
      rows.length (row, state) valid middle step
    have rest := ih middle continued tail
    have ready := RowEvaluation.ready_of_room layout rows.length (row, state) valid
    unfold RowEvaluation.denote at step
    rw [dite_eq_left ready] at step
    have first := EncodedCacheAccumulate.cache_growth layout.accumulation P comparison correct update updateBuffers reserve
      source (RowEvaluation.request layout default (row, state) ready) middle step
    change middle.val.2.length ≤ state.val.2.length + 1 at first
    simp only [List.length_cons]
    omega

theorem cache_growth {capacity : Nat} (value : Input layout capacity) (admitted : valid layout value)
    (answer : layout.state.Value)
    (reached : answer ∈ support (denote layout default P comparison correct update updateBuffers reserve source value)) :
    answer.val.2.length ≤ value.2.val.2.length + value.1.val.length :=
  fold_cache_growth layout default P comparison correct update updateBuffers reserve source value.1.val value.2 admitted answer reached

theorem remaining_room {capacity : Nat} (value : Input layout capacity) (remaining : Nat)
    (reserved : RowEvaluation.room layout (value.1.val.length + remaining) value.2)
    (answer : layout.state.Value)
    (reached : answer ∈ support (denote layout default P comparison correct update updateBuffers reserve source value)) :
    RowEvaluation.room layout remaining answer := by
  have admitted : valid layout value := by
    dsimp only [valid, RowEvaluation.room] at *
    omega
  have growth := cache_growth layout default P comparison correct update updateBuffers reserve source value admitted answer reached
  dsimp only [RowEvaluation.room] at reserved ⊢
  omega

end Signatures.Runtime.CaliperBackend.RowFold
