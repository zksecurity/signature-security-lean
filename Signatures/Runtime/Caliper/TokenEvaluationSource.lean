import Signatures.Runtime.Caliper.TokenEvaluation
import Signatures.Runtime.Caliper.RowFoldStateSource

/-! Erasing the combined evaluator gives the original ordered stateful fold.
Its postcondition reserves space using actual token count, including tokens
whose missing coefficient is zero. Preparation leaves the cache unchanged. -/
namespace Signatures.Runtime.CaliperBackend.TokenEvaluation
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {G F : Type}
    [DecidableEq (key.Value base)] (layout : Layouts w (key.Value base) G F (val.Value base))
    (coefficientDefault : layout.rows.accumulation.coefficient.Value)
    (initial default : layout.rows.accumulation.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.rows.accumulation.combine layout.rows.accumulation.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    {I : Type} {spec : OracleSpec I}
    (source : OracleComp spec layout.rows.accumulation.cache.value.Value)

theorem listCache (value : layout.input.Value) (ready : layout.ready value) :
    Subtype.val <$> denote layout coefficientDefault initial default P comparison correct update updateBuffers reserve source value =
      (value.val.1.1.reverse.mapIdx (fun n token => (token, (value.val.1.2[n]?).getD coefficientDefault.val))).foldlM
        (RowFold.sourceStep (combine := combine) (Subtype.val <$> source)) (initial.val, value.val.2) := by
  have folded := RowFold.listCache layout.rows default P comparison correct update updateBuffers reserve source
    (foldValue layout coefficientDefault initial value) (foldValue_ready layout coefficientDefault initial value ready)
  rw [foldValue_rows] at folded
  exact folded

theorem stateFold (value : layout.input.Value) (ready : layout.ready value) :
    Subtype.val <$> denote layout coefficientDefault initial default P comparison correct update updateBuffers reserve source value =
      ((value.val.1.1.reverse.mapIdx (fun n token => (token, (value.val.1.2[n]?).getD coefficientDefault.val))).foldlM
        (fun (acc : val.Value base) (row : (key.Value base × G) × F) => do
          let answer ← QueryImpl.ListCache.handler (fun _ => Subtype.val <$> source) row.1.1
          pure (combine (row.2, answer, acc))) initial.val).run value.val.2 := by
  rw [listCache, RowFold.sourceStep_fold]
  exact ready

theorem cache_growth (value : layout.input.Value) (ready : layout.ready value) (answer : layout.rows.state.Value)
    (reached : answer ∈ support (denote layout coefficientDefault initial default P comparison correct update updateBuffers reserve source value)) :
    answer.val.2.length ≤ value.val.2.length + value.val.1.1.length := by
  have growth := RowFold.cache_growth layout.rows default P comparison correct update updateBuffers reserve source
    (foldValue layout coefficientDefault initial value) (foldValue_ready layout coefficientDefault initial value ready) answer reached
  rw [foldValue_length] at growth
  exact growth

theorem remaining_room (value : layout.input.Value) (remaining : Nat)
    (reserved : value.val.2.length + value.val.1.1.length + remaining ≤ layout.rows.accumulation.cache.capacityPred + 1)
    (answer : layout.rows.state.Value)
    (reached : answer ∈ support (denote layout coefficientDefault initial default P comparison correct update updateBuffers reserve source value)) :
    RowEvaluation.room layout.rows remaining answer := by
  have ready : layout.ready value := by unfold Layouts.ready; omega
  have growth := cache_growth layout coefficientDefault initial default P comparison correct update updateBuffers reserve source value ready answer reached
  unfold RowEvaluation.room
  omega
end Signatures.Runtime.CaliperBackend.TokenEvaluation
