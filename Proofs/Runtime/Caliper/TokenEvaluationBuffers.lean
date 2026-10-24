import Proofs.Runtime.Caliper.TokenEvaluationMemory

/-! Actual buffer-name extent of a complete transcript evaluator. Reused loop
scratch keeps this independent of the number of statically unrolled rows. -/
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
    {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec) (draw : Interactive.Code w)

theorem buffers :
    ((code layout coefficientDefault initial default P comparison correct update updateBuffers reserve port draw).lower port).memBound ≤
      max 11 (max ((draw.lower port).memBound + 3) (slots + 2)) := by
  have prepared := prepare_buffers layout coefficientDefault initial
  have step := RowEvaluation.buffers layout.rows default P comparison correct update updateBuffers reserve port draw
  have folded := InteractiveFold.buffers port (RowEvaluation.code layout.rows default P comparison correct update updateBuffers reserve port draw)
    layout.rows.row.representation.encoding.words layout.rows.state.representation.encoding.words layout.capacity
  change ((RowFold.code layout.rows default P comparison correct update updateBuffers reserve layout.capacity port draw).lower port).memBound ≤ _ at folded
  change max (prepare layout coefficientDefault initial).program.code.memBound
    ((RowFold.code layout.rows default P comparison correct update updateBuffers reserve layout.capacity port draw).lower port).memBound ≤ _
  omega
end Signatures.Runtime.CaliperBackend.TokenEvaluation
