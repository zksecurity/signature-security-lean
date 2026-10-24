import Proofs.Runtime.Caliper.TokenEvaluationSource
import Proofs.Runtime.Caliper.WeightedRowsOracle
import Proofs.Runtime.Caliper.BLSTokensSource

/-! Chronological transcript extraction implements the source evalTerms
computation for any represented module of private answers. Delivered group
points stay in stored tokens but do not enter the scalar accumulation. -/
namespace Signatures.Runtime.CaliperBackend.TokenEvaluation
open Caliper BoundedSource OracleComp OracleSpec Model.LazyAGM
open BLS.LazyAGM.Reduction (privateListOracle)

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {G F : Type}
    [DecidableEq (key.Value base)] [Zero F] [SampleableType (val.Value base)]
    [AddCommMonoid (val.Value base)] [SMul F (val.Value base)]
    (layout : Layouts w (key.Value base) G F (val.Value base))
    (coefficientDefault : layout.rows.accumulation.coefficient.Value)
    (initial default : layout.rows.accumulation.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.rows.accumulation.combine layout.rows.accumulation.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    (combineLaw : ∀ value, combine value = value.2.2 + value.1 • value.2.1)
    (coefficientLaw : coefficientDefault.val = 0)
    (source : ProbComp layout.rows.accumulation.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include combineLaw coefficientLaw uniform in
theorem evalTerms_source (value : layout.input.Value) (admitted : layout.ready value) :
    Subtype.val <$> denote layout coefficientDefault initial default P comparison correct update updateBuffers reserve source value =
      (fun answer => (initial.val + answer.1, answer.2)) <$>
        (simulateQ privateListOracle
          (evalTerms (BLS.LazyAGM.Reduction.traceTerms value.val.1.2 value.val.1.1.reverse))).run value.val.2 := by
  rw [listCache layout coefficientDefault initial default P comparison correct update updateBuffers reserve source value admitted,
    uniform, coefficientLaw]
  rw [← BLSTokens.rows_terms]
  have mapped (rows : List ((key.Value base × G) × F)) (state : val.Value base × List (key.Value base × val.Value base)) :
      rows.foldlM (RowFold.sourceStep (combine := combine) ($ᵗ (val.Value base))) state =
        (rows.map fun row => (row.1.1, row.2)).foldlM
          (WeightedRows.sourceStep (combine := combine) ($ᵗ (val.Value base))) state := by
    rw [List.foldlM_map]
    rfl
  rw [mapped]
  exact WeightedRows.sourceStep_evalTerms combine combineLaw _ _ _

end Signatures.Runtime.CaliperBackend.TokenEvaluation
