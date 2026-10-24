import Proofs.Runtime.Caliper.BLSTokens

/-! The complete transcript evaluators have the original private-oracle fold,
starting from zero and retaining the final cache. Their rows come from executed
preparation, rather than a supplied already-prepared list. -/
namespace Signatures.Runtime.CaliperBackend.BLSTokens
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {G : Type}
    [DecidableEq (key.Value base)] [Zero (val.Value base)] [Mul (val.Value base)] [Add (val.Value base)]
    (layout : Layouts w (key.Value base) G (val.Value base))
    (zeroValid : layout.rows.accumulation.cache.value.valid 0)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (mul : Implementation .unit layout.rows.accumulation.arithmetic.pair layout.rows.accumulation.cache.value (fun value => value.1 * value.2))
    (add : Implementation .unit layout.rows.accumulation.arithmetic.pair layout.rows.accumulation.cache.value (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)
    (addBuffers : add.program.code.memBound ≤ slots)
    [SampleableType (val.Value base)] (source : ProbComp layout.rows.accumulation.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include uniform in
theorem good_privateOracle (value : layout.good.input.Value) (ready : layout.good.ready value) :
    Subtype.val <$> goodDenote layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers source value =
      ((value.val.1.1.reverse.mapIdx (fun n token => (token, (value.val.1.2[n]?).getD 0))).foldlM
        (fun (acc : val.Value base) (row : (key.Value base × G) × val.Value base) => do
          let answer ← (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base)) (.inr row.1.1)
          pure (acc + row.2 * answer)) 0).run value.val.2 := by
  have prepared := TokenEvaluation.foldValue_ready (base := base) (key := key) (val := val) layout.good
    (zero layout zeroValid) (zero layout zeroValid) value ready
  have folded := BLSRows.good_privateOracle layout.rows (zero layout zeroValid) P comparison correct mul add mulBuffers reserve addBuffers
    source uniform (TokenEvaluation.foldValue layout.good (zero layout zeroValid) (zero layout zeroValid) value) prepared
  refine folded.trans ?_
  exact congrArg (fun rows : List ((key.Value base × G) × val.Value base) =>
    (rows.foldlM (fun (acc : val.Value base) (row : (key.Value base × G) × val.Value base) => do
      let answer ← (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base)) (.inr row.1.1)
      pure (acc + row.2 * answer)) 0).run value.val.2)
    (TokenEvaluation.foldValue_rows layout.good (zero layout zeroValid) (zero layout zeroValid) value)

include uniform in
theorem bad_privateOracle (value : layout.bad.input.Value) (ready : layout.bad.ready value) :
    Subtype.val <$> badDenote layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers source value =
      ((value.val.1.1.reverse.mapIdx (fun n token => (token, (value.val.1.2[n]?).getD 0))).foldlM
        (fun (acc : val.Value base × val.Value base) (row : (key.Value base × G) × val.Value base) => do
          let answer ← (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base × val.Value base)) (.inr row.1.1)
          pure (acc.1 + row.2 * answer.1, acc.2 + row.2 * answer.2)) (0, 0)).run value.val.2 := by
  have prepared := TokenEvaluation.foldValue_ready (base := base) (key := key) (val := .pair val val) layout.bad
    (zero layout zeroValid) (pairZero layout zeroValid) value ready
  have folded := BLSRows.bad_privateOracle layout.rows (zero layout zeroValid) P comparison correct mul add mulBuffers reserve addBuffers
    source uniform (TokenEvaluation.foldValue layout.bad (zero layout zeroValid) (pairZero layout zeroValid) value) prepared
  refine folded.trans ?_
  exact congrArg (fun rows : List ((key.Value base × G) × val.Value base) =>
    (rows.foldlM (fun (acc : val.Value base × val.Value base) (row : (key.Value base × G) × val.Value base) => do
      let answer ← (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base × val.Value base)) (.inr row.1.1)
      pure (acc.1 + row.2 * answer.1, acc.2 + row.2 * answer.2)) (0, 0)).run value.val.2)
    (TokenEvaluation.foldValue_rows layout.bad (zero layout zeroValid) (pairZero layout zeroValid) value)
end Signatures.Runtime.CaliperBackend.BLSTokens
