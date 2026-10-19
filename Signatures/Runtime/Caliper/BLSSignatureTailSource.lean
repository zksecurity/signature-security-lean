import Signatures.Runtime.Caliper.BLSSignatureTail

/-! Erasing the entire composed signature tail recovers original evalTerms
and the original private oracle, preserving the updated cache and query order. -/
namespace Signatures.Runtime.CaliperBackend.BLSSignatureTail
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {G : Type}
    [DecidableEq (key.Value base)] [Field (val.Value base)] [SampleableType (val.Value base)]
    (layout : BLSTokens.Layouts w (key.Value base) G (val.Value base))
    (zeroValid : layout.rows.accumulation.cache.value.valid 0)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (mul : Implementation .unit layout.rows.accumulation.arithmetic.pair layout.rows.accumulation.cache.value (fun value => value.1 * value.2))
    (add : Implementation .unit layout.rows.accumulation.arithmetic.pair layout.rows.accumulation.cache.value (fun value => value.1 + value.2))
    (sub : Implementation .unit layout.rows.accumulation.arithmetic.pair layout.rows.accumulation.cache.value (fun value => value.1 - value.2))
    (negate : Implementation .unit layout.rows.accumulation.cache.value layout.rows.accumulation.cache.value Neg.neg)
    (divide : Implementation .unit layout.rows.accumulation.arithmetic.pair layout.rows.accumulation.cache.value (fun value => value.1 / value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots) (subBuffers : sub.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w) (negBuffers : negate.program.code.memBound ≤ slots) (divBuffers : divide.program.code.memBound ≤ slots)

    (source : ProbComp layout.rows.accumulation.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
include uniform in
theorem goodFinish_source (value : GoodReturned layout) (ready : goodFinalReady layout value) :
    Subtype.val <$> goodFinish layout zeroValid P comparison correct add sub divide addBuffers subBuffers reserve divBuffers source value =
      (fun result => ((value.2.val.2.1 + value.2.val.2.2) / (result.1 - value.1.val.1), result.2)) <$>
        ((BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base)) (.inr value.2.val.1)).run value.1.val.2 := by
  unfold goodFinish
  rw [dite_eq_left ready]
  exact BLSFinalTarget.good_privateOracle layout.rows.accumulation P comparison correct sub divide subBuffers reserve divBuffers source uniform _
include uniform in
theorem badFinish_source (value : BadReturned layout) (ready : badFinalReady layout zeroValid value) :
    Subtype.val <$> badFinish layout zeroValid P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers source value =
      (fun result => (-(result.1.2 - value.1.val.1.2) / (result.1.1 - value.1.val.1.1), result.2)) <$>
        ((BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base × val.Value base)) (.inr value.2.val.1)).run value.1.val.2 := by
  unfold badFinish
  rw [dite_eq_left ready]
  exact BLSFinalTarget.bad_privateOracle layout.rows.accumulation P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers source uniform _

noncomputable def goodSource (value : GoodInput layout) : ProbComp (val.Value base × List (key.Value base × val.Value base)) := do
  let evaluated ← (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base))
    (Model.LazyAGM.evalTerms (BLS.LazyAGM.Reduction.traceTerms value.1.val.1.2 value.1.val.1.1.reverse))).run value.1.val.2
  (fun result => ((value.2.val.2.1 + value.2.val.2.2) / (result.1 - evaluated.1), result.2)) <$>
    ((BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base)) (.inr value.2.val.1)).run evaluated.2
noncomputable def badSource (value : BadInput layout) : ProbComp (val.Value base × List (key.Value base × (val.Value base × val.Value base))) := do
  let evaluated ← (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base × val.Value base))
    (Model.LazyAGM.evalTerms (BLS.LazyAGM.Reduction.traceTerms value.1.val.1.2 value.1.val.1.1.reverse))).run value.1.val.2
  (fun result => (-(result.1.2 - evaluated.1.2) / (result.1.1 - evaluated.1.1), result.2)) <$>
    ((BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base × val.Value base)) (.inr value.2.val.1)).run evaluated.2

include uniform in
theorem good_source (value : GoodInput layout) (ready : goodReady layout value) :
    Subtype.val <$> goodDenote layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers source value =
      goodSource layout value := by
  have evaluated := BLSTokens.good_source layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers source uniform value.1
    (good_evaluation_ready layout value ready)
  unfold goodSource
  rw [← evaluated, bind_map_left]
  simp only [goodDenote, goodEvaluation, bind_map_left, map_bind]
  apply bind_congr_of_forall_mem_support
  intro result reached
  have preserved := good_preserves layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve value ready (result, value.2)
    (by simpa only [goodEvaluation, support_map, Set.mem_image] using ⟨result, reached, rfl⟩)
  exact goodFinish_source layout zeroValid P comparison correct add sub divide addBuffers subBuffers reserve divBuffers source uniform (result, value.2) preserved
include uniform in
theorem bad_source (value : BadInput layout) (ready : badReady layout value) :
    Subtype.val <$> badDenote layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers source value =
      badSource layout value := by
  have evaluated := BLSTokens.bad_source layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers source uniform value.1
    (bad_evaluation_ready layout value ready)
  unfold badSource
  rw [← evaluated, bind_map_left]
  simp only [badDenote, badEvaluation, bind_map_left, map_bind]
  apply bind_congr_of_forall_mem_support
  intro result reached
  have preserved := bad_preserves layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve value ready (result, value.2)
    (by simpa only [badEvaluation, support_map, Set.mem_image] using ⟨result, reached, rfl⟩)
  exact badFinish_source layout zeroValid P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers source uniform (result, value.2) preserved
end Signatures.Runtime.CaliperBackend.BLSSignatureTail
