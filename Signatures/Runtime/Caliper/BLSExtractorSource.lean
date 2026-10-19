import Signatures.Runtime.Caliper.BLSExtractor
import Signatures.Runtime.Caliper.BLSSignatureTailSource
import Signatures.Runtime.LazyAGMExtraction

/-! The complete encoded extractors recover the original BLS private extraction
programs, including both transcript evaluations, query order and final cache.
The scalar sampler's uniform law is explicit; no whole-extractor equality or
runtime bound is supplied as an assumption. -/
namespace Signatures.Runtime.CaliperBackend.BLSExtractor
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


noncomputable def goodSource (value : GoodInput layout) : ProbComp (val.Value base × List (key.Value base × val.Value base)) := do
  let hashes ← (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base))
    (Model.LazyAGM.evalTerms (BLS.LazyAGM.Reduction.traceTerms value.val.1.2.2.1 value.val.2.2.1.reverse))).run value.val.2.1
  let signatures ← (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base))
    (Model.LazyAGM.evalTerms (BLS.LazyAGM.Reduction.traceTerms value.val.1.2.2.2 value.val.2.2.2.reverse))).run hashes.2
  (fun result => ((value.val.1.2.1 + hashes.1) / (result.1 - signatures.1), result.2)) <$>
    ((BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base)) (.inr value.val.1.1)).run signatures.2
noncomputable def badSource (value : BadInput layout) : ProbComp (val.Value base × List (key.Value base × (val.Value base × val.Value base))) := do
  let signatures ← (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base × val.Value base))
    (Model.LazyAGM.evalTerms (BLS.LazyAGM.Reduction.traceTerms value.val.1.2.2.2 value.val.2.2.2.reverse))).run value.val.2.1
  (fun result => (-(result.1.2 - signatures.1.2) / (result.1.1 - signatures.1.1), result.2)) <$>
    ((BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base × val.Value base)) (.inr value.val.1.1)).run signatures.2

variable (source : ProbComp layout.rows.accumulation.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
include uniform in
theorem good_source (value : GoodInput layout) (ready : goodReady layout value) :
    Subtype.val <$> goodDenote layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers source value =
      goodSource layout value := by
  let prepared := BLSExtractorFrame.prepareValue layout.good value
  have preparedReady := prepare_preserves layout value ready
  have evaluated := BLSTokens.good_source layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers source uniform
    (hashInput layout prepared) (hash_evaluation_ready layout prepared preparedReady)
  change Subtype.val <$> BLSTokens.goodDenote layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers source
    (hashInput layout prepared) =
      (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base))
        (Model.LazyAGM.evalTerms (BLS.LazyAGM.Reduction.traceTerms value.val.1.2.2.1 value.val.2.2.1.reverse))).run value.val.2.1 at evaluated
  unfold goodSource
  rw [← evaluated, bind_map_left]
  simp only [goodDenote, hashDenote, bind_map_left, map_bind]
  apply bind_congr_of_forall_mem_support
  intro result reached
  have preserved := hash_preserves layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve source prepared preparedReady
    (hashValue layout prepared result) (by simpa only [hashDenote, support_map, Set.mem_image] using ⟨result, reached, rfl⟩)
  exact BLSSignatureTail.good_source layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers source uniform
    (BLSExtractorFrame.transitionValue layout (hashValue layout prepared result))
    (BLSExtractorFrame.transitionReady layout _ preserved)
include uniform in
theorem bad_source (value : BadInput layout) (ready : badReady layout value) :
    Subtype.val <$> badDenote layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers source value =
      badSource layout value :=
  BLSSignatureTail.bad_source layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers source uniform
    (BLSExtractorFrame.badValue layout value) (BLSExtractorFrame.badReady layout value ready)

theorem goodSource_original (value : GoodInput layout) : goodSource layout value =
    (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base))
      (LazyAGM.goodFinish ⟨value.val.1.1, value.val.1.2.1, value.val.1.2.2.1, value.val.1.2.2.2⟩
        (LazyAGM.chronological value.val.2.2))).run value.val.2.1 := by
  simp only [goodSource, LazyAGM.goodFinish, LazyAGM.chronological, simulateQ_bind, simulateQ_pure,
    simulateQ_spec_query, StateT.run_bind, StateT.run_pure]
  simp only [bind_pure_comp]
  rfl
theorem badSource_original (value : BadInput layout) : badSource layout value =
    (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base × val.Value base))
      (LazyAGM.badFinish ⟨value.val.1.1, value.val.1.2.1, value.val.1.2.2.1, value.val.1.2.2.2⟩
        (LazyAGM.chronological value.val.2.2))).run value.val.2.1 := by
  simp only [badSource, LazyAGM.badFinish, LazyAGM.chronological, simulateQ_bind, simulateQ_pure,
    simulateQ_spec_query, StateT.run_bind, StateT.run_pure]
  simp only [bind_pure_comp]
  rfl

include uniform in
theorem good_original (value : GoodInput layout) (ready : goodReady layout value) :
    Subtype.val <$> goodDenote layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers source value =
      (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base))
        (LazyAGM.goodFinish ⟨value.val.1.1, value.val.1.2.1, value.val.1.2.2.1, value.val.1.2.2.2⟩
          (LazyAGM.chronological value.val.2.2))).run value.val.2.1 :=
  (good_source layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers source uniform value ready).trans
    (goodSource_original layout value)
include uniform in
theorem bad_original (value : BadInput layout) (ready : badReady layout value) :
    Subtype.val <$> badDenote layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers source value =
      (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base × val.Value base))
        (LazyAGM.badFinish ⟨value.val.1.1, value.val.1.2.1, value.val.1.2.2.1, value.val.1.2.2.2⟩
          (LazyAGM.chronological value.val.2.2))).run value.val.2.1 :=
  (bad_source layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers source uniform value ready).trans
    (badSource_original layout value)
end Signatures.Runtime.CaliperBackend.BLSExtractor
