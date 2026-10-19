import Signatures.Runtime.Caliper.BLSSignatureTail

/-! Complete runtime of the signature-evaluation tail, including physical
save/restore, final request packing, numerator addition and target extraction. -/
namespace Signatures.Runtime.CaliperBackend.BLSSignatureTail
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {G : Type}
    [DecidableEq (key.Value base)] [Zero (val.Value base)] [Mul (val.Value base)] [Add (val.Value base)]
    [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)]
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

variable {I : Type} {spec : OracleSpec I}

def goodEvaluationTime (scalarTime mulTime addTime : Nat) : Nat :=
  TokenEvaluation.timeBudget layout.good scalarTime (BLSAccumulate.goodTime layout.rows.accumulation.arithmetic mulTime addTime) +
    8 * layout.good.input.representation.encoding.words + 8 * layout.rows.good.state.representation.encoding.words +
    12 * (goodContext layout).representation.encoding.words
def badEvaluationTime (scalarTime mulTime addTime : Nat) : Nat :=
  TokenEvaluation.timeBudget (base := base) (key := key) (val := .pair val val) layout.bad
    (PairSampling.timeBudget layout.rows.accumulation.cache.value layout.rows.accumulation.cache.value scalarTime scalarTime)
    (BLSAccumulate.badTime layout.rows.accumulation.arithmetic mulTime addTime) +
    8 * layout.bad.input.representation.encoding.words + 8 * layout.rows.bad.state.representation.encoding.words +
    12 * (badContext layout).representation.encoding.words
def goodFinishTime (scalarTime addTime subTime divTime : Nat) : Nat :=
  BLSFinalFrame.goodTime layout.rows.accumulation addTime +
    EncodedCacheScalarResult.timeBudget layout.rows.accumulation.good scalarTime
      (BLSExtractArithmetic.goodTime layout.rows.accumulation.arithmetic subTime divTime)
def badFinishTime (scalarTime subTime negTime divTime : Nat) : Nat :=
  CacheTargetFrame.timeBudget layout.rows.accumulation.bad +
    EncodedCacheScalarResult.timeBudget (base := base) (key := key) (val := .pair val val) layout.rows.accumulation.bad
      (PairSampling.timeBudget layout.rows.accumulation.cache.value layout.rows.accumulation.cache.value scalarTime scalarTime)
      (BLSExtractArithmetic.badTime layout.rows.accumulation.arithmetic subTime negTime divTime)
def goodTime (scalarTime mulTime addTime subTime divTime : Nat) : Nat :=
  goodEvaluationTime layout scalarTime mulTime addTime + goodFinishTime layout scalarTime addTime subTime divTime
def badTime (scalarTime mulTime addTime subTime negTime divTime : Nat) : Nat :=
  badEvaluationTime layout scalarTime mulTime addTime + badFinishTime layout scalarTime subTime negTime divTime

variable (port : Interactive.Port w spec) {source : OracleComp spec layout.rows.accumulation.cache.value.Value} {scalar : Interactive.Code w}
    (scalarCorrect : Interactive.Refines port .unit layout.rows.accumulation.cache.lookup.unit.representation
      layout.rows.accumulation.cache.value.representation (fun _ => source) scalar)
    {scalarTime mulTime mulWords addTime addWords subTime subWords negTime negWords divTime divWords : Nat}
    (scalarTimeBound : Interactive.TimeBound port .unit layout.rows.accumulation.cache.lookup.unit.representation scalar scalarTime)
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
    (subBound : sub.BoundedBy subTime subWords) (negBound : negate.BoundedBy negTime negWords) (divBound : divide.BoundedBy divTime divWords)
include scalarCorrect scalarTimeBound mulBound addBound in
omit [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] in
theorem goodEvaluation_time
    (fits : layout.good.input.representation.encoding.words + (goodContext layout).representation.encoding.words < 2 ^ w) :
    Interactive.TimeBoundOn (goodReady layout) port .unit (goodInput layout fits)
      (goodEvaluationCode layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar)
      (goodEvaluationTime layout scalarTime mulTime addTime) := by
  have refined := BLSTokens.good_refines layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalarCorrect
  have bounded := BLSTokens.good_time layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalarCorrect scalarTimeBound mulBound addBound
  have retained := (bounded.retain refined (by decide) (goodContext layout).representation layout.rows.accumulation.cache.wordFits fits).mono
    (Interactive.retain_time_unit_le _ _ _ _ _)
  exact fun tape value ready before holds finished reached => retained tape value (good_evaluation_ready layout value ready) before holds finished reached
include scalarCorrect scalarTimeBound mulBound addBound in
omit [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] in
theorem badEvaluation_time
    (fits : layout.bad.input.representation.encoding.words + (badContext layout).representation.encoding.words < 2 ^ w) :
    Interactive.TimeBoundOn (badReady layout) port .unit (badInput layout fits)
      (badEvaluationCode layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar)
      (badEvaluationTime layout scalarTime mulTime addTime) := by
  have refined := BLSTokens.bad_refines layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalarCorrect
  have bounded := BLSTokens.bad_time layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalarCorrect scalarTimeBound mulBound addBound
  have retained := (bounded.retain refined (by decide) (badContext layout).representation layout.rows.accumulation.cache.wordFits fits).mono
    (Interactive.retain_time_unit_le _ _ _ _ _)
  exact fun tape value ready before holds finished reached => retained tape value (bad_evaluation_ready layout value ready) before holds finished reached
include scalarCorrect scalarTimeBound addBound subBound divBound in
omit [Mul (val.Value base)] [Neg (val.Value base)] in
theorem goodFinish_time : Interactive.TimeBoundOn (goodFinalReady layout) port .unit (goodReturned layout)
    (goodFinishCode layout zeroValid P comparison correct add sub divide addBuffers subBuffers reserve divBuffers port scalar)
    (goodFinishTime layout scalarTime addTime subTime divTime) := by
  have refined := Interactive.Refines.compute port .unit (goodPrepare layout zeroValid add addBuffers reserve)
  have bounded := Interactive.TimeBound.compute (port := port) (cost := .unit) (goodPrepare layout zeroValid add addBuffers reserve)
    (BLSFinalFrame.goodTime layout.rows.accumulation addTime)
    (fun value => (BLSFinalFrame.good_bounded layout.rows.accumulation add addBuffers reserve addBound zeroValid).time_le (goodAdmitted layout value))
  have target := BLSFinalTarget.good_time layout.rows.accumulation P comparison correct sub divide subBuffers reserve divBuffers port scalarCorrect scalarTimeBound subBound divBound
  have composed := bounded.seq refined target
  exact fun tape value ready before holds finished reached => composed tape ⟨value, ready⟩ before holds finished reached
include scalarCorrect scalarTimeBound subBound negBound divBound in
omit [Mul (val.Value base)] [Add (val.Value base)] in
theorem badFinish_time : Interactive.TimeBoundOn (badFinalReady layout zeroValid) port .unit (badReturned layout)
    (badFinishCode layout zeroValid P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers port scalar)
    (badFinishTime layout scalarTime subTime negTime divTime) := by
  have refined := Interactive.Refines.compute port .unit (badPrepare layout zeroValid)
  have bounded := Interactive.TimeBound.compute (port := port) (cost := .unit) (badPrepare layout zeroValid)
    (CacheTargetFrame.timeBudget layout.rows.accumulation.bad)
    (fun value => (BLSFinalFrame.bad_bounded layout.rows.accumulation zeroValid).time_le (badAdmitted layout zeroValid value))
  have target := BLSFinalTarget.bad_time layout.rows.accumulation P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers port scalarCorrect scalarTimeBound subBound negBound divBound
  have composed := bounded.seq refined target
  exact fun tape value ready before holds finished reached => composed tape ⟨value, ready⟩ before holds finished reached
include scalarCorrect scalarTimeBound mulBound addBound subBound divBound in
omit [Neg (val.Value base)] in
theorem good_time
    (fits : layout.good.input.representation.encoding.words + (goodContext layout).representation.encoding.words < 2 ^ w) :
    Interactive.TimeBoundOn (goodReady layout) port .unit (goodInput layout fits)
      (goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar)
      (goodTime layout scalarTime mulTime addTime subTime divTime) :=
  (goodEvaluation_time layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalarCorrect scalarTimeBound mulBound addBound fits).seq
    (goodEvaluation_refines layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalarCorrect fits)
    (goodFinish_time layout zeroValid P comparison correct add sub divide addBuffers subBuffers reserve divBuffers port scalarCorrect scalarTimeBound addBound subBound divBound)
    (good_preserves layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve)
include scalarCorrect scalarTimeBound mulBound addBound subBound negBound divBound in
theorem bad_time
    (fits : layout.bad.input.representation.encoding.words + (badContext layout).representation.encoding.words < 2 ^ w) :
    Interactive.TimeBoundOn (badReady layout) port .unit (badInput layout fits)
      (badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar)
      (badTime layout scalarTime mulTime addTime subTime negTime divTime) :=
  (badEvaluation_time layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalarCorrect scalarTimeBound mulBound addBound fits).seq
    (badEvaluation_refines layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalarCorrect fits)
    (badFinish_time layout zeroValid P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers port scalarCorrect scalarTimeBound subBound negBound divBound)
    (bad_preserves layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve)
end Signatures.Runtime.CaliperBackend.BLSSignatureTail
