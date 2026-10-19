import Signatures.Runtime.Caliper.BLSSignatureTailFinish

/-! Signature-transcript evaluation, physically retained forgery context and
final extraction form one executed program. A proved decreasing reservation
connects their finite-cache domains. -/
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
def goodEvaluationCode (port : Interactive.Port w spec) (scalar : Interactive.Code w) : Interactive.Code w :=
  let body := BLSTokens.goodCode layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalar
  Interactive.retain body (Interactive.savedBuffer port body) layout.good.input.representation.encoding.words
    layout.rows.good.state.representation.encoding.words (goodContext layout).representation.encoding.words
def badEvaluationCode (port : Interactive.Port w spec) (scalar : Interactive.Code w) : Interactive.Code w :=
  let body := BLSTokens.badCode layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalar
  Interactive.retain body (Interactive.savedBuffer port body) layout.bad.input.representation.encoding.words
    layout.rows.bad.state.representation.encoding.words (badContext layout).representation.encoding.words
def goodEvaluation (source : OracleComp spec layout.rows.accumulation.cache.value.Value) (value : GoodInput layout) : OracleComp spec (GoodReturned layout) :=
  (fun answer => (answer, value.2)) <$> BLSTokens.goodDenote layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers source value.1
def badEvaluation (source : OracleComp spec layout.rows.accumulation.cache.value.Value) (value : BadInput layout) : OracleComp spec (BadReturned layout) :=
  (fun answer => (answer, value.2)) <$> BLSTokens.badDenote layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers source value.1

def goodCode (port : Interactive.Port w spec) (scalar : Interactive.Code w) : Interactive.Code w :=
  .seq (goodEvaluationCode layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar)
    (goodFinishCode layout zeroValid P comparison correct add sub divide addBuffers subBuffers reserve divBuffers port scalar)
def badCode (port : Interactive.Port w spec) (scalar : Interactive.Code w) : Interactive.Code w :=
  .seq (badEvaluationCode layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar)
    (badFinishCode layout zeroValid P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers port scalar)
def goodDenote (source : OracleComp spec layout.rows.accumulation.cache.value.Value) (value : GoodInput layout) :
    OracleComp spec (CacheScalarResult.output layout.rows.accumulation.good).Value :=
  goodEvaluation layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve source value >>=
    goodFinish layout zeroValid P comparison correct add sub divide addBuffers subBuffers reserve divBuffers source
def badDenote (source : OracleComp spec layout.rows.accumulation.cache.value.Value) (value : BadInput layout) :
    OracleComp spec (CacheScalarResult.output layout.rows.accumulation.bad).Value :=
  badEvaluation layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve source value >>=
    badFinish layout zeroValid P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers source

variable {source : OracleComp spec layout.rows.accumulation.cache.value.Value}
omit [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] in
theorem good_preserves (value : GoodInput layout) (ready : goodReady layout value) (answer : GoodReturned layout)
    (reached : answer ∈ support (goodEvaluation layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve source value)) :
    goodFinalReady layout answer := by
  simp only [goodEvaluation, support_map, Set.mem_image] at reached
  obtain ⟨result, supported, rfl⟩ := reached
  have room := TokenEvaluation.remaining_room layout.good (BLSTokens.zero layout zeroValid) (BLSTokens.zero layout zeroValid)
    (BLSTokens.zero layout zeroValid) P comparison correct
    (BLSPrivateAccumulate.goodUpdate layout.rows.accumulation mul add mulBuffers reserve)
    (BLSPrivateAccumulate.goodUpdate_buffers layout.rows.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.good_reserve layout.rows.accumulation reserve) source value.1 1 ready result supported
  apply BLSFinalFrame.admissible_of_room layout.rows.accumulation (goodView layout (result, value.2))
  change result.val.2.length ≤ _
  change result.val.2.length + 1 ≤ layout.rows.accumulation.cache.capacityPred + 1 at room
  omega
omit [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] in
theorem bad_preserves (value : BadInput layout) (ready : badReady layout value) (answer : BadReturned layout)
    (reached : answer ∈ support (badEvaluation layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve source value)) :
    badFinalReady layout zeroValid answer := by
  simp only [badEvaluation, support_map, Set.mem_image] at reached
  obtain ⟨result, supported, rfl⟩ := reached
  have room := TokenEvaluation.remaining_room (base := base) (key := key) (val := .pair val val) layout.bad
    (BLSTokens.zero layout zeroValid) (BLSTokens.pairZero layout zeroValid) (BLSTokens.pairZero layout zeroValid) P comparison correct
    (BLSPrivateAccumulate.badUpdate layout.rows.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.badUpdate_buffers layout.rows.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.bad_reserve layout.rows.accumulation reserve)
    (BLSPrivateAccumulate.pairSource layout.rows.accumulation source) value.1 1 ready result supported
  apply CacheTargetFrame.admissible_of_room layout.rows.accumulation.bad _ (badView layout (result, value.2))
  change result.val.2.length ≤ _
  change result.val.2.length + 1 ≤ layout.rows.accumulation.bad.cache.capacityPred + 1 at room
  omega

variable (port : Interactive.Port w spec) {scalar : Interactive.Code w}
    (scalarCorrect : Interactive.Refines port .unit layout.rows.accumulation.cache.lookup.unit.representation
      layout.rows.accumulation.cache.value.representation (fun _ => source) scalar)
include scalarCorrect in
omit [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] in
theorem goodEvaluation_refines
    (fits : layout.good.input.representation.encoding.words + (goodContext layout).representation.encoding.words < 2 ^ w) :
    Interactive.RefinesOn (goodReady layout) port .unit (goodInput layout fits) (goodReturned layout)
      (goodEvaluation layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve source)
      (goodEvaluationCode layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar) := by
  have retained := (BLSTokens.good_refines layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalarCorrect).retain
    (by decide) (goodContext layout).representation layout.rows.accumulation.cache.wordFits fits (goodOutputFits layout)
  exact fun tape value ready before holds => retained tape value (good_evaluation_ready layout value ready) before holds
include scalarCorrect in
omit [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] in
theorem badEvaluation_refines
    (fits : layout.bad.input.representation.encoding.words + (badContext layout).representation.encoding.words < 2 ^ w) :
    Interactive.RefinesOn (badReady layout) port .unit (badInput layout fits) (badReturned layout)
      (badEvaluation layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve source)
      (badEvaluationCode layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar) := by
  have retained := (BLSTokens.bad_refines layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalarCorrect).retain
    (by decide) (badContext layout).representation layout.rows.accumulation.cache.wordFits fits (badOutputFits layout)
  exact fun tape value ready before holds => retained tape value (bad_evaluation_ready layout value ready) before holds
include scalarCorrect in
omit [Neg (val.Value base)] in
theorem good_refines
    (fits : layout.good.input.representation.encoding.words + (goodContext layout).representation.encoding.words < 2 ^ w) :
    Interactive.RefinesOn (goodReady layout) port .unit (goodInput layout fits)
      (CacheScalarResult.output layout.rows.accumulation.good).representation
      (goodDenote layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers source)
      (goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar) :=
  (goodEvaluation_refines layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalarCorrect fits).seq
    (goodFinish_refines layout zeroValid P comparison correct add sub divide addBuffers subBuffers reserve divBuffers port scalarCorrect)
    (good_preserves layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve)
include scalarCorrect in
theorem bad_refines
    (fits : layout.bad.input.representation.encoding.words + (badContext layout).representation.encoding.words < 2 ^ w) :
    Interactive.RefinesOn (badReady layout) port .unit (badInput layout fits)
      (CacheScalarResult.output layout.rows.accumulation.bad).representation
      (badDenote layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers source)
      (badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar) :=
  (badEvaluation_refines layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalarCorrect fits).seq
    (badFinish_refines layout zeroValid P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers port scalarCorrect)
    (bad_preserves layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve)
end Signatures.Runtime.CaliperBackend.BLSSignatureTail
