import Proofs.Runtime.Caliper.BLSSignatureTailWords

/-! Generated names throughout the signature tail are accounted from the
scalar routines, sampler and stored code, including the retained forgery frame. -/
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

variable {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec) (scalar : Interactive.Code w)
    {drawNames names : Nat} (drawBound : WordIO.NamesBound (scalar.lower port) drawNames)
    (mulNames : NamesAccounted mul.program.code names) (addNames : NamesAccounted add.program.code names)
    (subNames : NamesAccounted sub.program.code names) (negNames : NamesAccounted negate.program.code names)
    (divNames : NamesAccounted divide.program.code names)
def nameBudget (drawNames names : Nat) : Nat := max (max 5 (PairSampling.slots drawNames drawNames)) names
include drawBound mulNames addNames in
omit [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] in
theorem goodEvaluation_names :
    WordIO.NamesAccounted ((goodEvaluationCode layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar).lower port)
      (nameBudget drawNames names) := by
  have arithmetic := BLSAccumulate.good_names layout.rows.accumulation.arithmetic names mul add mulNames addNames mulBuffers reserve
  have evaluated := TokenEvaluation.names layout.good (BLSTokens.zero layout zeroValid) (BLSTokens.zero layout zeroValid) (BLSTokens.zero layout zeroValid)
    P comparison correct (BLSPrivateAccumulate.goodUpdate layout.rows.accumulation mul add mulBuffers reserve)
    (BLSPrivateAccumulate.goodUpdate_buffers layout.rows.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.good_reserve layout.rows.accumulation reserve) port scalar drawBound arithmetic
  exact (Interactive.retain_names port evaluated layout.good.input.representation.encoding.words
    layout.rows.good.state.representation.encoding.words (goodContext layout).representation.encoding.words).mono
      (by simp only [nameBudget, PairSampling.slots]; omega)
include drawBound mulNames addNames in
omit [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] in
theorem badEvaluation_names :
    WordIO.NamesAccounted ((badEvaluationCode layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar).lower port)
      (nameBudget drawNames names) := by
  have arithmetic := BLSAccumulate.bad_names layout.rows.accumulation.arithmetic names mul add mulNames addNames mulBuffers reserve addBuffers
  have paired := PairSampling.names layout.rows.accumulation.cache.value layout.rows.accumulation.cache.value
    layout.rows.accumulation.cache.wordFits layout.rows.accumulation.cache.pairValueFits port scalar scalar drawBound drawBound
  have evaluated := TokenEvaluation.names (base := base) (key := key) (val := .pair val val) layout.bad
    (BLSTokens.zero layout zeroValid) (BLSTokens.pairZero layout zeroValid) (BLSTokens.pairZero layout zeroValid)
    P comparison correct (BLSPrivateAccumulate.badUpdate layout.rows.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.badUpdate_buffers layout.rows.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.bad_reserve layout.rows.accumulation reserve) port
    (BLSPrivateAccumulate.pairSampler layout.rows.accumulation port scalar) paired arithmetic
  exact Interactive.retain_names port evaluated layout.bad.input.representation.encoding.words
    layout.rows.bad.state.representation.encoding.words (badContext layout).representation.encoding.words
include drawBound addNames subNames divNames in
omit [Mul (val.Value base)] [Neg (val.Value base)] in
theorem goodFinish_names :
    WordIO.NamesAccounted ((goodFinishCode layout zeroValid P comparison correct add sub divide addBuffers subBuffers reserve divBuffers port scalar).lower port)
      (nameBudget drawNames names) := by
  have frame := (BLSFinalFrame.good_names layout.rows.accumulation names add addNames addBuffers reserve zeroValid).mono (Nat.le_max_right (max 5 (PairSampling.slots drawNames drawNames)) names)
  have arithmetic := BLSExtractArithmetic.good_names layout.rows.accumulation.arithmetic names sub subNames subBuffers
    (Nat.lt_of_le_of_lt (Nat.add_le_add_left (by decide : 2 ≤ 4) slots) reserve) divide divNames
  have target := EncodedCacheScalarResult.names layout.rows.accumulation.good P comparison correct
    (BLSFinalTarget.goodUpdate layout.rows.accumulation sub divide subBuffers reserve)
    (BLSFinalTarget.goodUpdate_buffers layout.rows.accumulation sub divide subBuffers reserve divBuffers)
    (BLSFinalTarget.good_reserve layout.rows.accumulation reserve) port scalar drawBound arithmetic
  exact (WordIO.NamesAccounted.compute frame).seq (target.mono (by simp only [PairSampling.slots]; omega))
include drawBound subNames negNames divNames in
omit [Mul (val.Value base)] [Add (val.Value base)] in
theorem badFinish_names :
    WordIO.NamesAccounted ((badFinishCode layout zeroValid P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers port scalar).lower port)
      (nameBudget drawNames names) := by
  have frame := BLSFinalFrame.bad_names layout.rows.accumulation (nameBudget drawNames names) zeroValid
  have arithmetic := BLSExtractArithmetic.bad_names layout.rows.accumulation.arithmetic names sub subNames subBuffers
    (Nat.lt_of_le_of_lt (Nat.add_le_add_left (by decide : 2 ≤ 4) slots) reserve) negate negNames negBuffers divide divNames
  have paired := PairSampling.names layout.rows.accumulation.cache.value layout.rows.accumulation.cache.value
    layout.rows.accumulation.cache.wordFits layout.rows.accumulation.cache.pairValueFits port scalar scalar drawBound drawBound
  have target := EncodedCacheScalarResult.names (base := base) (key := key) (val := .pair val val) layout.rows.accumulation.bad P comparison correct
    (BLSFinalTarget.badUpdate layout.rows.accumulation sub negate divide subBuffers reserve negBuffers)
    (BLSFinalTarget.badUpdate_buffers layout.rows.accumulation sub negate divide subBuffers reserve negBuffers divBuffers)
    (BLSFinalTarget.bad_reserve layout.rows.accumulation reserve) port
    (BLSPrivateAccumulate.pairSampler layout.rows.accumulation port scalar) paired arithmetic
  exact (WordIO.NamesAccounted.compute frame).seq target
include drawBound mulNames addNames subNames divNames in
omit [Neg (val.Value base)] in
theorem good_names :
    WordIO.NamesAccounted ((goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar).lower port)
      (nameBudget drawNames names) :=
  (goodEvaluation_names layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar drawBound mulNames addNames).seq
    (goodFinish_names layout zeroValid P comparison correct add sub divide addBuffers subBuffers reserve divBuffers port scalar drawBound addNames subNames divNames)
include drawBound mulNames addNames subNames negNames divNames in
theorem bad_names :
    WordIO.NamesAccounted ((badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar).lower port)
      (nameBudget drawNames names) :=
  (badEvaluation_names layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar drawBound mulNames addNames).seq
    (badFinish_names layout zeroValid P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers port scalar drawBound subNames negNames divNames)
end Signatures.Runtime.CaliperBackend.BLSSignatureTail
