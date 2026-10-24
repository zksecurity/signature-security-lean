import Proofs.Runtime.Caliper.BLSSignatureTailBounds

/-! Stored code for the complete signature tail includes every unrolled
transcript step, both save/restore routines and the final lookup/arithmetic. -/
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

def goodEvaluationWords (scalarWords mulWords addWords : Nat) : Nat :=
  TokenEvaluation.codeBudget layout.good scalarWords (BLSAccumulate.goodCode layout.rows.accumulation.arithmetic mulWords addWords) +
    26 * layout.good.input.representation.encoding.words + 26 * layout.rows.good.state.representation.encoding.words +
    39 * (goodContext layout).representation.encoding.words + 41
def badEvaluationWords (scalarWords mulWords addWords : Nat) : Nat :=
  TokenEvaluation.codeBudget (base := base) (key := key) (val := .pair val val) layout.bad
    (PairSampling.codeBudget layout.rows.accumulation.cache.value layout.rows.accumulation.cache.value scalarWords scalarWords)
    (BLSAccumulate.badCode layout.rows.accumulation.arithmetic mulWords addWords) +
    26 * layout.bad.input.representation.encoding.words + 26 * layout.rows.bad.state.representation.encoding.words +
    39 * (badContext layout).representation.encoding.words + 41
def goodFinishWords (scalarWords addWords subWords divWords : Nat) : Nat :=
  BLSFinalFrame.goodWords layout.rows.accumulation addWords +
    EncodedCacheScalarResult.codeBudget layout.rows.accumulation.good scalarWords
      (BLSExtractArithmetic.goodCode layout.rows.accumulation.arithmetic subWords divWords) + 2
def badFinishWords (scalarWords subWords negWords divWords : Nat) : Nat :=
  CacheTargetFrame.codeBudget layout.rows.accumulation.bad +
    EncodedCacheScalarResult.codeBudget (base := base) (key := key) (val := .pair val val) layout.rows.accumulation.bad
      (PairSampling.codeBudget layout.rows.accumulation.cache.value layout.rows.accumulation.cache.value scalarWords scalarWords)
      (BLSExtractArithmetic.badCode layout.rows.accumulation.arithmetic subWords negWords divWords) + 2
def goodWords (scalarWords mulWords addWords subWords divWords : Nat) : Nat :=
  goodEvaluationWords layout scalarWords mulWords addWords + goodFinishWords layout scalarWords addWords subWords divWords + 1
def badWords (scalarWords mulWords addWords subWords negWords divWords : Nat) : Nat :=
  badEvaluationWords layout scalarWords mulWords addWords + badFinishWords layout scalarWords subWords negWords divWords + 1

variable (port : Interactive.Port w spec) (scalar : Interactive.Code w)
    {scalarWords mulTime mulWords addTime addWords subTime subWords negTime negWords divTime divWords : Nat}
    (scalarWordsBound : (scalar.lower port).descriptionWords ≤ scalarWords)
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
    (subBound : sub.BoundedBy subTime subWords) (negBound : negate.BoundedBy negTime negWords) (divBound : divide.BoundedBy divTime divWords)
include scalarWordsBound mulBound addBound in
omit [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] in
theorem goodEvaluation_words :
    ((goodEvaluationCode layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar).lower port).descriptionWords ≤
      goodEvaluationWords layout scalarWords mulWords addWords := by
  have body := BLSTokens.good_words layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalarWordsBound mulBound addBound
  have copied := Interactive.retain_descriptionWords_le port
    (BLSTokens.goodCode layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalar)
    (Interactive.savedBuffer port (BLSTokens.goodCode layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalar))
    layout.good.input.representation.encoding.words layout.rows.good.state.representation.encoding.words (goodContext layout).representation.encoding.words
  exact copied.trans (by unfold goodEvaluationWords; omega)
include scalarWordsBound mulBound addBound in
omit [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] in
theorem badEvaluation_words :
    ((badEvaluationCode layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar).lower port).descriptionWords ≤
      badEvaluationWords layout scalarWords mulWords addWords := by
  have body := BLSTokens.bad_words layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalarWordsBound mulBound addBound
  have copied := Interactive.retain_descriptionWords_le port
    (BLSTokens.badCode layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalar)
    (Interactive.savedBuffer port (BLSTokens.badCode layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalar))
    layout.bad.input.representation.encoding.words layout.rows.bad.state.representation.encoding.words (badContext layout).representation.encoding.words
  exact copied.trans (by unfold badEvaluationWords; omega)
include scalarWordsBound addBound subBound divBound in
omit [Mul (val.Value base)] [Neg (val.Value base)] in
theorem goodFinish_words :
    ((goodFinishCode layout zeroValid P comparison correct add sub divide addBuffers subBuffers reserve divBuffers port scalar).lower port).descriptionWords ≤
      goodFinishWords layout scalarWords addWords subWords divWords := by
  have frame := (BLSFinalFrame.good_bounded layout.rows.accumulation add addBuffers reserve addBound zeroValid).code_le
  have target := BLSFinalTarget.good_words layout.rows.accumulation P comparison correct sub divide subBuffers reserve divBuffers port scalarWordsBound subBound divBound
  simp only [goodFinishCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold goodFinishWords
  omega
include scalarWordsBound subBound negBound divBound in
omit [Mul (val.Value base)] [Add (val.Value base)] in
theorem badFinish_words :
    ((badFinishCode layout zeroValid P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers port scalar).lower port).descriptionWords ≤
      badFinishWords layout scalarWords subWords negWords divWords := by
  have frame := (BLSFinalFrame.bad_bounded layout.rows.accumulation zeroValid).code_le
  have target := BLSFinalTarget.bad_words layout.rows.accumulation P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers port scalarWordsBound subBound negBound divBound
  simp only [badFinishCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold badFinishWords
  omega
include scalarWordsBound mulBound addBound subBound divBound in
omit [Neg (val.Value base)] in
theorem good_words :
    ((goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar).lower port).descriptionWords ≤
      goodWords layout scalarWords mulWords addWords subWords divWords := by
  have evaluated := goodEvaluation_words layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar scalarWordsBound mulBound addBound
  have finished := goodFinish_words layout zeroValid P comparison correct add sub divide addBuffers subBuffers reserve divBuffers port scalar scalarWordsBound addBound subBound divBound
  simp only [goodCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq]
  unfold goodWords
  omega
include scalarWordsBound mulBound addBound subBound negBound divBound in
theorem bad_words :
    ((badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar).lower port).descriptionWords ≤
      badWords layout scalarWords mulWords addWords subWords negWords divWords := by
  have evaluated := badEvaluation_words layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar scalarWordsBound mulBound addBound
  have finished := badFinish_words layout zeroValid P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers port scalar scalarWordsBound subBound negBound divBound
  simp only [badCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq]
  unfold badWords
  omega
end Signatures.Runtime.CaliperBackend.BLSSignatureTail
