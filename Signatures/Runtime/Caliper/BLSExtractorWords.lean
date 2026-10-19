import Signatures.Runtime.Caliper.BLSExtractorBounds

/-! Complete extractor code bounds include both transcript passes, every
unrolled row, all physical context copies, and composition instructions. -/
namespace Signatures.Runtime.CaliperBackend.BLSExtractor
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
def hashWords (scalarWords mulWords addWords : Nat) : Nat :=
  TokenEvaluation.codeBudget layout.good scalarWords (BLSAccumulate.goodCode layout.rows.accumulation.arithmetic mulWords addWords) +
    26 * layout.good.input.representation.encoding.words + 26 * layout.rows.good.state.representation.encoding.words +
    39 * (BLSExtractorFrame.context layout.good).representation.encoding.words + 41
def afterHashWords (scalarWords mulWords addWords subWords divWords : Nat) : Nat :=
  26 * (BLSSignatureTail.goodInput layout (BLSExtractorFrame.goodTailFits layout)).encoding.words + 14 +
    BLSSignatureTail.goodWords layout scalarWords mulWords addWords subWords divWords + 2
def goodWords (scalarWords mulWords addWords subWords divWords : Nat) : Nat :=
  26 * (BLSExtractorFrame.prepared layout.good).representation.encoding.words + 14 +
    hashWords layout scalarWords mulWords addWords + afterHashWords layout scalarWords mulWords addWords subWords divWords + 3
def badWords (scalarWords mulWords addWords subWords negWords divWords : Nat) : Nat :=
  26 * (BLSExtractorFrame.signatureInput layout.bad).representation.encoding.words + 14 +
    BLSSignatureTail.badWords layout scalarWords mulWords addWords subWords negWords divWords + 2

variable (port : Interactive.Port w spec) (scalar : Interactive.Code w)
    {scalarWords mulTime mulWords addTime addWords subTime subWords negTime negWords divTime divWords : Nat}
    (scalarWordsBound : (scalar.lower port).descriptionWords ≤ scalarWords)
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
    (subBound : sub.BoundedBy subTime subWords) (negBound : negate.BoundedBy negTime negWords) (divBound : divide.BoundedBy divTime divWords)
include scalarWordsBound mulBound addBound in
omit [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] in
theorem hash_words :
    ((hashCode layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar).lower port).descriptionWords ≤
      hashWords layout scalarWords mulWords addWords := by
  have body := BLSTokens.good_words layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalarWordsBound mulBound addBound
  have copied := Interactive.retain_descriptionWords_le port
    (BLSTokens.goodCode layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalar)
    (Interactive.savedBuffer port (BLSTokens.goodCode layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalar))
    layout.good.input.representation.encoding.words layout.rows.good.state.representation.encoding.words
    (BLSExtractorFrame.context layout.good).representation.encoding.words
  exact copied.trans (by unfold hashWords; omega)
include scalarWordsBound mulBound addBound subBound divBound in
omit [Neg (val.Value base)] in
theorem afterHash_words :
    ((afterHashCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar).lower port).descriptionWords ≤
      afterHashWords layout scalarWords mulWords addWords subWords divWords := by
  have prepared := BLSExtractorFrame.transition_words layout
  have tail := BLSSignatureTail.good_words layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers
    port scalar scalarWordsBound mulBound addBound subBound divBound
  simp only [afterHashCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold afterHashWords
  omega
include scalarWordsBound mulBound addBound subBound divBound in
omit [Neg (val.Value base)] in
theorem good_words :
    ((goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar).lower port).descriptionWords ≤
      goodWords layout scalarWords mulWords addWords subWords divWords := by
  have prepared := BLSExtractorFrame.prepare_words layout.good
  have evaluated := hash_words layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar scalarWordsBound mulBound addBound
  have tail := afterHash_words layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers
    port scalar scalarWordsBound mulBound addBound subBound divBound
  simp only [goodCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold goodWords
  omega
include scalarWordsBound mulBound addBound subBound negBound divBound in
theorem bad_words :
    ((badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar).lower port).descriptionWords ≤
      badWords layout scalarWords mulWords addWords subWords negWords divWords := by
  have prepared := BLSExtractorFrame.signature_words layout.bad
  have tail := BLSSignatureTail.bad_words layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers
    port scalar scalarWordsBound mulBound addBound subBound negBound divBound
  simp only [badCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold badWords
  change descriptionWords (BLSExtractorFrame.selectSignature layout.bad).code + 1 + _ + 1 ≤ _
  omega
end Signatures.Runtime.CaliperBackend.BLSExtractor
