import Proofs.Runtime.Caliper.BLSExtractorMemory

/-! Every stored operand of each complete extractor fits the machine word.
The hash-pass context name is derived from the evaluator's actual footprint;
routing fits and signature-tail acceptance are already proved constructors. -/
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


variable {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec) (scalar : Interactive.Code w)
    (scalarFits : (scalar.lower port).DescriptionFits) {drawNames : Nat}
    (drawBound : WordIO.NamesBound (scalar.lower port) drawNames) (namesFit : drawNames + 4 < 2 ^ w)
include scalarFits drawBound namesFit in
omit [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] in
theorem hash_descriptionFits :
    ((hashCode layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar).lower port).DescriptionFits := by
  have evaluated := TokenEvaluation.descriptionFits layout.good (BLSTokens.zero layout zeroValid) (BLSTokens.zero layout zeroValid) (BLSTokens.zero layout zeroValid)
    P comparison correct (BLSPrivateAccumulate.goodUpdate layout.rows.accumulation mul add mulBuffers reserve)
    (BLSPrivateAccumulate.goodUpdate_buffers layout.rows.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.good_reserve layout.rows.accumulation reserve) port scalar scalarFits drawBound (by omega)
  have buffers := TokenEvaluation.buffers layout.good (BLSTokens.zero layout zeroValid) (BLSTokens.zero layout zeroValid) (BLSTokens.zero layout zeroValid)
    P comparison correct (BLSPrivateAccumulate.goodUpdate layout.rows.accumulation mul add mulBuffers reserve)
    (BLSPrivateAccumulate.goodUpdate_buffers layout.rows.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.good_reserve layout.rows.accumulation reserve) port scalar
  let body := BLSTokens.goodCode layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalar
  have savedFit : Interactive.savedBuffer port body < 2 ^ w := by
    change (body.lower port).memBound ≤ _ at buffers
    have := drawBound.buffers
    have := layout.rows.accumulation.cache.wordFits
    dsimp only [Interactive.savedBuffer]
    omega
  have retained := Interactive.retain_descriptionFits port body (Interactive.savedBuffer port body)
    layout.good.input.representation.encoding.words layout.rows.good.state.representation.encoding.words (BLSExtractorFrame.context layout.good).representation.encoding.words
    layout.rows.accumulation.cache.wordFits evaluated savedFit layout.good.input.representation.fits
    (BLSExtractorFrame.context layout.good).representation.fits (BLSExtractorFrame.returned layout.good).representation.fits
  exact retained
include scalarFits drawBound namesFit in
omit [Neg (val.Value base)] in
theorem good_descriptionFits :
    ((goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar).lower port).DescriptionFits := by
  have hashed := hash_descriptionFits layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar scalarFits drawBound namesFit
  have tail := BLSSignatureTail.good_descriptionFits layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers
    port scalar scalarFits drawBound namesFit
  exact WordIO.Code.DescriptionFits.seq layout.rows.accumulation.cache.wordFits (.compute (BLSExtractorFrame.prepare layout.good).description_fits)
    (.seq layout.rows.accumulation.cache.wordFits hashed
      (.seq layout.rows.accumulation.cache.wordFits (.compute (BLSExtractorFrame.transition layout).description_fits) tail))
include scalarFits drawBound namesFit in
theorem bad_descriptionFits :
    ((badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar).lower port).DescriptionFits :=
  WordIO.Code.DescriptionFits.seq layout.rows.accumulation.cache.wordFits (.compute (BLSExtractorFrame.prepareBad layout).description_fits)
    (BLSSignatureTail.bad_descriptionFits layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers
      port scalar scalarFits drawBound namesFit)
end Signatures.Runtime.CaliperBackend.BLSExtractor
