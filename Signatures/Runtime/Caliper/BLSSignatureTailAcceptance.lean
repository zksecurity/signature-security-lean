import Signatures.Runtime.Caliper.BLSSignatureTailMemory
import Signatures.Runtime.Caliper.TokenEvaluationBuffers

/-! Every stored operand in the composed signature tail fits the word width.
The extra context buffer is derived from actual evaluator footprints, never
assumed representable merely because its callees were accepted. -/
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
    (scalarFits : (scalar.lower port).DescriptionFits) {drawNames : Nat}
    (drawBound : WordIO.NamesBound (scalar.lower port) drawNames) (namesFit : drawNames + 4 < 2 ^ w)
include scalarFits drawBound namesFit in
omit [Neg (val.Value base)] in
theorem good_descriptionFits :
    ((goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar).lower port).DescriptionFits := by
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
    layout.good.input.representation.encoding.words layout.rows.good.state.representation.encoding.words (goodContext layout).representation.encoding.words
    layout.rows.accumulation.cache.wordFits evaluated savedFit layout.good.input.representation.fits
    (goodContext layout).representation.fits (goodOutputFits layout)
  have target := EncodedCacheScalarResult.descriptionFits layout.rows.accumulation.good P comparison correct
    (BLSFinalTarget.goodUpdate layout.rows.accumulation sub divide subBuffers reserve)
    (BLSFinalTarget.goodUpdate_buffers layout.rows.accumulation sub divide subBuffers reserve divBuffers)
    (BLSFinalTarget.good_reserve layout.rows.accumulation reserve) port scalar scalarFits drawBound (by omega)
  exact WordIO.Code.DescriptionFits.seq layout.rows.accumulation.cache.wordFits retained
    (.seq layout.rows.accumulation.cache.wordFits
      (.compute (BLSFinalFrame.good layout.rows.accumulation add addBuffers reserve zeroValid).program.description_fits) target)
include scalarFits drawBound namesFit in
theorem bad_descriptionFits :
    ((badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar).lower port).DescriptionFits := by
  have pairedNames := PairSampling.names layout.rows.accumulation.cache.value layout.rows.accumulation.cache.value
    layout.rows.accumulation.cache.wordFits layout.rows.accumulation.cache.pairValueFits port scalar scalar drawBound drawBound
  have pairedFits := PairSampling.descriptionFits layout.rows.accumulation.cache.value layout.rows.accumulation.cache.value
    layout.rows.accumulation.cache.wordFits layout.rows.accumulation.cache.pairValueFits port scalar scalar scalarFits scalarFits drawBound (by omega)
  have pairNameFit : PairSampling.slots drawNames drawNames + 2 < 2 ^ w := by
    have := layout.rows.accumulation.cache.wordFits
    unfold PairSampling.slots
    omega
  have evaluated := TokenEvaluation.descriptionFits (base := base) (key := key) (val := .pair val val) layout.bad
    (BLSTokens.zero layout zeroValid) (BLSTokens.pairZero layout zeroValid) (BLSTokens.pairZero layout zeroValid) P comparison correct
    (BLSPrivateAccumulate.badUpdate layout.rows.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.badUpdate_buffers layout.rows.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.bad_reserve layout.rows.accumulation reserve) port
    (BLSPrivateAccumulate.pairSampler layout.rows.accumulation port scalar) pairedFits pairedNames pairNameFit
  have buffers := TokenEvaluation.buffers (base := base) (key := key) (val := .pair val val) layout.bad
    (BLSTokens.zero layout zeroValid) (BLSTokens.pairZero layout zeroValid) (BLSTokens.pairZero layout zeroValid) P comparison correct
    (BLSPrivateAccumulate.badUpdate layout.rows.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.badUpdate_buffers layout.rows.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.bad_reserve layout.rows.accumulation reserve) port
    (BLSPrivateAccumulate.pairSampler layout.rows.accumulation port scalar)
  let body := BLSTokens.badCode layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalar
  have savedFit : Interactive.savedBuffer port body < 2 ^ w := by
    change (body.lower port).memBound ≤ _ at buffers
    have sampled := pairedNames.buffers
    change ((BLSPrivateAccumulate.pairSampler layout.rows.accumulation port scalar).lower port).memBound ≤ PairSampling.slots drawNames drawNames at sampled
    have := layout.rows.accumulation.cache.wordFits
    dsimp only [Interactive.savedBuffer, PairSampling.slots] at *
    omega
  have retained := Interactive.retain_descriptionFits port body (Interactive.savedBuffer port body)
    layout.bad.input.representation.encoding.words layout.rows.bad.state.representation.encoding.words (badContext layout).representation.encoding.words
    layout.rows.accumulation.cache.wordFits evaluated savedFit layout.bad.input.representation.fits
    (badContext layout).representation.fits (badOutputFits layout)
  have target := EncodedCacheScalarResult.descriptionFits (base := base) (key := key) (val := .pair val val) layout.rows.accumulation.bad P comparison correct
    (BLSFinalTarget.badUpdate layout.rows.accumulation sub negate divide subBuffers reserve negBuffers)
    (BLSFinalTarget.badUpdate_buffers layout.rows.accumulation sub negate divide subBuffers reserve negBuffers divBuffers)
    (BLSFinalTarget.bad_reserve layout.rows.accumulation reserve) port
    (BLSPrivateAccumulate.pairSampler layout.rows.accumulation port scalar) pairedFits pairedNames pairNameFit
  exact WordIO.Code.DescriptionFits.seq layout.rows.accumulation.cache.wordFits retained
    (.seq layout.rows.accumulation.cache.wordFits (.compute (BLSFinalFrame.bad layout.rows.accumulation zeroValid).program.description_fits) target)
end Signatures.Runtime.CaliperBackend.BLSSignatureTail
