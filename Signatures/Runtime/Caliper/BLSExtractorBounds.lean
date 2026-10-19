import Signatures.Runtime.Caliper.BLSExtractor

/-! Runtime of the entire extractor is derived from scalar-routine budgets and
the executed routes, retained hash pass, and signature tail. No additional
running-time assumption is made about any assembled extraction phase. -/
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
def hashTime (scalarTime mulTime addTime : Nat) : Nat :=
  TokenEvaluation.timeBudget layout.good scalarTime (BLSAccumulate.goodTime layout.rows.accumulation.arithmetic mulTime addTime) +
    8 * layout.good.input.representation.encoding.words + 8 * layout.rows.good.state.representation.encoding.words +
    12 * (BLSExtractorFrame.context layout.good).representation.encoding.words
def afterHashTime (scalarTime mulTime addTime subTime divTime : Nat) : Nat :=
  8 * (BLSSignatureTail.goodInput layout (BLSExtractorFrame.goodTailFits layout)).encoding.words +
    BLSSignatureTail.goodTime layout scalarTime mulTime addTime subTime divTime
def goodTime (scalarTime mulTime addTime subTime divTime : Nat) : Nat :=
  8 * (BLSExtractorFrame.prepared layout.good).representation.encoding.words +
    (hashTime layout scalarTime mulTime addTime + afterHashTime layout scalarTime mulTime addTime subTime divTime)
def badTime (scalarTime mulTime addTime subTime negTime divTime : Nat) : Nat :=
  8 * (BLSExtractorFrame.signatureInput layout.bad).representation.encoding.words +
    BLSSignatureTail.badTime layout scalarTime mulTime addTime subTime negTime divTime

variable (port : Interactive.Port w spec) {source : OracleComp spec layout.rows.accumulation.cache.value.Value} {scalar : Interactive.Code w}
    (scalarCorrect : Interactive.Refines port .unit layout.rows.accumulation.cache.lookup.unit.representation
      layout.rows.accumulation.cache.value.representation (fun _ => source) scalar)
    {scalarTime mulTime mulWords addTime addWords subTime subWords negTime negWords divTime divWords : Nat}
    (scalarTimeBound : Interactive.TimeBound port .unit layout.rows.accumulation.cache.lookup.unit.representation scalar scalarTime)
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
    (subBound : sub.BoundedBy subTime subWords) (negBound : negate.BoundedBy negTime negWords) (divBound : divide.BoundedBy divTime divWords)
include scalarCorrect scalarTimeBound mulBound addBound in
omit [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] in
theorem hash_time : Interactive.TimeBoundOn (hashReady layout) port .unit (BLSExtractorFrame.prepared layout.good).representation
    (hashCode layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar)
    (hashTime layout scalarTime mulTime addTime) := by
  have refined := BLSTokens.good_refines layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalarCorrect
  have bounded := BLSTokens.good_time layout zeroValid P comparison correct mul add mulBuffers reserve addBuffers port scalarCorrect scalarTimeBound mulBound addBound
  have retained := (bounded.retain refined (by decide) (BLSExtractorFrame.context layout.good).representation layout.rows.accumulation.cache.wordFits
    (BLSExtractorFrame.prepared layout.good).representation.fits).mono (Interactive.retain_time_unit_le _ _ _ _ _)
  have viewed := retained.viewInput (BLSExtractorFrame.prepared layout.good).representation
    (productView layout.good.input (BLSExtractorFrame.context layout.good)) (fun _ => rfl)
  exact fun tape value ready before holds finished reached => viewed tape value (hash_evaluation_ready layout value ready) before holds finished reached
include scalarCorrect scalarTimeBound mulBound addBound subBound divBound in
omit [Neg (val.Value base)] in
theorem afterHash_time : Interactive.TimeBoundOn (afterHashReady layout) port .unit (BLSExtractorFrame.returned layout.good).representation
    (afterHashCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar)
    (afterHashTime layout scalarTime mulTime addTime subTime divTime) := by
  have refined := (Interactive.Refines.compute port .unit (BLSExtractorFrame.transition layout)).on (afterHashReady layout)
  have bounded := (Interactive.TimeBound.compute (port := port) (cost := .unit) (BLSExtractorFrame.transition layout) _
    (BLSExtractorFrame.transition_time layout)).on (afterHashReady layout)
  have tail := BLSSignatureTail.good_time layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers
    port scalarCorrect scalarTimeBound mulBound addBound subBound divBound (BLSExtractorFrame.goodTailFits layout)
  exact bounded.seq refined tail (by
    intro value ready answer reached
    have equal : answer = BLSExtractorFrame.transitionValue layout value := by simpa only [support_pure, Set.mem_singleton_iff] using reached
    subst answer
    exact BLSExtractorFrame.transitionReady layout value ready)
include scalarCorrect scalarTimeBound mulBound addBound subBound divBound in
omit [Neg (val.Value base)] in
theorem good_time : Interactive.TimeBoundOn (goodReady layout) port .unit (BLSExtractorFrame.input layout.good).representation
    (goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar)
    (goodTime layout scalarTime mulTime addTime subTime divTime) := by
  have refined := hash_refines layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalarCorrect
  have bounded := hash_time layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalarCorrect scalarTimeBound mulBound addBound
  have following := afterHash_time layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers
    port scalarCorrect scalarTimeBound mulBound addBound subBound divBound
  have evaluated := bounded.seq refined following (hash_preserves layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve source)
  have prepared := (Interactive.Refines.compute port .unit (BLSExtractorFrame.prepare layout.good)).on (goodReady layout)
  have preparedTime := (Interactive.TimeBound.compute (port := port) (cost := .unit) (BLSExtractorFrame.prepare layout.good) _
    (BLSExtractorFrame.prepare_time layout.good)).on (goodReady layout)
  exact preparedTime.seq prepared evaluated (by
    intro value ready answer reached
    have equal : answer = BLSExtractorFrame.prepareValue layout.good value := by simpa only [support_pure, Set.mem_singleton_iff] using reached
    subst answer
    exact prepare_preserves layout value ready)
include scalarCorrect scalarTimeBound mulBound addBound subBound negBound divBound in
theorem bad_time : Interactive.TimeBoundOn (badReady layout) port .unit (BLSExtractorFrame.input layout.bad).representation
    (badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar)
    (badTime layout scalarTime mulTime addTime subTime negTime divTime) := by
  have refined := (Interactive.Refines.compute port .unit (BLSExtractorFrame.prepareBad layout)).on (badReady layout)
  have bounded := (Interactive.TimeBound.compute (port := port) (cost := .unit) (BLSExtractorFrame.prepareBad layout) _
    (BLSExtractorFrame.signature_time layout.bad)).on (badReady layout)
  have tail := BLSSignatureTail.bad_time layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers
    port scalarCorrect scalarTimeBound mulBound addBound subBound negBound divBound (BLSExtractorFrame.badTailFits layout)
  exact bounded.seq refined tail (by
    intro value ready answer reached
    have equal : answer = BLSExtractorFrame.badValue layout value := by simpa only [support_pure, Set.mem_singleton_iff] using reached
    subst answer
    exact BLSExtractorFrame.badReady layout value ready)
end Signatures.Runtime.CaliperBackend.BLSExtractor
