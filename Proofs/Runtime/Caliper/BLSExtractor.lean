import Proofs.Runtime.Caliper.BLSExtractorHash
import Proofs.Runtime.Caliper.BLSSignatureTailAcceptance

/-! Complete bounded BLS private extractors, from the original forgery and
reverse-stored logs to the extracted scalar and final cache. The good branch
executes both hash and signature passes. All surrounding routing and retained
context are constructed programs; only named scalar routines are parameters. -/
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
def afterHashCode (port : Interactive.Port w spec) (scalar : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (BLSExtractorFrame.transition layout).code)
    (BLSSignatureTail.goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar)
def goodCode (port : Interactive.Port w spec) (scalar : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (BLSExtractorFrame.prepare layout.good).code)
    (.seq (hashCode layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar)
      (afterHashCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar))
def badCode (port : Interactive.Port w spec) (scalar : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (BLSExtractorFrame.prepareBad layout).code)
    (BLSSignatureTail.badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar)
def afterHash (source : OracleComp spec layout.rows.accumulation.cache.value.Value) (value : HashOutput layout) :
    OracleComp spec (CacheScalarResult.output layout.rows.accumulation.good).Value :=
  BLSSignatureTail.goodDenote layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers source
    (BLSExtractorFrame.transitionValue layout value)
def goodDenote (source : OracleComp spec layout.rows.accumulation.cache.value.Value) (value : GoodInput layout) :
    OracleComp spec (CacheScalarResult.output layout.rows.accumulation.good).Value :=
  hashDenote layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve source (BLSExtractorFrame.prepareValue layout.good value) >>=
    afterHash layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers source
def badDenote (source : OracleComp spec layout.rows.accumulation.cache.value.Value) (value : BadInput layout) :
    OracleComp spec (CacheScalarResult.output layout.rows.accumulation.bad).Value :=
  BLSSignatureTail.badDenote layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers source
    (BLSExtractorFrame.badValue layout value)

variable (port : Interactive.Port w spec) {source : OracleComp spec layout.rows.accumulation.cache.value.Value} {scalar : Interactive.Code w}
    (scalarCorrect : Interactive.Refines port .unit layout.rows.accumulation.cache.lookup.unit.representation
      layout.rows.accumulation.cache.value.representation (fun _ => source) scalar)
include scalarCorrect in
omit [Neg (val.Value base)] in
theorem afterHash_refines : Interactive.RefinesOn (afterHashReady layout) port .unit (BLSExtractorFrame.returned layout.good).representation
    (CacheScalarResult.output layout.rows.accumulation.good).representation
    (afterHash layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers source)
    (afterHashCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar) := by
  have prepared := (Interactive.Refines.compute port .unit (BLSExtractorFrame.transition layout)).on (afterHashReady layout)
  have tail := BLSSignatureTail.good_refines layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers
    port scalarCorrect (BLSExtractorFrame.goodTailFits layout)
  have composed := prepared.seq tail (by
    intro value ready answer reached
    have equal : answer = BLSExtractorFrame.transitionValue layout value := by simpa only [support_pure, Set.mem_singleton_iff] using reached
    subst answer
    exact BLSExtractorFrame.transitionReady layout value ready)
  convert composed using 1
  · funext value
    exact (pure_bind _ _).symm
  · rfl
include scalarCorrect in
omit [Neg (val.Value base)] in
theorem good_refines : Interactive.RefinesOn (goodReady layout) port .unit (BLSExtractorFrame.input layout.good).representation
    (CacheScalarResult.output layout.rows.accumulation.good).representation
    (goodDenote layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers source)
    (goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar) := by
  have evaluated := (hash_refines layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalarCorrect).seq
    (afterHash_refines layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalarCorrect)
    (hash_preserves layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve source)
  have prepared := (Interactive.Refines.compute port .unit (BLSExtractorFrame.prepare layout.good)).on (goodReady layout)
  have composed := prepared.seq evaluated (by
    intro value ready answer reached
    have equal : answer = BLSExtractorFrame.prepareValue layout.good value := by simpa only [support_pure, Set.mem_singleton_iff] using reached
    subst answer
    exact prepare_preserves layout value ready)
  convert composed using 1
  · funext value
    exact (pure_bind _ _).symm
  · rfl
include scalarCorrect in
theorem bad_refines : Interactive.RefinesOn (badReady layout) port .unit (BLSExtractorFrame.input layout.bad).representation
    (CacheScalarResult.output layout.rows.accumulation.bad).representation
    (badDenote layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers source)
    (badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar) := by
  have prepared := (Interactive.Refines.compute port .unit (BLSExtractorFrame.prepareBad layout)).on (badReady layout)
  have tail := BLSSignatureTail.bad_refines layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers
    port scalarCorrect (BLSExtractorFrame.badTailFits layout)
  have composed := prepared.seq tail (by
    intro value ready answer reached
    have equal : answer = BLSExtractorFrame.badValue layout value := by simpa only [support_pure, Set.mem_singleton_iff] using reached
    subst answer
    exact BLSExtractorFrame.badReady layout value ready)
  convert composed using 1
  · funext value
    exact (pure_bind _ _).symm
  · rfl
end Signatures.Runtime.CaliperBackend.BLSExtractor
