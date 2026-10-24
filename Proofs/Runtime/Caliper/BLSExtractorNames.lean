import Proofs.Runtime.Caliper.BLSExtractorWords

/-! Generated names throughout the complete extractor are derived from the
scalar routines and sampler. Routing only adds its proved small local footprint;
the hash pass's saved buffer is accounted from the actual lowered body. -/
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
    {drawNames names : Nat} (drawBound : WordIO.NamesBound (scalar.lower port) drawNames)
    (mulNames : NamesAccounted mul.program.code names) (addNames : NamesAccounted add.program.code names)
    (subNames : NamesAccounted sub.program.code names) (negNames : NamesAccounted negate.program.code names)
    (divNames : NamesAccounted divide.program.code names)
def nameBudget (drawNames names : Nat) : Nat := BLSSignatureTail.nameBudget drawNames names

omit [DecidableEq (key.Value base)] [Zero (val.Value base)] [Mul (val.Value base)] [Add (val.Value base)]
    [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] in
private theorem routing_names {code : Stmt w} (bounded : registerSlots code ≤ 3 ∧ code.memBound ≤ 2) :
    WordIO.NamesAccounted (.compute code) (nameBudget drawNames names) := by
  have named : NamesBound code 3 := ⟨bounded.1, bounded.2.trans (by decide)⟩
  exact WordIO.NamesAccounted.compute (named.accounted.mono (by unfold nameBudget BLSSignatureTail.nameBudget; omega))
include drawBound mulNames addNames in
omit [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] in
theorem hash_names :
    WordIO.NamesAccounted ((hashCode layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar).lower port)
      (nameBudget drawNames names) := by
  have arithmetic := BLSAccumulate.good_names layout.rows.accumulation.arithmetic names mul add mulNames addNames mulBuffers reserve
  have evaluated := TokenEvaluation.names layout.good (BLSTokens.zero layout zeroValid) (BLSTokens.zero layout zeroValid) (BLSTokens.zero layout zeroValid)
    P comparison correct (BLSPrivateAccumulate.goodUpdate layout.rows.accumulation mul add mulBuffers reserve)
    (BLSPrivateAccumulate.goodUpdate_buffers layout.rows.accumulation mul add mulBuffers reserve addBuffers)
    (BLSPrivateAccumulate.good_reserve layout.rows.accumulation reserve) port scalar drawBound arithmetic
  exact (Interactive.retain_names port evaluated layout.good.input.representation.encoding.words
    layout.rows.good.state.representation.encoding.words (BLSExtractorFrame.context layout.good).representation.encoding.words).mono
      (by simp only [nameBudget, BLSSignatureTail.nameBudget, PairSampling.slots]; omega)
include drawBound mulNames addNames subNames divNames in
omit [Neg (val.Value base)] in
theorem afterHash_names :
    WordIO.NamesAccounted ((afterHashCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar).lower port)
      (nameBudget drawNames names) :=
  (routing_names (BLSExtractorFrame.transition_names layout)).seq
    (BLSSignatureTail.good_names layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers
      port scalar drawBound mulNames addNames subNames divNames)
include drawBound mulNames addNames subNames divNames in
omit [Neg (val.Value base)] in
theorem good_names :
    WordIO.NamesAccounted ((goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar).lower port)
      (nameBudget drawNames names) :=
  (routing_names (BLSExtractorFrame.prepare_names layout.good)).seq
    ((hash_names layout zeroValid P comparison correct mul add mulBuffers addBuffers reserve port scalar drawBound mulNames addNames).seq
      (afterHash_names layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers
        port scalar drawBound mulNames addNames subNames divNames))
include drawBound mulNames addNames subNames negNames divNames in
theorem bad_names :
    WordIO.NamesAccounted ((badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar).lower port)
      (nameBudget drawNames names) :=
  (routing_names (BLSExtractorFrame.signature_names layout.bad)).seq
    (BLSSignatureTail.bad_names layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers
      port scalar drawBound mulNames addNames subNames negNames divNames)
end Signatures.Runtime.CaliperBackend.BLSExtractor
