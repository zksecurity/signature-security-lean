import Signatures.Runtime.Caliper.BLSSignatureTailLayout

/-! Final frame construction and private lookup on the exact returned bytes
of signature evaluation. The arbitrary source extension outside the proved
hit-or-room domain has no execution contract and adds no machine branch. -/
namespace Signatures.Runtime.CaliperBackend.BLSSignatureTail
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {G : Type}
    [DecidableEq (key.Value base)] [Zero (val.Value base)] [Add (val.Value base)]
    [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)]
    (layout : BLSTokens.Layouts w (key.Value base) G (val.Value base))
    (zeroValid : layout.rows.accumulation.cache.value.valid 0)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (add : Implementation .unit layout.rows.accumulation.arithmetic.pair layout.rows.accumulation.cache.value (fun value => value.1 + value.2))
    (sub : Implementation .unit layout.rows.accumulation.arithmetic.pair layout.rows.accumulation.cache.value (fun value => value.1 - value.2))
    (negate : Implementation .unit layout.rows.accumulation.cache.value layout.rows.accumulation.cache.value Neg.neg)
    (divide : Implementation .unit layout.rows.accumulation.arithmetic.pair layout.rows.accumulation.cache.value (fun value => value.1 / value.2))
    {slots : Nat} (addBuffers : add.program.code.memBound ≤ slots) (subBuffers : sub.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w) (negBuffers : negate.program.code.memBound ≤ slots) (divBuffers : divide.program.code.memBound ≤ slots)

def goodRequest (value : GoodReturned layout) (ready : goodFinalReady layout value) : layout.rows.accumulation.good.input.Value :=
  ⟨((value.2.val.1, 0, value.1.val.2, ()), value.2.val.2.1 + value.2.val.2.2, value.1.val.1),
    (BLSFinalFrame.good layout.rows.accumulation add addBuffers reserve zeroValid).preserves
      (goodAdmitted layout ⟨value, ready⟩).val (goodAdmitted layout ⟨value, ready⟩).property⟩
def badRequest (value : BadReturned layout) (ready : badFinalReady layout zeroValid value) : layout.rows.accumulation.bad.input.Value :=
  ⟨((value.2.val.1, (0, 0), value.1.val.2, ()), value.2.val.2, value.1.val.1),
    (BLSFinalFrame.bad layout.rows.accumulation zeroValid).preserves
      (badAdmitted layout zeroValid ⟨value, ready⟩).val (badAdmitted layout zeroValid ⟨value, ready⟩).property⟩
def goodPrepare : Realizer .unit ((goodReturned layout).restrict (goodFinalReady layout)) layout.rows.accumulation.good.input.representation
    (fun value => goodRequest layout zeroValid add addBuffers reserve value.val value.property) :=
  (BLSFinalFrame.good layout.rows.accumulation add addBuffers reserve zeroValid).program.viewInput _ (goodAdmitted layout) (fun _ => rfl)
def badPrepare : Realizer .unit ((badReturned layout).restrict (badFinalReady layout zeroValid)) layout.rows.accumulation.bad.input.representation
    (fun value => badRequest layout zeroValid value.val value.property) :=
  (BLSFinalFrame.bad layout.rows.accumulation zeroValid).program.viewInput _ (badAdmitted layout zeroValid) (fun _ => rfl)

variable {I : Type} {spec : OracleSpec I}
def goodFinishCode (port : Interactive.Port w spec) (scalar : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (BLSFinalFrame.good layout.rows.accumulation add addBuffers reserve zeroValid).program.code)
    (BLSFinalTarget.goodCode layout.rows.accumulation P comparison correct sub divide subBuffers reserve divBuffers port scalar)
def badFinishCode (port : Interactive.Port w spec) (scalar : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (BLSFinalFrame.bad layout.rows.accumulation zeroValid).program.code)
    (BLSFinalTarget.badCode layout.rows.accumulation P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers port scalar)
def goodFinish (source : OracleComp spec layout.rows.accumulation.cache.value.Value) (value : GoodReturned layout) :
    OracleComp spec (CacheScalarResult.output layout.rows.accumulation.good).Value :=
  if ready : goodFinalReady layout value then
    BLSFinalTarget.goodDenote layout.rows.accumulation P comparison correct sub divide subBuffers reserve divBuffers source
      (goodRequest layout zeroValid add addBuffers reserve value ready)
  else pure ⟨(0, value.1.val.2), zeroValid, value.1.property.2⟩
def badFinish (source : OracleComp spec layout.rows.accumulation.cache.value.Value) (value : BadReturned layout) :
    OracleComp spec (CacheScalarResult.output layout.rows.accumulation.bad).Value :=
  if ready : badFinalReady layout zeroValid value then
    BLSFinalTarget.badDenote layout.rows.accumulation P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers source
      (badRequest layout zeroValid value ready)
  else pure ⟨(0, value.1.val.2), zeroValid, value.1.property.2⟩

variable (port : Interactive.Port w spec) {source : OracleComp spec layout.rows.accumulation.cache.value.Value} {scalar : Interactive.Code w}
    (scalarCorrect : Interactive.Refines port .unit layout.rows.accumulation.cache.lookup.unit.representation
      layout.rows.accumulation.cache.value.representation (fun _ => source) scalar)
include scalarCorrect in
omit [Neg (val.Value base)] in
theorem goodFinish_refines : Interactive.RefinesOn (goodFinalReady layout) port .unit (goodReturned layout)
    (CacheScalarResult.output layout.rows.accumulation.good).representation
    (goodFinish layout zeroValid P comparison correct add sub divide addBuffers subBuffers reserve divBuffers source)
    (goodFinishCode layout zeroValid P comparison correct add sub divide addBuffers subBuffers reserve divBuffers port scalar) := by
  have prepared := Interactive.Refines.compute port .unit (goodPrepare layout zeroValid add addBuffers reserve)
  have target := BLSFinalTarget.good_refines layout.rows.accumulation P comparison correct sub divide subBuffers reserve divBuffers port scalarCorrect
  have composed := prepared.seq target
  intro tape value ready before holds
  unfold goodFinish
  rw [dite_eq_left ready]
  simpa only [pure_bind, goodFinishCode, goodPrepare, Realizer.viewInput] using composed tape ⟨value, ready⟩ before holds
include scalarCorrect in
omit [Add (val.Value base)] in
theorem badFinish_refines : Interactive.RefinesOn (badFinalReady layout zeroValid) port .unit (badReturned layout)
    (CacheScalarResult.output layout.rows.accumulation.bad).representation
    (badFinish layout zeroValid P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers source)
    (badFinishCode layout zeroValid P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers port scalar) := by
  have prepared := Interactive.Refines.compute port .unit (badPrepare layout zeroValid)
  have target := BLSFinalTarget.bad_refines layout.rows.accumulation P comparison correct sub negate divide subBuffers reserve negBuffers divBuffers port scalarCorrect
  have composed := prepared.seq target
  intro tape value ready before holds
  unfold badFinish
  rw [dite_eq_left ready]
  simpa only [pure_bind, badFinishCode, badPrepare, Realizer.viewInput] using composed tape ⟨value, ready⟩ before holds
end Signatures.Runtime.CaliperBackend.BLSSignatureTail
