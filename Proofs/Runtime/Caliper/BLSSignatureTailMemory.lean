import Proofs.Runtime.Caliper.BLSSignatureTailNames

/-! Source answer, runtime and every visited memory state belong to one
execution of the complete signature tail. Initial caller storage, retained
forgery data, stored code and dense descriptor/name extents are all included. -/
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
    {source : OracleComp spec layout.rows.accumulation.cache.value.Value}
    (scalarCorrect : Interactive.Refines port .unit layout.rows.accumulation.cache.lookup.unit.representation
      layout.rows.accumulation.cache.value.representation (fun _ => source) scalar)
    {scalarTime scalarWords mulTime mulWords addTime addWords subTime subWords negTime negWords divTime divWords drawNames names : Nat}
    (scalarTimeBound : Interactive.TimeBound port .unit layout.rows.accumulation.cache.lookup.unit.representation scalar scalarTime)
    (scalarWordsBound : (scalar.lower port).descriptionWords ≤ scalarWords)
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
    (subBound : sub.BoundedBy subTime subWords) (negBound : negate.BoundedBy negTime negWords) (divBound : divide.BoundedBy divTime divWords)
    (drawNamesBound : WordIO.NamesBound (scalar.lower port) drawNames)
    (mulNames : NamesAccounted mul.program.code names) (addNames : NamesAccounted add.program.code names)
    (subNames : NamesAccounted sub.program.code names) (negNames : NamesAccounted negate.program.code names)
    (divNames : NamesAccounted divide.program.code names)
include scalarCorrect scalarTimeBound scalarWordsBound mulBound addBound subBound divBound drawNamesBound mulNames addNames subNames divNames in
omit [Neg (val.Value base)] in
theorem good_resources
    (fits : layout.good.input.representation.encoding.words + (goodContext layout).representation.encoding.words < 2 ^ w)
    (tape : RandomTape w) (value : GoodInput layout) (ready : goodReady layout value) (before : State w)
    (holds : (goodInput layout fits).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w) (reached : some finished ∈ support ((goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar).execute port .unit tape before)) :
    finished.time ≤ goodTime layout scalarTime mulTime addTime subTime divTime ∧
      ∃ answer ∈ support ((goodDenote layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers source) value), (CacheScalarResult.output layout.rows.accumulation.good).representation.Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit tape ((goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar).lower port) before finished.state finished.trace finished.time finished.net finished.peak,
          ∀ between, execution.Visits between →
            RegisterBound between (max registers ((goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar).lower port).registerSlots) ∧
            between.SupportBound (max buffers ((goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar).lower port).memBound) ∧ between.WellFormed ∧
            (((goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar).lower port).staticWords registers buffers : Int) + between.liveMem (max buffers ((goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar).lower port).memBound) ≤
              5 * goodWords layout scalarWords mulWords addWords subWords divWords + 4 * nameBudget drawNames names + registers + 3 * buffers + before.liveMem buffers +
                goodTime layout scalarTime mulTime addTime subTime divTime := by
  have refined := good_refines layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalarCorrect fits
  have bounded := good_time layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalarCorrect scalarTimeBound mulBound addBound subBound divBound fits
  have stored := good_words layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar scalarWordsBound mulBound addBound subBound divBound
  have accounted := good_names layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar drawNamesBound mulNames addNames subNames divNames
  obtain ⟨elapsed, answer, supported, output, execution, memory⟩ := refined.resources bounded stored accounted tape value ready before holds
    registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨regs, bufs, wf, total⟩ := memory between visited
  exact ⟨regs, bufs, wf, by omega⟩
include scalarCorrect scalarTimeBound scalarWordsBound mulBound addBound subBound negBound divBound drawNamesBound mulNames addNames subNames negNames divNames in
theorem bad_resources
    (fits : layout.bad.input.representation.encoding.words + (badContext layout).representation.encoding.words < 2 ^ w)
    (tape : RandomTape w) (value : BadInput layout) (ready : badReady layout value) (before : State w)
    (holds : (badInput layout fits).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w) (reached : some finished ∈ support ((badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar).execute port .unit tape before)) :
    finished.time ≤ badTime layout scalarTime mulTime addTime subTime negTime divTime ∧
      ∃ answer ∈ support ((badDenote layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers source) value), (CacheScalarResult.output layout.rows.accumulation.bad).representation.Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit tape ((badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar).lower port) before finished.state finished.trace finished.time finished.net finished.peak,
          ∀ between, execution.Visits between →
            RegisterBound between (max registers ((badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar).lower port).registerSlots) ∧
            between.SupportBound (max buffers ((badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar).lower port).memBound) ∧ between.WellFormed ∧
            (((badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar).lower port).staticWords registers buffers : Int) + between.liveMem (max buffers ((badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar).lower port).memBound) ≤
              5 * badWords layout scalarWords mulWords addWords subWords negWords divWords + 4 * nameBudget drawNames names + registers + 3 * buffers + before.liveMem buffers +
                badTime layout scalarTime mulTime addTime subTime negTime divTime := by
  have refined := bad_refines layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalarCorrect fits
  have bounded := bad_time layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalarCorrect scalarTimeBound mulBound addBound subBound negBound divBound fits
  have stored := bad_words layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar scalarWordsBound mulBound addBound subBound negBound divBound
  have accounted := bad_names layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar drawNamesBound mulNames addNames subNames negNames divNames
  obtain ⟨elapsed, answer, supported, output, execution, memory⟩ := refined.resources bounded stored accounted tape value ready before holds
    registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨regs, bufs, wf, total⟩ := memory between visited
  exact ⟨regs, bufs, wf, by omega⟩
end Signatures.Runtime.CaliperBackend.BLSSignatureTail
