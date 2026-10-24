import Proofs.Runtime.Caliper.BLSExtractionExit
import Proofs.Runtime.Caliper.BLSExtractorSource

/-! On returned forgeries, terminal dispatch recovers the original scalar
extraction program. The configuration has no semantic effect, but its bytes are
charged by the exit implementation. Cutoff executes a literal zero. -/
namespace Signatures.Runtime.CaliperBackend.BLSExtractionExit
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {G : Type}
    [DecidableEq (key.Value base)] [Field (val.Value base)] [SampleableType (val.Value base)]
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


variable {C Pending : Type}
    (source : ProbComp layout.rows.accumulation.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include uniform in
theorem good_return_source
    (forgery : BLSCallerFinish.Forgery layout.good) (configuration : C) (saved : BLSCallerFinish.Store layout.good)
    (ready : BLSExtractor.goodReady layout (BLSCallerFinish.extractInput layout.good (forgery, configuration, saved))) :
    Subtype.val <$> goodDenote layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers (Pending := Pending) source (.inl forgery, configuration, saved) =
      Prod.fst <$> (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base))
        (LazyAGM.goodFinish ⟨forgery.val.1, forgery.val.2.1, forgery.val.2.2.1, forgery.val.2.2.2⟩
          (LazyAGM.chronological saved.val.2))).run saved.val.1 := by
  have original := BLSExtractor.good_original layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers source uniform
    (BLSCallerFinish.extractInput layout.good (forgery, configuration, saved)) ready
  have projected := congrArg (fun computation => Prod.fst <$> computation) original
  simp only [Functor.map_map] at projected
  unfold goodDenote BLSCallerFinish.denote BLSCallerFinish.success
  exact (PFunctor.FreeM.comp_map Subtype.val
    (fun answer : (BLSCallerFinish.result layout.good).Value =>
      (⟨answer.val.1, answer.property.1⟩ : layout.rows.accumulation.cache.value.Value)) _).symm.trans projected

omit [SampleableType (val.Value base)] in
theorem good_cutoff_source (next : Pending) (configuration : C) (saved : BLSCallerFinish.Store layout.good) :
    Subtype.val <$> goodDenote layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers source (.inr next, configuration, saved) = pure 0 := by
  simp only [goodDenote, BLSCallerFinish.denote]
  rfl

include uniform in
theorem bad_return_source
    (forgery : BLSCallerFinish.Forgery layout.bad) (configuration : C) (saved : BLSCallerFinish.Store layout.bad)
    (ready : BLSExtractor.badReady layout (BLSCallerFinish.extractInput layout.bad (forgery, configuration, saved))) :
    Subtype.val <$> badDenote layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers (Pending := Pending) source (.inl forgery, configuration, saved) =
      Prod.fst <$> (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base × val.Value base))
        (LazyAGM.badFinish ⟨forgery.val.1, forgery.val.2.1, forgery.val.2.2.1, forgery.val.2.2.2⟩
          (LazyAGM.chronological saved.val.2))).run saved.val.1 := by
  have original := BLSExtractor.bad_original layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers source uniform
    (BLSCallerFinish.extractInput layout.bad (forgery, configuration, saved)) ready
  have projected := congrArg (fun computation => Prod.fst <$> computation) original
  simp only [Functor.map_map] at projected
  unfold badDenote BLSCallerFinish.denote BLSCallerFinish.success
  exact (PFunctor.FreeM.comp_map Subtype.val
    (fun answer : (BLSCallerFinish.result layout.bad).Value =>
      (⟨answer.val.1, answer.property.1⟩ : layout.rows.accumulation.cache.value.Value)) _).symm.trans projected

omit [SampleableType (val.Value base)] in
theorem bad_cutoff_source (next : Pending) (configuration : C) (saved : BLSCallerFinish.Store layout.bad) :
    Subtype.val <$> badDenote layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers source (.inr next, configuration, saved) = pure 0 := by
  simp only [badDenote, BLSCallerFinish.denote]
  rfl
end Signatures.Runtime.CaliperBackend.BLSExtractionExit
