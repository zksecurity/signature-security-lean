import Signatures.Runtime.Caliper.CacheAccumulateFinishNames
import Signatures.Runtime.Caliper.CacheReadOracle

/-! An executed private read followed by an accumulator update. The coefficient
and old accumulator survive the complete cache implementation in a disjoint
saved buffer. The cache is the shared list cache, with sampling only on misses. -/

namespace Signatures.Runtime.CaliperBackend.EncodedCacheAccumulate
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {F : Type}
    [DecidableEq (key.Value base)] (layout : CacheAccumulate.Layouts w (key.Value base) F (val.Value base))
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {I : Type} {spec : OracleSpec I}

def request (value : layout.input.Value) : layout.cache.input.Value :=
  (productView layout.cache.input layout.saved value).1
def retainedValue (value : layout.input.Value) (answer : (CacheRead.output layout.cache).Value) : layout.returned.Value :=
  (productView (CacheRead.output layout.cache) layout.saved).symm
    (answer, (productView layout.cache.input layout.saved value).2)
def retainedDenote (drawSource : OracleComp spec layout.cache.value.Value) (value : layout.input.Value) :
    OracleComp spec layout.returned.Value :=
  retainedValue layout value <$> EncodedCacheRead.denote layout.cache P comparison correct drawSource (request layout value)
def retainedCode (port : Interactive.Port w spec) (draw : Interactive.Code w) : Interactive.Code w :=
  let read := EncodedCacheRead.code layout.cache P comparison correct port draw
  Interactive.retain read (Interactive.savedBuffer port read) layout.cache.input.representation.encoding.words
    (CacheRead.output layout.cache).representation.encoding.words layout.saved.representation.encoding.words

theorem retained_refines (port : Interactive.Port w spec) (drawSource : OracleComp spec layout.cache.value.Value)
    (draw : Interactive.Code w)
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation layout.cache.value.representation
      (fun _ => drawSource) draw) :
    Interactive.Refines port .unit layout.input.representation layout.returned.representation
      (retainedDenote layout P comparison correct drawSource) (retainedCode layout P comparison correct port draw) := by
  have retained := (EncodedCacheRead.refines layout.cache P comparison correct port drawSource draw drawCorrect).retain
    (by decide) layout.saved.representation layout.cache.wordFits layout.input.representation.fits layout.returned.representation.fits
  have viewed := (retained.viewInput layout.input.representation
    (productView layout.cache.input layout.saved) (fun _ => rfl)).viewOutput layout.returned.representation
      (productView (CacheRead.output layout.cache) layout.saved).symm (by
        intro value
        exact congrArg ((CacheRead.output layout.cache).representation.prod layout.saved.representation
          layout.returned.representation.fits).encoding.encode
          ((productView (CacheRead.output layout.cache) layout.saved).apply_symm_apply value))
  convert viewed using 1
  · funext value
    exact PFunctor.FreeM.comp_map _ _ _
  · rfl

variable {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.combine layout.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)

def completed (value : layout.returned.Value) : (CacheRead.output layout.cache).Value :=
  ⟨(combine (value.val.2.1, value.val.1.1, value.val.2.2), value.val.1.2),
    (CacheAccumulate.finish layout update updateBuffers reserve).preserves value.val value.property⟩
def denote (drawSource : OracleComp spec layout.cache.value.Value) (value : layout.input.Value) :
    OracleComp spec (CacheRead.output layout.cache).Value :=
  completed layout update updateBuffers reserve <$> retainedDenote layout P comparison correct drawSource value
def code (port : Interactive.Port w spec) (draw : Interactive.Code w) : Interactive.Code w :=
  .seq (retainedCode layout P comparison correct port draw) (.compute (CacheAccumulate.finish layout update updateBuffers reserve).program.code)

theorem refines (port : Interactive.Port w spec) (drawSource : OracleComp spec layout.cache.value.Value)
    (draw : Interactive.Code w)
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation layout.cache.value.representation
      (fun _ => drawSource) draw) :
    Interactive.Refines port .unit layout.input.representation (CacheRead.output layout.cache).representation
      (denote layout P comparison correct update updateBuffers reserve drawSource)
      (code layout P comparison correct update updateBuffers reserve port draw) := by
  convert (retained_refines layout P comparison correct port drawSource draw drawCorrect).seq
    (Interactive.Refines.compute port .unit (CacheAccumulate.finish layout update updateBuffers reserve).program) using 1
  · funext value
    simp only [bind_pure_comp]
    rfl
  · rfl

/-- Source agreement preserves the entire updated private cache, not just the
accumulator result. No public transcript event is introduced by this read. -/
theorem listCache (drawSource : OracleComp spec layout.cache.value.Value) (value : layout.input.Value) :
    Subtype.val <$> denote layout P comparison correct update updateBuffers reserve drawSource value =
      (fun result => (combine (value.val.2.1, result.1, value.val.2.2), result.2)) <$>
        (QueryImpl.ListCache.handler (fun _ => Subtype.val <$> drawSource) value.val.1.1).run value.val.1.2.2.1 := by
  have read := EncodedCacheRead.listCache layout.cache P comparison correct drawSource (request layout value)
  change Subtype.val <$> EncodedCacheRead.denote layout.cache P comparison correct drawSource (request layout value) =
    (QueryImpl.ListCache.handler (fun _ => Subtype.val <$> drawSource) value.val.1.1).run value.val.1.2.2.1 at read
  rw [← read]
  simp only [denote, retainedDenote, Functor.map_map]
  rfl

end Signatures.Runtime.CaliperBackend.EncodedCacheAccumulate
