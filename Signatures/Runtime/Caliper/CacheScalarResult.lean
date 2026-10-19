import Signatures.Runtime.Caliper.CacheScalarFinish
import Signatures.Runtime.Caliper.CacheAccumulateBounds

/-! The actual retained private lookup followed by a scalar result. This uses
the existing bounded cache implementation, including hit-or-room validity.
The result retains the whole cache for subsequent composition. -/
namespace Signatures.Runtime.CaliperBackend.EncodedCacheScalarResult
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {F : Type}
    [DecidableEq (key.Value base)] (layout : CacheAccumulate.Layouts w (key.Value base) F (val.Value base))
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {I : Type} {spec : OracleSpec I}
    {combine : F × (val.Value base × val.Value base) → F}
    (update : Implementation .unit layout.combine layout.coefficient combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)

def completed (value : layout.returned.Value) : (CacheScalarResult.output layout).Value :=
  ⟨(combine (value.val.2.1, value.val.1.1, value.val.2.2), value.val.1.2),
    (CacheScalarResult.finish layout update updateBuffers reserve).preserves value.val value.property⟩
def denote (drawSource : OracleComp spec layout.cache.value.Value) (value : layout.input.Value) :
    OracleComp spec (CacheScalarResult.output layout).Value :=
  completed layout update updateBuffers reserve <$> EncodedCacheAccumulate.retainedDenote layout P comparison correct drawSource value
def code (port : Interactive.Port w spec) (draw : Interactive.Code w) : Interactive.Code w :=
  .seq (EncodedCacheAccumulate.retainedCode layout P comparison correct port draw)
    (.compute (CacheScalarResult.finish layout update updateBuffers reserve).program.code)

theorem refines (port : Interactive.Port w spec) (drawSource : OracleComp spec layout.cache.value.Value)
    (draw : Interactive.Code w)
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation layout.cache.value.representation
      (fun _ => drawSource) draw) :
    Interactive.Refines port .unit layout.input.representation (CacheScalarResult.output layout).representation
      (denote layout P comparison correct update updateBuffers reserve drawSource)
      (code layout P comparison correct update updateBuffers reserve port draw) := by
  convert (EncodedCacheAccumulate.retained_refines layout P comparison correct port drawSource draw drawCorrect).seq
    (Interactive.Refines.compute port .unit (CacheScalarResult.finish layout update updateBuffers reserve).program) using 1
  · funext value
    simp only [bind_pure_comp]
    rfl
  · rfl

theorem listCache (drawSource : OracleComp spec layout.cache.value.Value) (value : layout.input.Value) :
    Subtype.val <$> denote layout P comparison correct update updateBuffers reserve drawSource value =
      (fun result => (combine (value.val.2.1, result.1, value.val.2.2), result.2)) <$>
        (QueryImpl.ListCache.handler (fun _ => Subtype.val <$> drawSource) value.val.1.1).run value.val.1.2.2.1 := by
  have read := EncodedCacheRead.listCache layout.cache P comparison correct drawSource (EncodedCacheAccumulate.request layout value)
  change Subtype.val <$> EncodedCacheRead.denote layout.cache P comparison correct drawSource (EncodedCacheAccumulate.request layout value) =
    (QueryImpl.ListCache.handler (fun _ => Subtype.val <$> drawSource) value.val.1.1).run value.val.1.2.2.1 at read
  rw [← read]
  simp only [denote, EncodedCacheAccumulate.retainedDenote, Functor.map_map]
  rfl

def timeBudget (drawTime updateTime : Nat) : Nat :=
  EncodedCacheRead.timeBudget layout.cache drawTime + updateTime + 404 * layout.width
def codeBudget (drawWords updateWords : Nat) : Nat :=
  EncodedCacheRead.codeBudget layout.cache drawWords + updateWords + 1313 * layout.width + 532

theorem time_bound (port : Interactive.Port w spec) {drawSource : OracleComp spec layout.cache.value.Value} {draw : Interactive.Code w}
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation layout.cache.value.representation
      (fun _ => drawSource) draw) {drawTime updateTime updateWords : Nat}
    (drawBound : Interactive.TimeBound port .unit layout.cache.lookup.unit.representation draw drawTime)
    (updateBound : update.BoundedBy updateTime updateWords) :
    Interactive.TimeBound port .unit layout.input.representation (code layout P comparison correct update updateBuffers reserve port draw)
      (timeBudget layout drawTime updateTime) := by
  have bound := (EncodedCacheAccumulate.retained_time layout P comparison correct port drawCorrect drawBound).seq
    (EncodedCacheAccumulate.retained_refines layout P comparison correct port drawSource draw drawCorrect)
    (Interactive.TimeBound.compute (port := port) (cost := .unit) (CacheScalarResult.finish layout update updateBuffers reserve).program _
      (CacheScalarResult.finish_bounded layout update updateBuffers reserve updateBound).time_le)
  apply bound.mono
  unfold timeBudget
  omega

theorem code_bound (port : Interactive.Port w spec) (draw : Interactive.Code w) {drawWords updateTime updateWords : Nat}
    (drawBound : (draw.lower port).descriptionWords ≤ drawWords) (updateBound : update.BoundedBy updateTime updateWords) :
    ((code layout P comparison correct update updateBuffers reserve port draw).lower port).descriptionWords ≤ codeBudget layout drawWords updateWords := by
  have read := EncodedCacheRead.code_bound layout.cache P comparison correct port draw drawBound
  have retained := Interactive.retain_descriptionWords_le port (EncodedCacheRead.code layout.cache P comparison correct port draw)
    (Interactive.savedBuffer port (EncodedCacheRead.code layout.cache P comparison correct port draw))
    layout.cache.input.representation.encoding.words (CacheRead.output layout.cache).representation.encoding.words layout.saved.representation.encoding.words
  change ((EncodedCacheAccumulate.retainedCode layout P comparison correct port draw).lower port).descriptionWords ≤ _ at retained
  have finished := (CacheScalarResult.finish_bounded layout update updateBuffers reserve updateBound).code_le
  have inputSize : layout.cache.input.representation.encoding.words = layout.cache.lookup.width := LookupLayout.input_words _
  have := layout.sizes
  have := layout.base_sizes
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega
end Signatures.Runtime.CaliperBackend.EncodedCacheScalarResult
