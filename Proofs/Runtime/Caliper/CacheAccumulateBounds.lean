import Proofs.Runtime.Caliper.CacheAccumulate

/-! Whole read/update bounds derived from lookup, sampling, local arithmetic
and all saved-frame copying. These bound the actual composed word program. -/
namespace Signatures.Runtime.CaliperBackend.EncodedCacheAccumulate
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {F : Type}
    [DecidableEq (key.Value base)] (layout : CacheAccumulate.Layouts w (key.Value base) F (val.Value base))
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {I : Type} {spec : OracleSpec I}
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.combine layout.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    (port : Interactive.Port w spec)

def timeBudget (drawTime updateTime : Nat) : Nat :=
  EncodedCacheRead.timeBudget layout.cache drawTime + updateTime + 404 * layout.width
def codeBudget (drawWords updateWords : Nat) : Nat :=
  EncodedCacheRead.codeBudget layout.cache drawWords + updateWords + 1313 * layout.width + 532

theorem retained_time {drawSource : OracleComp spec layout.cache.value.Value} {draw : Interactive.Code w}
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation layout.cache.value.representation
      (fun _ => drawSource) draw) {drawTime : Nat}
    (drawBound : Interactive.TimeBound port .unit layout.cache.lookup.unit.representation draw drawTime) :
    Interactive.TimeBound port .unit layout.input.representation (retainedCode layout P comparison correct port draw)
      (EncodedCacheRead.timeBudget layout.cache drawTime + 28 * layout.width) := by
  have read := EncodedCacheRead.refines layout.cache P comparison correct port drawSource draw drawCorrect
  have retained := (EncodedCacheRead.time_bound layout.cache P comparison correct port drawCorrect drawBound).retain
    read (by decide) layout.saved.representation layout.cache.wordFits layout.input.representation.fits
  have viewed := retained.viewInput layout.input.representation (productView layout.cache.input layout.saved) (fun _ => rfl)
  apply viewed.mono
  apply (Interactive.retain_time_unit_le _ _ _ _ _).trans
  have inputSize : layout.cache.input.representation.encoding.words = layout.cache.lookup.width := LookupLayout.input_words _
  have := layout.sizes
  have := layout.base_sizes
  omega

theorem time_bound {drawSource : OracleComp spec layout.cache.value.Value} {draw : Interactive.Code w}
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation layout.cache.value.representation
      (fun _ => drawSource) draw) {drawTime updateTime updateWords : Nat}
    (drawBound : Interactive.TimeBound port .unit layout.cache.lookup.unit.representation draw drawTime)
    (updateBound : update.BoundedBy updateTime updateWords) :
    Interactive.TimeBound port .unit layout.input.representation (code layout P comparison correct update updateBuffers reserve port draw)
      (timeBudget layout drawTime updateTime) := by
  have bound := (retained_time layout P comparison correct port drawCorrect drawBound).seq
    (retained_refines layout P comparison correct port drawSource draw drawCorrect)
    (Interactive.TimeBound.compute (port := port) (cost := .unit) (CacheAccumulate.finish layout update updateBuffers reserve).program _
      (CacheAccumulate.finish_bounded layout update updateBound updateBuffers reserve).time_le)
  apply bound.mono
  unfold timeBudget
  omega

theorem code_bound (draw : Interactive.Code w) {drawWords updateTime updateWords : Nat}
    (drawBound : (draw.lower port).descriptionWords ≤ drawWords) (updateBound : update.BoundedBy updateTime updateWords) :
    ((code layout P comparison correct update updateBuffers reserve port draw).lower port).descriptionWords ≤ codeBudget layout drawWords updateWords := by
  have read := EncodedCacheRead.code_bound layout.cache P comparison correct port draw drawBound
  have retained := Interactive.retain_descriptionWords_le port (EncodedCacheRead.code layout.cache P comparison correct port draw)
    (Interactive.savedBuffer port (EncodedCacheRead.code layout.cache P comparison correct port draw))
    layout.cache.input.representation.encoding.words (CacheRead.output layout.cache).representation.encoding.words layout.saved.representation.encoding.words
  change ((retainedCode layout P comparison correct port draw).lower port).descriptionWords ≤ _ at retained
  have finished := (CacheAccumulate.finish_bounded layout update updateBound updateBuffers reserve).code_le
  have inputSize : layout.cache.input.representation.encoding.words = layout.cache.lookup.width := LookupLayout.input_words _
  have := layout.sizes
  have := layout.base_sizes
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

end Signatures.Runtime.CaliperBackend.EncodedCacheAccumulate
