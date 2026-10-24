import Proofs.Runtime.Caliper.StatefulCacheBounds
import Proofs.Runtime.Caliper.InteractiveInvariantViews

/-! The stateful cache may call a draw whose input needs a capacity reservation.
The reservation is required before the call, not after it: a miss may spend the
last slot. These refinements use the existing executed cache code unchanged. -/
namespace Signatures.Runtime.CaliperBackend.StatefulCacheRead
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {K V S I : Type} {spec : OracleSpec I}
    (layout : Layouts w K V S) (port : Interactive.Port w spec)
    {ready : S → Prop} {source : S → OracleComp spec (layout.cache.value.Value × S)}
    {draw : Interactive.Code w}
    (drawCorrect : Interactive.RefinesOn ready port .unit layout.saved layout.freshOutput source draw)

include drawCorrect in
theorem miss_refines_on : Interactive.RefinesOn (fun value => ready value.2) port .unit
    layout.missInput layout.output (missDenote layout source) (missCode layout port draw) := by
  have retained := drawCorrect.retain (by decide) (CacheRead.no layout.cache).representation layout.cache.wordFits
    (layout.fits_of_le (by have := layout.sizes; omega)) layout.sampled.fits
  have tail := (Interactive.Refines.compute port .unit (shuffle layout)).seq (insert_refines layout port)
  have sampled := retained.seq (tail.on (fun _ => True)) (fun _ _ _ _ => trivial)
  have compiled := ((Interactive.Refines.compute port .unit (swap layout)).on (fun value => ready value.2)).seq
    sampled (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact valid)
  convert compiled using 1
  · funext value
    simp only [pure_bind, map_pure, bind_pure_comp, Functor.map_map, missDenote]
    rfl
  · rfl

include drawCorrect in
theorem branch_refines_on : Interactive.RefinesOn
    (Sum.elim (fun value => ready value.2) (fun value => ready value.2)) port .unit
    layout.choice layout.output (branchDenote layout source) (branchCode layout port draw) :=
  Interactive.RefinesOn.dispatch layout.hitInput layout.missInput layout.output
    ((hit_refines layout port).on (fun value => ready value.2))
    (miss_refines_on layout port drawCorrect) (width_pos layout.cache.wordFits) layout.choice.fits

include drawCorrect in
theorem miss_time_on {drawTime : Nat}
    (drawBound : Interactive.TimeBoundOn ready port .unit layout.saved draw drawTime) :
    Interactive.TimeBoundOn (fun value => ready value.2) port .unit layout.missInput (missCode layout port draw)
      (drawTime + CacheRead.finishTime layout.cache + 136 * layout.width) := by
  have retained := (Interactive.TimeBoundOn.retain drawCorrect drawBound (by decide)
    (CacheRead.no layout.cache).representation layout.cache.wordFits
    (layout.fits_of_le (by have := layout.sizes; omega))).mono (Interactive.retain_time_unit_le _ _ _ _ _)
  have tail := (Interactive.TimeBound.compute (port := port) (cost := .unit) (shuffle layout) _ (shuffle_time layout)).seq
    (Interactive.Refines.compute port .unit (shuffle layout)) (insert_time layout port)
  have sampled := Interactive.TimeBoundOn.seq
    (drawCorrect.retain (by decide) (CacheRead.no layout.cache).representation layout.cache.wordFits
      (layout.fits_of_le (by have := layout.sizes; omega)) layout.sampled.fits)
    retained (tail.on (fun _ => True)) (fun _ _ _ _ => trivial)
  have compiled := Interactive.TimeBoundOn.seq
    ((Interactive.Refines.compute port .unit (swap layout)).on (fun value => ready value.2))
    ((Interactive.TimeBound.compute (port := port) (cost := .unit) (swap layout) _ (swap_time layout)).on (fun value => ready value.2))
    sampled (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact valid)
  apply compiled.mono
  have := layout.sizes
  have := frame_sizes layout
  omega

include drawCorrect in
theorem branch_time_on {drawTime : Nat}
    (drawBound : Interactive.TimeBoundOn ready port .unit layout.saved draw drawTime) :
    Interactive.TimeBoundOn (Sum.elim (fun value => ready value.2) (fun value => ready value.2)) port .unit
      layout.choice (branchCode layout port draw)
      (CacheRead.hitTime layout.cache + CacheRead.finishTime layout.cache + drawTime + 152 * layout.width + 2) := by
  apply (Interactive.TimeBoundOn.dispatch layout.hitInput layout.missInput
    ((hit_time layout port).on (fun value => ready value.2)) (miss_time_on layout port drawCorrect drawBound)
    (width_pos layout.cache.wordFits) layout.choice.fits).mono
  rw [Interactive.dispatchTime_unit]
  have := frame_sizes layout
  omega

section Lookup
variable {Atom : Type} {base : Atom → Type} {key val : Ty Atom} [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) (val.Value base) S)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))

theorem selected_ready (ready : S → Prop) (value : layout.cache.input.Value × S) (valid : ready value.2) :
    Sum.elim (fun answer => ready answer.2) (fun answer => ready answer.2) (selected layout P comparison correct value) := by
  unfold selected
  cases sumView (CacheRead.yes layout.cache) (CacheRead.no layout.cache)
    (EncodedCacheRead.chosen layout.cache P comparison correct value.1) <;> exact valid

theorem refines_on {ready : S → Prop} {source : S → OracleComp spec (layout.cache.value.Value × S)}
    {draw : Interactive.Code w}
    (drawCorrect : Interactive.RefinesOn ready port .unit layout.saved layout.freshOutput source draw) :
    Interactive.RefinesOn (fun value => ready value.2) port .unit layout.input layout.output
      (denote layout P comparison correct source) (code port layout P comparison correct draw) := by
  have composed := ((select_refines port layout P comparison correct).on (fun value => ready value.2)).seq
    (branch_refines_on layout port drawCorrect) (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact selected_ready layout P comparison correct ready value valid)
  convert composed using 1
  · funext value
    simp only [pure_bind]
    rfl
  · rfl

theorem time_bound_on {ready : S → Prop} {source : S → OracleComp spec (layout.cache.value.Value × S)}
    {draw : Interactive.Code w} {drawTime : Nat}
    (drawCorrect : Interactive.RefinesOn ready port .unit layout.saved layout.freshOutput source draw)
    (drawBound : Interactive.TimeBoundOn ready port .unit layout.saved draw drawTime) :
    Interactive.TimeBoundOn (fun value => ready value.2) port .unit layout.input
      (code port layout P comparison correct draw) (timeBudget layout drawTime) := by
  have composed := Interactive.TimeBoundOn.seq
    ((select_refines port layout P comparison correct).on (fun value => ready value.2))
    ((select_time port layout P comparison correct).on (fun value => ready value.2))
    (branch_time_on layout port drawCorrect drawBound) (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact selected_ready layout P comparison correct ready value valid)
  apply composed.mono
  dsimp only [timeBudget]
  omega

end Lookup
end Signatures.Runtime.CaliperBackend.StatefulCacheRead
