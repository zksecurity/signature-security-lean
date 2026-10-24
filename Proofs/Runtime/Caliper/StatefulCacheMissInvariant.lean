import Proofs.Runtime.Caliper.StatefulCacheInvariant

/-! A cached answer bypasses the fresh-entry routine. Its input reservation is
therefore needed only on misses, including when that routine reads another cache.
The executed code and all existing static bounds are unchanged. -/
namespace Signatures.Runtime.CaliperBackend.StatefulCacheRead
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {K V S I : Type} {spec : OracleSpec I}
    (layout : Layouts w K V S) (port : Interactive.Port w spec)
    {ready : S → Prop} {source : S → OracleComp spec (layout.cache.value.Value × S)}
    {draw : Interactive.Code w}
    (drawCorrect : Interactive.RefinesOn ready port .unit layout.saved layout.freshOutput source draw)

include drawCorrect in
theorem branch_refines_on_miss : Interactive.RefinesOn
    (Sum.elim (fun _ => True) (fun value => ready value.2)) port .unit
    layout.choice layout.output (branchDenote layout source) (branchCode layout port draw) :=
  Interactive.RefinesOn.dispatch layout.hitInput layout.missInput layout.output
    ((hit_refines layout port).on (fun _ => True))
    (miss_refines_on layout port drawCorrect) (width_pos layout.cache.wordFits) layout.choice.fits

include drawCorrect in
theorem branch_time_on_miss {drawTime : Nat}
    (drawBound : Interactive.TimeBoundOn ready port .unit layout.saved draw drawTime) :
    Interactive.TimeBoundOn (Sum.elim (fun _ => True) (fun value => ready value.2)) port .unit
      layout.choice (branchCode layout port draw)
      (CacheRead.hitTime layout.cache + CacheRead.finishTime layout.cache + drawTime + 152 * layout.width + 2) := by
  apply (Interactive.TimeBoundOn.dispatch layout.hitInput layout.missInput
    ((hit_time layout port).on (fun _ => True)) (miss_time_on layout port drawCorrect drawBound)
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

def readyOnMiss (ready : S → Prop) (value : layout.cache.input.Value × S) : Prop :=
  ((lookupExpr comparison).denote P value.1.val).1 ≠ true → ready value.2

theorem selected_ready_on_miss (ready : S → Prop) (value : layout.cache.input.Value × S)
    (valid : readyOnMiss layout P comparison ready value) :
    Sum.elim (fun _ => True) (fun answer => ready answer.2) (selected layout P comparison correct value) := by
  by_cases found : ((lookupExpr comparison).denote P value.1.val).1 = true
  · simp [selected, EncodedCacheRead.chosen, GuardedBranch.select, sumView, SumContext.view, found]
  · simpa [selected, EncodedCacheRead.chosen, GuardedBranch.select, sumView, SumContext.view, found]
      using valid found

theorem refines_on_miss {ready : S → Prop} {source : S → OracleComp spec (layout.cache.value.Value × S)}
    {draw : Interactive.Code w}
    (drawCorrect : Interactive.RefinesOn ready port .unit layout.saved layout.freshOutput source draw) :
    Interactive.RefinesOn (readyOnMiss layout P comparison ready) port .unit layout.input layout.output
      (denote layout P comparison correct source) (code port layout P comparison correct draw) := by
  have composed := ((select_refines port layout P comparison correct).on (readyOnMiss layout P comparison ready)).seq
    (branch_refines_on_miss layout port drawCorrect) (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact selected_ready_on_miss layout P comparison correct ready value valid)
  convert composed using 1
  · funext value
    simp only [pure_bind]
    rfl
  · rfl

theorem time_bound_on_miss {ready : S → Prop} {source : S → OracleComp spec (layout.cache.value.Value × S)}
    {draw : Interactive.Code w} {drawTime : Nat}
    (drawCorrect : Interactive.RefinesOn ready port .unit layout.saved layout.freshOutput source draw)
    (drawBound : Interactive.TimeBoundOn ready port .unit layout.saved draw drawTime) :
    Interactive.TimeBoundOn (readyOnMiss layout P comparison ready) port .unit layout.input
      (code port layout P comparison correct draw) (timeBudget layout drawTime) := by
  have composed := Interactive.TimeBoundOn.seq
    ((select_refines port layout P comparison correct).on (readyOnMiss layout P comparison ready))
    ((select_time port layout P comparison correct).on (readyOnMiss layout P comparison ready))
    (branch_time_on_miss layout port drawCorrect drawBound) (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact selected_ready_on_miss layout P comparison correct ready value valid)
  apply composed.mono
  dsimp only [timeBudget]
  omega

end Lookup
end Signatures.Runtime.CaliperBackend.StatefulCacheRead
