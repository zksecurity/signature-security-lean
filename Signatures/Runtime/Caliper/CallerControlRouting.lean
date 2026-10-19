import Signatures.Runtime.Caliper.CallerControlRefinement

/-! Explicit budgets for return/cutoff tags and generated caller routing. No
layout conversion or saved-context transfer is treated as free. -/

namespace Signatures.Runtime.CaliperBackend.CallerControl
open Caliper OracleComp OracleSpec

variable {w : Nat} {C Q R B S : Type} (layout : CallerStep.Layouts w C Q R B S)

theorem sizes :
    layout.state.encoding.words ≤ CallerStep.width layout ∧
    layout.request.encoding.words ≤ CallerStep.width layout ∧
    layout.reply.encoding.words ≤ CallerStep.width layout ∧
    layout.result.encoding.words ≤ CallerStep.width layout ∧
    layout.store.encoding.words ≤ CallerStep.width layout ∧
    (CallerStep.pending layout).encoding.words ≤ CallerStep.width layout ∧
    (CallerStep.next layout).encoding.words ≤ CallerStep.width layout ∧
    (CallerStep.frame layout).encoding.words ≤ CallerStep.width layout ∧
    (CallerStep.output layout).encoding.words ≤ CallerStep.width layout ∧
    (result layout).encoding.words ≤ CallerStep.width layout ∧
    (choice layout).encoding.words ≤ CallerStep.width layout ∧
    (iteration layout).encoding.words ≤ 2 * CallerStep.width layout := by
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧
    layout.request.encoding.words + layout.state.encoding.words ≤ _ ∧
    1 + max layout.result.encoding.words (layout.request.encoding.words + layout.state.encoding.words) ≤ _ ∧
    layout.request.encoding.words + layout.state.encoding.words + layout.store.encoding.words ≤ _ ∧
    1 + max layout.result.encoding.words (layout.request.encoding.words + layout.state.encoding.words) + layout.store.encoding.words ≤ _ ∧
    layout.result.encoding.words + layout.store.encoding.words ≤ _ ∧
    1 + max (layout.result.encoding.words + layout.store.encoding.words)
      (layout.request.encoding.words + layout.state.encoding.words + layout.store.encoding.words) ≤ _ ∧
    1 + max (1 + max layout.result.encoding.words (layout.request.encoding.words + layout.state.encoding.words) + layout.store.encoding.words)
      (layout.request.encoding.words + layout.state.encoding.words + layout.store.encoding.words) ≤ _
  dsimp only [CallerStep.width]
  omega

theorem done_time (value : B × S) : (done layout).time value ≤ 36 * CallerStep.width layout := by
  have tagged := inl_time layout.result (CallerStep.pending layout) layout.width (CallerStep.next layout).fits value.1
  have copied := (inlRealizer .unit (by decide) layout.result (CallerStep.pending layout) layout.width (CallerStep.next layout).fits).retain_time_unit_le
    layout.store layout.width (by
      have := (inl_names layout.result (CallerStep.pending layout) layout.width (CallerStep.next layout).fits).buffers
      dsimp only [Realizer.savedBuffer]
      have := layout.width
      omega) (result layout).fits (CallerStep.output layout).fits value
  have bounds := sizes layout
  change _ ≤ 8 * (CallerStep.next layout).encoding.words at tagged
  change _ ≤ _ + 8 * layout.result.encoding.words + 8 * (CallerStep.next layout).encoding.words +
    12 * layout.store.encoding.words at copied
  exact copied.trans (by omega)

theorem stop_time (value : Frame C Q S) : (stop layout).time value ≤ 36 * CallerStep.width layout := by
  have tagged := inr_time layout.result (CallerStep.pending layout) layout.width (CallerStep.next layout).fits value.1
  have copied := (inrRealizer .unit (by decide) layout.result (CallerStep.pending layout) layout.width (CallerStep.next layout).fits).retain_time_unit_le
    layout.store layout.width (by
      have := (inr_names layout.result (CallerStep.pending layout) layout.width (CallerStep.next layout).fits).buffers
      dsimp only [Realizer.savedBuffer]
      have := layout.width
      omega) (CallerStep.frame layout).fits (CallerStep.output layout).fits value
  have bounds := sizes layout
  change _ ≤ 8 * (CallerStep.next layout).encoding.words at tagged
  change _ ≤ _ + 8 * (CallerStep.pending layout).encoding.words + 8 * (CallerStep.next layout).encoding.words +
    12 * layout.store.encoding.words at copied
  exact copied.trans (by omega)

theorem done_words : descriptionWords (done layout).code ≤ 117 * CallerStep.width layout + 53 := by
  have tagged := inl_words layout.result (CallerStep.pending layout) layout.width (CallerStep.next layout).fits
  have copied := (inlRealizer .unit (by decide) layout.result (CallerStep.pending layout) layout.width (CallerStep.next layout).fits).retain_descriptionWords_le
    (by decide) layout.store layout.width (by
      have := (inl_names layout.result (CallerStep.pending layout) layout.width (CallerStep.next layout).fits).buffers
      dsimp only [Realizer.savedBuffer]
      have := layout.width
      omega) (result layout).fits (CallerStep.output layout).fits
  have bounds := sizes layout
  change _ ≤ 26 * (CallerStep.next layout).encoding.words + 14 at tagged
  change _ ≤ _ + 26 * layout.result.encoding.words + 26 * (CallerStep.next layout).encoding.words +
    39 * layout.store.encoding.words + 39 at copied
  exact copied.trans (by omega)

theorem stop_words : descriptionWords (stop layout).code ≤ 117 * CallerStep.width layout + 53 := by
  have tagged := inr_words layout.result (CallerStep.pending layout) layout.width (CallerStep.next layout).fits
  have copied := (inrRealizer .unit (by decide) layout.result (CallerStep.pending layout) layout.width (CallerStep.next layout).fits).retain_descriptionWords_le
    (by decide) layout.store layout.width (by
      have := (inr_names layout.result (CallerStep.pending layout) layout.width (CallerStep.next layout).fits).buffers
      dsimp only [Realizer.savedBuffer]
      have := layout.width
      omega) (CallerStep.frame layout).fits (CallerStep.output layout).fits
  have bounds := sizes layout
  change _ ≤ 26 * (CallerStep.next layout).encoding.words + 14 at tagged
  change _ ≤ _ + 26 * (CallerStep.pending layout).encoding.words + 26 * (CallerStep.next layout).encoding.words +
    39 * layout.store.encoding.words + 39 at copied
  exact copied.trans (by omega)

theorem distribute_time (value : Packet C Q B S) : (distribute layout).time value ≤ 24 * CallerStep.width layout + 2 := by
  have bound := SumContext.time layout.result (CallerStep.pending layout) layout.store layout.width (CallerStep.output layout).fits value
  have size := (sizes layout).2.2.2.2.2.2.2.2.1
  exact bound.trans (by change 24 * (CallerStep.output layout).encoding.words + 2 ≤ _; omega)

theorem distribute_words : descriptionWords (distribute layout).code ≤ 156 * CallerStep.width layout + 95 := by
  have bound := SumContext.words layout.result (CallerStep.pending layout) layout.store layout.width (CallerStep.output layout).fits
  have size := (sizes layout).2.2.2.2.2.2.2.2.1
  exact bound.trans (by change 156 * (CallerStep.output layout).encoding.words + 95 ≤ _; omega)

theorem route_time (value : Packet C Q B S) : (route layout).time value ≤ 84 * CallerStep.width layout + 4 := by
  have copied := distribute_time layout value
  have bounds := sizes layout
  rcases value with ⟨value | pending, saved⟩
  · have finished := done_time layout (value, saved)
    have tagged := inl_time (CallerStep.output layout) (CallerStep.frame layout) layout.width (iteration layout).fits
      (returned (C := C) (Q := Q) (value, saved))
    change _ + (1 + (1 + ((selectSlice (w := w) 1 (result layout).encoding.words).staticTime .unit + (_ + _)))) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, CostModel.unit]
    dsimp only [CostModel.unit] at tagged
    change _ ≤ 8 * (iteration layout).encoding.words at tagged
    omega
  · have tagged := inr_time (CallerStep.output layout) (CallerStep.frame layout) layout.width (iteration layout).fits (pending, saved)
    change _ + (1 + (1 + ((selectSlice (w := w) 1 (CallerStep.frame layout).encoding.words).staticTime .unit + _))) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, CostModel.unit]
    dsimp only [CostModel.unit] at tagged
    change _ ≤ 8 * (iteration layout).encoding.words at tagged
    omega

theorem route_words : descriptionWords (route layout).code ≤ 430 * CallerStep.width layout + 216 := by
  have copied := distribute_words layout
  have finished := done_words layout
  have left := inl_words (CallerStep.output layout) (CallerStep.frame layout) layout.width (iteration layout).fits
  have right := inr_words (CallerStep.output layout) (CallerStep.frame layout) layout.width (iteration layout).fits
  have bounds := sizes layout
  change _ ≤ 26 * (iteration layout).encoding.words + 14 at left right
  change descriptionWords (_ ;; Dispatch.code (_ ;; _) _ (result layout).encoding.words (CallerStep.frame layout).encoding.words) ≤ _
  rw [descriptionWords_seq, Dispatch.code_descriptionWords, descriptionWords_seq]
  omega

theorem done_names : NamesAccounted (done layout).code 3 :=
  Retain.names (inl_names layout.result (CallerStep.pending layout) layout.width (CallerStep.next layout).fits).accounted _ _ _
theorem stop_names : NamesAccounted (stop layout).code 3 :=
  Retain.names (inr_names layout.result (CallerStep.pending layout) layout.width (CallerStep.next layout).fits).accounted _ _ _
theorem distribute_names : NamesAccounted (distribute layout).code 3 :=
  SumContext.names layout.result (CallerStep.pending layout) layout.store layout.width (CallerStep.output layout).fits
theorem route_names : NamesAccounted (route layout).code 3 :=
  (distribute_names layout).seq (Dispatch.names
    ((done_names layout).seq (inl_names _ _ layout.width (iteration layout).fits).accounted)
    (inr_names _ _ layout.width (iteration layout).fits).accounted _ _)

end Signatures.Runtime.CaliperBackend.CallerControl
