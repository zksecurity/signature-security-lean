import Proofs.Runtime.Caliper.AttachStepBounds

/-! Complete positional row assembly. An accepted staged fold grows its row
buffer and pads every early exit. A final executed reversal restores key order.
Only the recorded key list is traversed; extra coefficients create no rows. -/

namespace Signatures.Runtime.CaliperBackend.AttachRows
open Caliper BoundedSource
variable {w : Nat} {K V : Type} (layout : Layouts w K V)

def Layouts.result := layout.states (Fin.last layout.capacity)
def Layouts.output := layout.rows (Fin.last layout.capacity)

def counterView (i : Fin (layout.capacity + 1)) :
    Implementation .unit (layout.counter i) (layout.counter (Fin.last layout.capacity)) id :=
  Implementation.view (width_pos layout.wordFits) (by
    intro value valid
    have bound : value < i.val + 1 := valid
    change value < layout.capacity + 1
    omega) (fun _ => rfl)
def stopCounter (i : Fin (layout.capacity + 1)) :
    Implementation .unit (layout.states i) (layout.counter (Fin.last layout.capacity)) Prod.fst :=
  (Implementation.first (by decide) (layout.counter i) (layout.rows i) layout.wordFits (layout.states i).representation.fits).then
    (counterView layout i)
def stopRows (i : Fin (layout.capacity + 1)) : Implementation .unit (layout.states i) layout.output Prod.snd :=
  (Implementation.second (by decide) (layout.counter i) (layout.rows i) layout.wordFits (layout.states i).representation.fits).then
    (ListReverse.stop layout.reversal i)
theorem stopCounter_buffers (i : Fin (layout.capacity + 1)) : (stopCounter layout i).program.code.memBound ≤ 2 :=
  max_le (Implementation.first_buffers _ _ _ _ _) (show (0 : Nat) ≤ 2 by decide)
theorem stopRows_buffers (i : Fin (layout.capacity + 1)) : (stopRows layout i).program.code.memBound ≤ 2 :=
  max_le (Implementation.second_buffers _ _ _ _ _) (ListReverse.stop_buffers _ _)
def stop (i : Fin (layout.capacity + 1)) : Implementation .unit (layout.states i) layout.result id :=
  (stopCounter layout i).pair (stopRows layout i) (by decide) layout.wordFits
    (layout.nameFits _ (stopCounter_buffers layout i) (by decide)) (layout.nameFits _ (stopRows_buffers layout i) (by decide))
    (layout.fits_of_le (by have := layout.stage_sizes i; omega))
    (layout.fits_of_le (by rw [Layouts.counter_words]; have := layout.stage_sizes i; dsimp only [Layouts.width] at *; omega))
    layout.result.representation.fits
theorem stop_buffers (i : Fin (layout.capacity + 1)) : (stop layout i).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 2) _ _ _ _ _ _ _ _
    (stopCounter_buffers layout i) (stopRows_buffers layout i)

def compiled := StagedFold.compile (by decide) layout.key layout.result layout.env layout.wordFits step
  layout.capacity layout.states layout.countFits layout.argFits layout.frameFits (fun i => some (body layout i)) (stop layout)
theorem accepted : (compiled layout).isSome := by
  obtain ⟨implementation, equal, _⟩ := StagedFold.accept (by decide) layout.key layout.result layout.env layout.wordFits step
    layout.capacity layout.states layout.countFits layout.argFits layout.frameFits (body layout) (stop layout)
    9 3 (body_buffers layout) (stop_buffers layout) (by have := layout.wordFits; omega)
  rw [compiled, equal]
  rfl
def loop : Implementation .unit layout.frame layout.result (FoldImplementation.sourceFold step) :=
  (compiled layout).get (accepted layout)
theorem loop_buffers : (loop layout).program.code.memBound ≤ 10 := by
  obtain ⟨implementation, equal, bound⟩ := StagedFold.accept (by decide) layout.key layout.result layout.env layout.wordFits step
    layout.capacity layout.states layout.countFits layout.argFits layout.frameFits (body layout) (stop layout)
    9 3 (body_buffers layout) (stop_buffers layout) (by have := layout.wordFits; omega)
  rw [show loop layout = implementation from Option.get_of_eq_some (accepted layout) equal]
  exact bound

def initial : (layout.states 0).Value := ⟨(0, []), by exact ⟨by change 0 < 1; decide, by simp [Layouts.rows, Layout.boundedList]⟩⟩
def initialState := Implementation.constant layout.input (layout.states 0) (initial layout) layout.wordFits
def inputKeys : Implementation .unit layout.input layout.keys Prod.fst :=
  Implementation.first (by decide) layout.keys layout.env layout.wordFits layout.input.representation.fits
def inputEnv : Implementation .unit layout.input layout.env Prod.snd :=
  Implementation.second (by decide) layout.keys layout.env layout.wordFits layout.input.representation.fits
theorem initialState_buffers : (initialState layout).program.code.memBound ≤ 2 := Implementation.constant_buffers _ _ _ _
theorem inputKeys_buffers : (inputKeys layout).program.code.memBound ≤ 2 := Implementation.first_buffers _ _ _ _ _
theorem inputEnv_buffers : (inputEnv layout).program.code.memBound ≤ 2 := Implementation.second_buffers _ _ _ _ _
def saved := (layout.states 0).prod layout.env (layout.fits_of_le (by have := layout.stage_sizes 0; have := layout.base_sizes; omega))
theorem saved_size : (saved layout).representation.encoding.words ≤ 2 * layout.width := by
  change (layout.states 0).representation.encoding.words + layout.env.representation.encoding.words ≤ _
  have := layout.stage_sizes 0; have := layout.base_sizes; omega
def prepareSaved : Implementation .unit layout.input (saved layout) (fun value => ((0, []), value.2)) :=
  (initialState layout).pair (inputEnv layout) (by decide) layout.wordFits
    (layout.nameFits _ (initialState_buffers layout) (by decide)) (layout.nameFits _ (inputEnv_buffers layout) (by decide))
    (layout.fits_of_le (by have := layout.base_sizes; omega))
    (layout.fits_of_le (by have := layout.stage_sizes 0; have := layout.base_sizes; omega))
    (saved layout).representation.fits
theorem prepareSaved_buffers : (prepareSaved layout).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 2) _ _ _ _ _ _ _ _
    (initialState_buffers layout) (inputEnv_buffers layout)
def prepare : Implementation .unit layout.input layout.frame (fun value => (value.1, (0, []), value.2)) :=
  (inputKeys layout).pair (prepareSaved layout) (by decide) layout.wordFits
    (layout.nameFits _ (inputKeys_buffers layout) (by decide)) (layout.nameFits _ (prepareSaved_buffers layout) (by decide))
    (layout.fits_of_le (by have := layout.base_sizes; omega))
    (layout.fits_of_le (by have := layout.base_sizes; omega)) layout.frame.representation.fits
theorem prepare_buffers : (prepare layout).program.code.memBound ≤ 4 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 3) _ _ _ _ _ _ _ _
    (inputKeys_buffers layout) (prepareSaved_buffers layout)
def finish : Implementation .unit layout.result layout.output (fun value => value.2.reverse) :=
  (Implementation.second (by decide) (layout.counter (Fin.last layout.capacity)) layout.output layout.wordFits layout.result.representation.fits).then
    (ListReverse.implementation layout.reversal)
theorem finish_buffers : (finish layout).program.code.memBound ≤ 3 :=
  max_le ((Implementation.second_buffers _ _ _ _ _).trans (by decide)) (ListReverse.buffers _)

theorem source_result (keys : List K) (default : V) (values : List V) :
    (FoldImplementation.sourceFold step (keys, (0, []), (default, values))).2.reverse =
      keys.mapIdx (fun n key => (key, (values[n]?).getD default)) := by
  change (keys.foldl (AGM.attachStep default values) (0, [])).2.reverse = _
  rw [AGM.attachStep_fold]
  simp
def implementation : Implementation .unit layout.input layout.output
    (fun value => value.1.mapIdx (fun n key => (key, (value.2.2[n]?).getD value.2.1))) :=
  (((prepare layout).then (loop layout)).then (finish layout)).castFunction (by
    funext value
    exact source_result value.1 value.2.1 value.2.2)
theorem buffers : (implementation layout).program.code.memBound ≤ 10 :=
  max_le (max_le ((prepare_buffers layout).trans (by decide)) (loop_buffers layout)) ((finish_buffers layout).trans (by decide))

end Signatures.Runtime.CaliperBackend.AttachRows
