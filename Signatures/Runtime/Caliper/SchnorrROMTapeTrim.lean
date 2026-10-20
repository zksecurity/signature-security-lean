import Signatures.Runtime.Caliper.SchnorrROMTapeTrimBounds

/-! The complete executed trim scan. Short input tapes use an executed padding
conversion; the unrolled scan is bounded by retained tape capacity. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : Layouts w F)

def stopCount (i : Fin (layout.capacity + 1)) : Implementation .unit (layout.states i) layout.counter Prod.fst :=
  Implementation.first (by decide) layout.counter (layout.list i.val (by omega)) layout.wordFits (layout.states i).representation.fits
def stopList (i : Fin (layout.capacity + 1)) : Implementation .unit (layout.states i)
    (layout.list layout.capacity (by omega)) Prod.snd :=
  (Implementation.second (by decide) layout.counter (layout.list i.val (by omega)) layout.wordFits
    (layout.states i).representation.fits).then
    (ListData.widen .unit (by decide) layout.entry i.val layout.capacity (by omega) layout.wordFits
      (by have := layout.countFits; omega) (layout.list layout.capacity (by omega)).representation.fits)
theorem stopCount_buffers (i : Fin (layout.capacity + 1)) : (stopCount layout i).program.code.memBound ≤ 2 :=
  Implementation.first_buffers _ _ _ _ _
theorem stopList_buffers (i : Fin (layout.capacity + 1)) : (stopList layout i).program.code.memBound ≤ 2 :=
  max_le (Implementation.second_buffers _ _ _ _ _)
    ((Assembly.code_names _ 1 ((Assembly.sourcesBound_append _ _ _).mpr
      ⟨Assembly.sourcesBound_reads _ _ _ _ (by decide), Assembly.sourcesBound_replicate _ _ _⟩)).2)
def stop (i : Fin (layout.capacity + 1)) :
    Implementation .unit (layout.states i) (layout.state layout.capacity (by omega)) id :=
  (stopCount layout i).pair (stopList layout i) (by decide) layout.wordFits
    (layout.nameFits _ (stopCount_buffers layout i) (by decide))
    (layout.nameFits _ (stopList_buffers layout i) (by decide))
    (layout.fits_of_le (by
      have size : (layout.states i).representation.encoding.words ≤ layout.width := layout.state_le i.val (by omega)
      omega))
    (layout.fits_of_le (by
      have size : (layout.states i).representation.encoding.words ≤ layout.width := layout.state_le i.val (by omega)
      change 1 + _ ≤ _; unfold Layouts.width at *; omega))
    (layout.state layout.capacity (by omega)).representation.fits
theorem stop_buffers (i : Fin (layout.capacity + 1)) : (stop layout i).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 2) _ _ _ _ _ _ _ _
    (stopCount_buffers layout i) (stopList_buffers layout i)
theorem stop_bounded (i : Fin (layout.capacity + 1)) :
    (stop layout i).BoundedBy (84 * layout.width + 44) (273 * layout.width + 311) := by
  have countBound : (stopCount layout i).BoundedBy 8 40 := Implementation.first_boundedBy _ _ _ _
  have listBound : (stopList layout i).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
    apply ((Implementation.second_boundedBy _ _ _ _).then (ListData.widen_boundedBy _ _ _ _ _ _ _)).mono
    · change 8 * (1 + i.val * layout.entry.representation.encoding.words) +
        8 * (1 + layout.capacity * layout.entry.representation.encoding.words) ≤ _
      have := layout.list_le i.val (by omega)
      have := layout.list_le layout.capacity (by omega)
      rw [Layouts.list_words] at *
      omega
    · change 26 * (1 + i.val * layout.entry.representation.encoding.words) + 14 +
        (26 * (1 + layout.capacity * layout.entry.representation.encoding.words) + 14) + 1 ≤ _
      have := layout.list_le i.val (by omega)
      have := layout.list_le layout.capacity (by omega)
      rw [Layouts.list_words] at *
      omega
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ countBound listBound).mono
  all_goals
    rw [Layouts.counter_words]
    have size := layout.state_le i.val (by omega)
    change (layout.states i).representation.encoding.words ≤ layout.width at size
    have := layout.list_le layout.capacity (by omega)
    omega
theorem stop_names (i : Fin (layout.capacity + 1)) (slots : Nat) :
    NamesAccounted (stop layout i).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (Implementation.first_names _ _ _ _ slots)
    ((Implementation.second_names _ _ _ _ slots).seq (ListData.widen_names _ _ _ _ _ _ _ slots))

def compiled := StagedFold.compile (by decide) layout.entry (layout.state layout.capacity (by omega)) layout.unit
  layout.wordFits step layout.capacity layout.states (by have := layout.countFits; omega)
  layout.argFits layout.frameFits (fun i => some (body layout i)) (stop layout)
theorem accepted : (compiled layout).isSome := by
  obtain ⟨implementation, equal, _⟩ := StagedFold.accept (by decide) layout.entry (layout.state layout.capacity (by omega))
    layout.unit layout.wordFits step layout.capacity layout.states (by have := layout.countFits; omega)
    layout.argFits layout.frameFits (body layout) (stop layout)
    4 3 (body_buffers layout) (stop_buffers layout) (by have := layout.wordFits; omega)
  rw [compiled, equal]; rfl
def loop : Implementation .unit layout.frame (layout.state layout.capacity (by omega)) (FoldImplementation.sourceFold step) :=
  (compiled layout).get (accepted layout)
theorem loop_buffers : (loop layout).program.code.memBound ≤ 5 := by
  obtain ⟨implementation, equal, bound⟩ := StagedFold.accept (by decide) layout.entry (layout.state layout.capacity (by omega))
    layout.unit layout.wordFits step layout.capacity layout.states (by have := layout.countFits; omega)
    layout.argFits layout.frameFits (body layout) (stop layout)
    4 3 (body_buffers layout) (stop_buffers layout) (by have := layout.wordFits; omega)
  rw [show loop layout = implementation from Option.get_of_eq_some (accepted layout) equal]
  exact bound

def loopTime : Nat := StagedFold.timeBudget layout.width (2700 * layout.width + 1000) (84 * layout.width + 44) layout.capacity
def loopWords : Nat := StagedFold.codeBudget layout.width (10000 * layout.width + 6000) (273 * layout.width + 311) layout.capacity
theorem loop_bounded : (loop layout).BoundedBy (loopTime layout) (loopWords layout) :=
  StagedFold.compile_boundedBy layout.entry (layout.state layout.capacity (by omega)) layout.unit layout.wordFits step
    layout.capacity layout.states (by have := layout.countFits; omega) layout.argFits layout.frameFits
    (fun i => some (body layout i)) (stop layout)
    layout.width (2700 * layout.width + 1000) (10000 * layout.width + 6000) (84 * layout.width + 44) (273 * layout.width + 311)
    layout.entry_le (by rw [Layouts.unit_words]; exact Nat.zero_le _)
    (fun i => layout.state_le i.val (by omega))
    (fun i implementation equal => Option.some.inj equal ▸ body_bounded layout i) (stop_bounded layout)
    (loop layout) (Option.eq_some_of_isSome (accepted layout))
theorem loop_names (slots : Nat) : NamesAccounted (loop layout).program.code slots :=
  StagedFold.compile_names layout.entry (layout.state layout.capacity (by omega)) layout.unit layout.wordFits step
    layout.capacity layout.states (by have := layout.countFits; omega) layout.argFits layout.frameFits
    (fun i => some (body layout i)) (stop layout) slots
    (fun i implementation equal => Option.some.inj equal ▸ body_names layout i slots)
    (fun i => stop_names layout i slots) (loop layout) (Option.eq_some_of_isSome (accepted layout))

theorem loop_source (slot : Nat) (saved : List (Schnorr.TapeCell F)) :
    FoldImplementation.sourceFold step (saved, (slot, []), ()) =
      ((Schnorr.SeedTape.trim 1 slot saved).1, (Schnorr.SeedTape.trim 1 slot saved).2.reverse) := by
  simpa only [FoldImplementation.sourceFold, step, List.append_nil] using Schnorr.SeedTape.trim_fold 1 slot saved []

end Signatures.Runtime.CaliperBackend.SchnorrROMTape
