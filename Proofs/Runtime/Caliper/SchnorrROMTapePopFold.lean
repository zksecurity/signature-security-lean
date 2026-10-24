import Proofs.Runtime.Caliper.SchnorrROMTapePopStep

/-! Accepted staged removal scan with derived bounds for every body, padding
exit and stored branch. The runtime family tag is retained across the scan. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Pop
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : Layouts w F)

def stopFlag (i : Fin (layout.capacity + 1)) : Constructed (states layout i) layout.boolean Prod.fst :=
  Constructed.first layout.boolean (payload layout i.val (by omega)) layout.wordFits (states layout i).representation.fits
def stopPrior (i : Fin (layout.capacity + 1)) : Constructed (states layout i) (payload layout i.val (by omega)) Prod.snd :=
  Constructed.second layout.boolean (payload layout i.val (by omega)) layout.wordFits (states layout i).representation.fits
def stopAnswer (i : Fin (layout.capacity + 1)) : Constructed (states layout i) layout.entry (fun value => value.2.1) :=
  (stopPrior layout i).then (Constructed.first layout.entry (layout.list i.val (by omega))
    layout.wordFits (payload layout i.val (by omega)).representation.fits)
def stopRest (i : Fin (layout.capacity + 1)) : Constructed (states layout i) (layout.list layout.capacity (by omega))
    (fun value => value.2.2) :=
  ((stopPrior layout i).then (Constructed.second layout.entry (layout.list i.val (by omega))
    layout.wordFits (payload layout i.val (by omega)).representation.fits)).then
      (Constructed.widen layout.entry i.val layout.capacity (by omega) layout.wordFits
        (by have := layout.countFits; omega) (layout.list layout.capacity (by omega)).representation.fits)
def stopPayload (i : Fin (layout.capacity + 1)) : Constructed (states layout i) (payload layout layout.capacity (by omega)) Prod.snd :=
  (stopAnswer layout i).pair (stopRest layout i) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 2 < _; have := layout.wordFits; omega)
    (layout.fits_of_le (by
      have bound : (states layout i).representation.encoding.words ≤ layout.width := state_le layout i.val (by omega)
      omega))
    (layout.fits_of_le (by
      have bound : (states layout i).representation.encoding.words ≤ layout.width := state_le layout i.val (by omega)
      have := layout.entry_le; omega))
    (payload layout layout.capacity (by omega)).representation.fits
def stop (i : Fin (layout.capacity + 1)) : Constructed (states layout i) (state layout layout.capacity (by omega)) id :=
  (stopFlag layout i).pair (stopPayload layout i) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 3 < _; have := layout.wordFits; omega)
    (layout.fits_of_le (by
      have bound : (states layout i).representation.encoding.words ≤ layout.width := state_le layout i.val (by omega)
      omega))
    (layout.fits_of_le (by
      have bound : (states layout i).representation.encoding.words ≤ layout.width := state_le layout i.val (by omega)
      rw [Layouts.boolean_words]; unfold Layouts.width at *; omega))
    (state layout layout.capacity (by omega)).representation.fits
theorem stop_buffers (i : Fin (layout.capacity + 1)) : (stop layout i).buffers = 4 := rfl
theorem stop_budget (i : Fin (layout.capacity + 1)) :
    (stop layout i).budget.time ≤ 600 * layout.width + 100 ∧
      (stop layout i).budget.words ≤ 2000 * layout.width + 1000 := by
  have s : (states layout i).representation.encoding.words ≤ layout.width := state_le layout i.val (by omega)
  have p := payload_le layout i.val (by omega)
  have p' := payload_le layout layout.capacity (by omega)
  have l := layout.list_le i.val (by omega)
  have l' := layout.list_le layout.capacity (by omega)
  have encodedRest := l'
  have e := layout.entry_le
  dsimp only [stop, stopPayload, stopAnswer, stopRest, stopPrior, stopFlag, Constructed.pair,
    Constructed.then, Constructed.first, Constructed.second, Constructed.widen, Budget.pair, Budget.seq, Budget.storage]
  simp only [Layouts.boolean_words]
  change 1 + layout.capacity * layout.entry.representation.encoding.words ≤ layout.width at l'
  constructor <;> omega
theorem stop_bounded (i : Fin (layout.capacity + 1)) : (stop layout i).implementation.BoundedBy
    (600 * layout.width + 100) (2000 * layout.width + 1000) :=
  (stop layout i).bounded.mono (stop_budget layout i).1 (stop_budget layout i).2

def compiled := StagedFold.compile (by decide) layout.entry (state layout layout.capacity (by omega)) layout.counter
  layout.wordFits step layout.capacity (states layout) (by have := layout.countFits; omega)
  (argFits layout) (frameFits layout) (fun i => some (body layout i).implementation) (fun i => (stop layout i).implementation)
theorem accepted : (compiled layout).isSome := by
  obtain ⟨implementation, equal, _⟩ := StagedFold.accept (by decide) layout.entry (state layout layout.capacity (by omega))
    layout.counter layout.wordFits step layout.capacity (states layout) (by have := layout.countFits; omega)
    (argFits layout) (frameFits layout) (fun i => (body layout i).implementation) (fun i => (stop layout i).implementation)
    5 4 (fun i => (body_buffers layout i) ▸ (body layout i).buffers_le)
    (fun i => (stop_buffers layout i) ▸ (stop layout i).buffers_le) (by have := layout.wordFits; omega)
  rw [compiled, equal]; rfl
def loopImplementation := (compiled layout).get (accepted layout)
theorem loop_buffers : (loopImplementation layout).program.code.memBound ≤ 6 := by
  obtain ⟨implementation, equal, bound⟩ := StagedFold.accept (by decide) layout.entry (state layout layout.capacity (by omega))
    layout.counter layout.wordFits step layout.capacity (states layout) (by have := layout.countFits; omega)
    (argFits layout) (frameFits layout) (fun i => (body layout i).implementation) (fun i => (stop layout i).implementation)
    5 4 (fun i => (body_buffers layout i) ▸ (body layout i).buffers_le)
    (fun i => (stop_buffers layout i) ▸ (stop layout i).buffers_le) (by have := layout.wordFits; omega)
  rw [show loopImplementation layout = implementation from Option.get_of_eq_some (accepted layout) equal]
  exact bound
def loopBudget : Budget := .stagedFold layout.width layout.capacity
  ⟨3000 * layout.width + 500, 12000 * layout.width + 6000⟩
  ⟨600 * layout.width + 100, 2000 * layout.width + 1000⟩
def loop : Constructed (frame layout) (state layout layout.capacity (by omega)) (FoldImplementation.sourceFold step) where
  implementation := loopImplementation layout
  budget := loopBudget layout
  bounded := StagedFold.compile_boundedBy layout.entry (state layout layout.capacity (by omega)) layout.counter layout.wordFits step
    layout.capacity (states layout) (by have := layout.countFits; omega) (argFits layout) (frameFits layout)
    (fun i => some (body layout i).implementation) (fun i => (stop layout i).implementation)
    layout.width (3000 * layout.width + 500) (12000 * layout.width + 6000) (600 * layout.width + 100) (2000 * layout.width + 1000)
    layout.entry_le (by rw [Layouts.counter_words]; unfold Layouts.width; omega)
    (fun i => state_le layout i.val (by omega))
    (fun i implementation equal => Option.some.inj equal ▸ body_bounded layout i) (stop_bounded layout)
    (loopImplementation layout) (Option.eq_some_of_isSome (accepted layout))
  buffers := 6
  buffers_le := loop_buffers layout
  names slots := StagedFold.compile_names layout.entry (state layout layout.capacity (by omega)) layout.counter layout.wordFits step
    layout.capacity (states layout) (by have := layout.countFits; omega) (argFits layout) (frameFits layout)
    (fun i => some (body layout i).implementation) (fun i => (stop layout i).implementation) slots
    (fun i implementation equal => Option.some.inj equal ▸ (body layout i).names slots)
    (fun i => (stop layout i).names slots) (loopImplementation layout) (Option.eq_some_of_isSome (accepted layout))

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Pop
