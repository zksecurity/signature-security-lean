import Proofs.Runtime.Caliper.ChronologicalIndexStep
import Proofs.Runtime.Caliper.StagedFoldAcceptance

/-! A complete, costed chronological lookup. The scan runs over the stored
newest-first list and agrees with searching its reverse, without constructing
that reverse. No default key or payload is needed for an empty list. -/
namespace Signatures.Runtime.CaliperBackend.ChronologicalIndex
open Caliper BoundedSource
variable {w : Nat} {K V : Type} [DecidableEq K] (layout : Layouts w K V)

def stop (i : Fin (layout.capacity + 1)) : Constructed (layout.state i) layout.result id :=
  (Constructed.identity (layout.state i) (width_pos layout.wordFits)).viewOutput layout.result
    (fun value valid => ⟨valid.1, by have count := valid.2; change value.2 < i.val + 1 at count; change value.2 < layout.capacity + 1; omega⟩)
    (fun _ => rfl)
def compiled := StagedFold.compile (by decide) layout.entry layout.result layout.key layout.wordFits step
  layout.capacity layout.state (by have := layout.countFits; omega) layout.argFits layout.frameFits
    (fun i => some (body layout i).implementation) (fun i => (stop layout i).implementation)
theorem accepted : (compiled layout).isSome := by
  obtain ⟨implementation, equal, _⟩ := StagedFold.accept (by decide) layout.entry layout.result layout.key layout.wordFits step
    layout.capacity layout.state (by have := layout.countFits; omega) layout.argFits layout.frameFits
    (fun i => (body layout i).implementation) (fun i => (stop layout i).implementation) 6 0
    (fun i => by simpa only [body_buffers] using (body layout i).buffers_le)
    (fun i => (stop layout i).buffers_le) (by have := layout.wordFits; omega)
  rw [compiled, equal]
  rfl
def loop : Implementation .unit layout.frame layout.result (FoldImplementation.sourceFold step) :=
  (compiled layout).get (accepted layout)
theorem loop_buffers : (loop layout).program.code.memBound ≤ 7 := by
  obtain ⟨implementation, equal, bounded⟩ := StagedFold.accept (by decide) layout.entry layout.result layout.key layout.wordFits step
    layout.capacity layout.state (by have := layout.countFits; omega) layout.argFits layout.frameFits
    (fun i => (body layout i).implementation) (fun i => (stop layout i).implementation) 6 0
    (fun i => by simpa only [body_buffers] using (body layout i).buffers_le)
    (fun i => (stop layout i).buffers_le) (by have := layout.wordFits; omega)
  rw [show loop layout = implementation from Option.get_of_eq_some (accepted layout) equal]
  exact bounded
def loopTime := StagedFold.timeBudget layout.width (600 * layout.width + 100) 0 layout.capacity
def loopWords := StagedFold.codeBudget layout.width (2000 * layout.width + 1000) 1 layout.capacity
theorem loop_bounded : (loop layout).BoundedBy (loopTime layout) (loopWords layout) :=
  StagedFold.compile_boundedBy layout.entry layout.result layout.key layout.wordFits step
    layout.capacity layout.state (by have := layout.countFits; omega) layout.argFits layout.frameFits
    (fun i => some (body layout i).implementation) (fun i => (stop layout i).implementation)
    layout.width (600 * layout.width + 100) (2000 * layout.width + 1000) 0 1
    (layout.sizes 0).2.1 (layout.sizes 0).1
    (fun i => by rw [(layout.sizes i).2.2.2.2.1]; unfold Layouts.width; omega)
    (fun i implementation equal => Option.some.inj equal ▸
      (body layout i).bounded.mono (body_budget layout i).1 (body_budget layout i).2)
    (fun i => (stop layout i).bounded) (loop layout) (Option.eq_some_of_isSome (accepted layout))
theorem loop_names (slots : Nat) : NamesAccounted (loop layout).program.code slots :=
  StagedFold.compile_names layout.entry layout.result layout.key layout.wordFits step
    layout.capacity layout.state (by have := layout.countFits; omega) layout.argFits layout.frameFits
    (fun i => some (body layout i).implementation) (fun i => (stop layout i).implementation) slots
    (fun i implementation equal => Option.some.inj equal ▸ (body layout i).names slots)
    (fun i => (stop layout i).names slots) (loop layout) (Option.eq_some_of_isSome (accepted layout))

def inputKey : Constructed layout.input layout.key Prod.fst :=
  Constructed.first layout.key layout.list layout.wordFits layout.input.representation.fits
def inputList : Constructed layout.input layout.list Prod.snd :=
  Constructed.second layout.key layout.list layout.wordFits layout.input.representation.fits
def initial : Constructed layout.input (layout.state 0) (fun _ => (false, 0)) :=
  Constructed.constant layout.input (layout.state 0) ⟨(false, 0), trivial, by change 0 < 1; decide⟩ layout.wordFits
def initialTail : Constructed layout.input (layout.stateTail 0) (fun value => ((false, 0), value.1)) :=
  (initial layout).pair (inputKey layout) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 2 < _; have := layout.wordFits; omega)
    (layout.fits (by have := layout.sizes 0; omega))
    (layout.fits (by have := layout.sizes 0; change 2 + _ ≤ _; unfold Layouts.width at *; omega))
    (layout.stateTail 0).representation.fits
def prepare : Constructed layout.input layout.frame (fun value => (value.2, (false, 0), value.1)) :=
  (inputList layout).pair (initialTail layout) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 3 < _; have := layout.wordFits; omega)
    (layout.fits (by have := layout.sizes 0; omega))
    (layout.fits (by have := layout.sizes 0; omega)) layout.frame.representation.fits
omit [DecidableEq K] in
theorem prepare_buffers : (prepare layout).buffers = 4 := rfl
omit [DecidableEq K] in
theorem prepare_budget : (prepare layout).budget.time ≤ 600 * layout.width + 200 ∧
    (prepare layout).budget.words ≤ 2000 * layout.width + 1000 := by
  have sizes := layout.sizes 0
  have positive : 4 ≤ layout.width := by unfold Layouts.width; omega
  dsimp only [prepare, inputList, initialTail, initial, inputKey, Constructed.second, Constructed.pair,
    Constructed.constant, Constructed.first, Budget.pair, Budget.storage]
  change 8 * layout.list.representation.encoding.words +
    (8 * 2 + 8 * layout.key.representation.encoding.words + 52 * layout.input.representation.encoding.words + 36 * 2 +
      16 * layout.key.representation.encoding.words) + 52 * layout.input.representation.encoding.words +
      36 * layout.list.representation.encoding.words + 16 * (layout.stateTail 0).representation.encoding.words ≤ _ ∧ _
  simp only [sizes.2.2.2.2.1]
  exact ⟨by omega, by omega⟩

def implementation : Implementation .unit layout.input layout.result value :=
  ((prepare layout).implementation.then (loop layout)).castFunction (funext fun input => fold_value input.1 input.2)
def timeBudget := 600 * layout.width + 200 + loopTime layout
def codeBudget := 2000 * layout.width + 1001 + loopWords layout
theorem bounded : (implementation layout).BoundedBy (timeBudget layout) (codeBudget layout) := by
  apply (((prepare layout).bounded.mono (prepare_budget layout).1 (prepare_budget layout).2).then (loop_bounded layout)).castFunction
    (funext fun input => fold_value input.1 input.2) |>.mono
  · exact le_rfl
  · unfold codeBudget; omega
theorem buffers : (implementation layout).program.code.memBound ≤ 7 :=
  max_le ((prepare layout).buffers_le.trans (by rw [prepare_buffers]; decide)) (loop_buffers layout)
theorem names (slots : Nat) : NamesAccounted (implementation layout).program.code slots :=
  ((prepare layout).names slots).seq (loop_names layout slots)
def constructed : Constructed layout.input layout.result value where
  implementation := implementation layout
  budget := ⟨timeBudget layout, codeBudget layout⟩
  bounded := bounded layout
  buffers := 7
  buffers_le := buffers layout
  names := names layout

end Signatures.Runtime.CaliperBackend.ChronologicalIndex
