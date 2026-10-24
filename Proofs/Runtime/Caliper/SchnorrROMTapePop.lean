import Proofs.Runtime.Caliper.SchnorrROMTapePopFold

/-! Complete executed first-family-cell removal. Both scan preparation and
restoration of the remaining tape's original order are included. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Pop
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : Layouts w F)

def inputTag : Constructed layout.resetInput layout.counter Prod.fst :=
  Constructed.first layout.counter layout.resetTail layout.wordFits layout.resetInput.representation.fits
def inputTail : Constructed layout.resetInput layout.resetTail Prod.snd :=
  Constructed.second layout.counter layout.resetTail layout.wordFits layout.resetInput.representation.fits
def inputFallback : Constructed layout.resetInput layout.entry (fun value => value.2.1) :=
  (inputTail layout).then (Constructed.first layout.entry (layout.list layout.capacity (by omega))
    layout.wordFits layout.resetTail.representation.fits)
def inputList : Constructed layout.resetInput (layout.list layout.capacity (by omega)) (fun value => value.2.2) :=
  (inputTail layout).then (Constructed.second layout.entry (layout.list layout.capacity (by omega))
    layout.wordFits layout.resetTail.representation.fits)
def empty : Constructed layout.resetInput (layout.list 0 (by omega)) (fun _ => []) :=
  Constructed.constant layout.resetInput (layout.list 0 (by omega)) ⟨[], by exact ⟨by simp, by simp⟩⟩ layout.wordFits
def initialPayload : Constructed layout.resetInput (payload layout 0 (by omega)) (fun value => (value.2.1, [])) :=
  (inputFallback layout).pair (empty layout) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 2 < _; have := layout.wordFits; omega)
    layout.resetDuplicate
    (layout.fits_of_le (by have := layout.entry_le; have := layout.resetInput_le; omega))
    (payload layout 0 (by omega)).representation.fits
def initialState : Constructed layout.resetInput (states layout 0) (fun value => (false, value.2.1, [])) :=
  (Constructed.constant layout.resetInput layout.boolean ⟨false, trivial⟩ layout.wordFits).pair
    (initialPayload layout) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 3 < _; have := layout.wordFits; omega)
    layout.resetDuplicate
    (layout.fits_of_le (by rw [Layouts.boolean_words]; have := layout.resetInput_le; unfold Layouts.width at *; omega))
    (states layout 0).representation.fits
def initialEnv : Constructed layout.resetInput (tail layout 0) (fun value => ((false, value.2.1, []), value.1)) :=
  (initialState layout).pair (inputTag layout) layout.wordFits
    (by change 4 < _; have := layout.wordFits; omega) (by change 2 < _; have := layout.wordFits; omega)
    layout.resetDuplicate
    (layout.fits_of_le (by
      have bound : (states layout 0).representation.encoding.words ≤ layout.width := state_le layout 0 (by omega)
      have := layout.resetInput_le; omega))
    (tail layout 0).representation.fits
def prepare : Constructed layout.resetInput (frame layout) (fun value => (value.2.2, (false, value.2.1, []), value.1)) :=
  (inputList layout).pair (initialEnv layout) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 5 < _; have := layout.wordFits; omega)
    layout.resetDuplicate
    (layout.fits_of_le (by have := layout.list_le layout.capacity (by omega); have := layout.resetInput_le; omega))
    (frame layout).representation.fits

def resultFlag : Constructed (state layout layout.capacity (by omega)) layout.boolean Prod.fst :=
  Constructed.first layout.boolean (payload layout layout.capacity (by omega)) layout.wordFits
  (state layout layout.capacity (by omega)).representation.fits
def resultPayload : Constructed (state layout layout.capacity (by omega)) (payload layout layout.capacity (by omega)) Prod.snd :=
  Constructed.second layout.boolean (payload layout layout.capacity (by omega)) layout.wordFits
  (state layout layout.capacity (by omega)).representation.fits
def resultAnswer : Constructed (state layout layout.capacity (by omega)) layout.entry (fun value => value.2.1) :=
  (resultPayload layout).then
  (Constructed.first layout.entry (layout.list layout.capacity (by omega)) layout.wordFits
    (payload layout layout.capacity (by omega)).representation.fits)
def resultRest : Constructed (state layout layout.capacity (by omega)) (layout.list layout.capacity (by omega))
    (fun value => value.2.2.reverse) := ((resultPayload layout).then
  (Constructed.second layout.entry (layout.list layout.capacity (by omega)) layout.wordFits
    (payload layout layout.capacity (by omega)).representation.fits)).then (Constructed.reverse (reversal layout))
def reversedPayload : Constructed (state layout layout.capacity (by omega)) (payload layout layout.capacity (by omega))
    (fun value => (value.2.1, value.2.2.reverse)) :=
  (resultAnswer layout).pair (resultRest layout) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 3 < _; have := layout.wordFits; omega)
    (layout.fits_of_le (by have := state_le layout layout.capacity (by omega); omega))
    (layout.fits_of_le (by have := layout.entry_le; have := state_le layout layout.capacity (by omega); omega))
    (payload layout layout.capacity (by omega)).representation.fits
def finish : Constructed (state layout layout.capacity (by omega)) (state layout layout.capacity (by omega))
    (fun value => (value.1, value.2.1, value.2.2.reverse)) :=
  (resultFlag layout).pair (reversedPayload layout) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 4 < _; have := layout.wordFits; omega)
    (layout.fits_of_le (by have := state_le layout layout.capacity (by omega); omega))
    (layout.fits_of_le (by
      rw [Layouts.boolean_words]; have := state_le layout layout.capacity (by omega); unfold Layouts.width at *; omega))
    (state layout layout.capacity (by omega)).representation.fits

def constructed : Constructed layout.resetInput (state layout layout.capacity (by omega))
    (fun value => Schnorr.SeedTape.pop value.1 value.2.1 value.2.2) :=
  (((prepare layout).then (loop layout)).then (finish layout)).castFunction (by
    funext value
    simpa only [Function.comp_apply, FoldImplementation.sourceFold, step, List.reverse_nil, List.nil_append] using
      Schnorr.SeedTape.popStep_result value.1 value.2.2 value.2.1 [])
def implementation := (constructed layout).implementation
theorem constructed_buffers : (constructed layout).buffers = 6 := rfl
theorem buffers : (implementation layout).program.code.memBound ≤ 6 := (constructed layout).buffers_le
theorem names (slots : Nat) : NamesAccounted (implementation layout).program.code slots := (constructed layout).names slots

theorem prepare_budget :
    (prepare layout).budget.time ≤ 800 * layout.width + 200 ∧
      (prepare layout).budget.words ≤ 3000 * layout.width + 2000 := by
  have b := layout.resetInput_le
  have t := layout.resetTail_le
  have e := layout.entry_le
  have l := layout.list_le layout.capacity (by omega)
  have reversedWidth : (reversal layout).list.representation.encoding.words ≤ layout.width := l
  have p := payload_le layout 0 (by omega)
  have s : (states layout 0).representation.encoding.words ≤ layout.width := state_le layout 0 (by omega)
  have env := tail_le layout 0
  dsimp only [prepare, initialEnv, initialState, initialPayload, empty, inputTag, inputList, inputTail, inputFallback,
    Constructed.pair, Constructed.then, Constructed.constant, Constructed.first, Constructed.second,
    Budget.pair, Budget.seq, Budget.storage]
  simp only [Layouts.counter_words, Layouts.boolean_words, Layouts.list_words, Nat.zero_mul, Nat.add_zero]
  rw [Layouts.list_words] at l
  constructor <;> omega
theorem finish_budget :
    (finish layout).budget.time ≤ 300 * layout.width + 100 + ListReverse.timeBudget (reversal layout) ∧
      (finish layout).budget.words ≤ 1000 * layout.width + 1000 + ListReverse.codeBudget (reversal layout) := by
  have s := state_le layout layout.capacity (by omega)
  have p := payload_le layout layout.capacity (by omega)
  have l := layout.list_le layout.capacity (by omega)
  have e := layout.entry_le
  dsimp only [finish, resultFlag, reversedPayload, resultAnswer, resultRest, resultPayload, Constructed.pair, Constructed.then,
    Constructed.first, Constructed.second, Constructed.reverse, Budget.pair, Budget.seq, Budget.storage]
  simp only [Layouts.boolean_words]
  constructor <;> omega

def timeBudget := 1200 * layout.width + 400 + (loopBudget layout).time + ListReverse.timeBudget (reversal layout)
def codeBudget := 4200 * layout.width + 3200 + (loopBudget layout).words + ListReverse.codeBudget (reversal layout)
theorem bounded : (implementation layout).BoundedBy (timeBudget layout) (codeBudget layout) := by
  apply (constructed layout).bounded.mono
  all_goals
    have := prepare_budget layout
    have := finish_budget layout
    dsimp only [constructed, Constructed.castFunction, Constructed.then, Budget.seq, loop, timeBudget, codeBudget]
    omega

theorem resources (tape : RandomTape w) (input : layout.resetInput.Value) (before : State w)
    (holds : layout.resetInput.representation.Holds input before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation layout).program.code before after
      ((implementation layout).program.time input) net peak ∧
      (state layout layout.capacity (by omega)).representation.Holds
        ⟨Schnorr.SeedTape.pop input.val.1 input.val.2.1 input.val.2.2, (implementation layout).preserves input.val input.property⟩ after ∧
      (implementation layout).program.time input ≤ timeBudget layout ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation layout).program.code before between ∨ between = after) →
        (staticWords (implementation layout).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation layout).program.code.memBound) ≤
            5 * codeBudget layout + registers + 3 * buffers + before.liveMem buffers + timeBudget layout := by
  obtain ⟨after, net, peak, execution, output, elapsed, memory⟩ :=
    (bounded layout).memoryBound (names layout 0) tape input before holds registers buffers initialRegisters initialBuffers
  exact ⟨after, net, peak, execution, output, elapsed, fun between visited => by simpa using (memory between visited).2.2.2⟩

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Pop
