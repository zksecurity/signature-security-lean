import Proofs.Runtime.Caliper.IndexStepNames

/-! Executed bounded-list indexing, from a runtime index, default and list to
the selected value. Preparation, the complete scan, and result projection all
execute Caliper instructions. The list capacity is independent of the index. -/

namespace Signatures.Runtime.CaliperBackend.ListIndex
open Caliper BoundedSource
variable {w : Nat} {V : Type} (layout : Layouts w V)

def inputIndex : Implementation .unit layout.input layout.counter Prod.fst :=
  Implementation.first (by decide) layout.counter layout.tail layout.wordFits layout.input.representation.fits
def inputTail : Implementation .unit layout.input layout.tail Prod.snd :=
  Implementation.second (by decide) layout.counter layout.tail layout.wordFits layout.input.representation.fits
def inputDefault : Implementation .unit layout.input layout.value (fun value => value.2.1) :=
  (inputTail layout).then (Implementation.first (by decide) layout.value layout.list layout.wordFits layout.tail.representation.fits)
def inputList : Implementation .unit layout.input layout.list (fun value => value.2.2) :=
  (inputTail layout).then (Implementation.second (by decide) layout.value layout.list layout.wordFits layout.tail.representation.fits)
def initialFlag : Implementation .unit layout.input layout.boolean (fun _ => false) :=
  Implementation.constant layout.input layout.boolean ⟨false, trivial⟩ layout.wordFits
def initialUnit : Implementation .unit layout.input layout.unit (fun _ => ()) :=
  Implementation.constant layout.input layout.unit ⟨(), trivial⟩ layout.wordFits

theorem inputIndex_buffers : (inputIndex layout).program.code.memBound ≤ 2 := Implementation.first_buffers _ _ _ _ _
theorem inputTail_buffers : (inputTail layout).program.code.memBound ≤ 2 := Implementation.second_buffers _ _ _ _ _
theorem inputDefault_buffers : (inputDefault layout).program.code.memBound ≤ 2 :=
  max_le (inputTail_buffers layout) (Implementation.first_buffers _ _ _ _ _)
theorem inputList_buffers : (inputList layout).program.code.memBound ≤ 2 :=
  max_le (inputTail_buffers layout) (Implementation.second_buffers _ _ _ _ _)
theorem initialFlag_buffers : (initialFlag layout).program.code.memBound ≤ 2 := Implementation.constant_buffers _ _ _ _
theorem initialUnit_buffers : (initialUnit layout).program.code.memBound ≤ 2 := Implementation.constant_buffers _ _ _ _

theorem Layouts.inputDuplicate : layout.input.representation.encoding.words + layout.input.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := layout.sizes; omega)
def initialPayload : Implementation .unit layout.input layout.payload (fun value => (false, value.2.1)) :=
  (initialFlag layout).pair (inputDefault layout) (by decide) layout.wordFits
    (layout.nameFits _ (initialFlag_buffers layout) (by decide)) (layout.nameFits _ (inputDefault_buffers layout) (by decide))
    layout.inputDuplicate (layout.fits_of_le (by rw [Layouts.boolean_words]; have := layout.sizes; dsimp only [Layouts.width] at *; omega))
    layout.payload.representation.fits
theorem initialPayload_buffers : (initialPayload layout).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 2) _ _ _ _ _ _ _ _
    (initialFlag_buffers layout) (inputDefault_buffers layout)
def initialState : Implementation .unit layout.input layout.state (fun value => (value.1, false, value.2.1)) :=
  (inputIndex layout).pair (initialPayload layout) (by decide) layout.wordFits
    (layout.nameFits _ (inputIndex_buffers layout) (by decide)) (layout.nameFits _ (initialPayload_buffers layout) (by decide))
    layout.inputDuplicate (layout.fits_of_le (by rw [Layouts.counter_words]; have := layout.sizes; dsimp only [Layouts.width] at *; omega))
    layout.state.representation.fits
theorem initialState_buffers : (initialState layout).program.code.memBound ≤ 4 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 3) _ _ _ _ _ _ _ _
    (inputIndex_buffers layout) (initialPayload_buffers layout)
def initialTail : Implementation .unit layout.input layout.stateTail (fun value => ((value.1, false, value.2.1), ())) :=
  (initialState layout).pair (initialUnit layout) (by decide) layout.wordFits
    (layout.nameFits _ (initialState_buffers layout) (by decide)) (layout.nameFits _ (initialUnit_buffers layout) (by decide))
    layout.inputDuplicate (layout.fits_of_le (by have := layout.sizes; omega)) layout.stateTail.representation.fits
theorem initialTail_buffers : (initialTail layout).program.code.memBound ≤ 5 :=
  Implementation.pair_buffers (firstBuffers := 4) (secondBuffers := 2) _ _ _ _ _ _ _ _
    (initialState_buffers layout) (initialUnit_buffers layout)
def prepare : Implementation .unit layout.input layout.frame (fun value => (value.2.2, (value.1, false, value.2.1), ())) :=
  (inputList layout).pair (initialTail layout) (by decide) layout.wordFits
    (layout.nameFits _ (inputList_buffers layout) (by decide)) (layout.nameFits _ (initialTail_buffers layout) (by decide))
    layout.inputDuplicate (layout.fits_of_le (by have := layout.sizes; omega)) layout.frame.representation.fits
theorem prepare_buffers : (prepare layout).program.code.memBound ≤ 6 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 5) _ _ _ _ _ _ _ _
    (inputList_buffers layout) (initialTail_buffers layout)

def loop := FoldImplementation.compile layout.value layout.state layout.unit layout.argFits (body layout) (by decide)
  layout.wordFits (layout.nameFits _ (body_buffers layout) (by decide)) layout.capacity layout.countFits layout.frameFits
theorem loop_buffers : (loop layout).program.code.memBound ≤ 5 :=
  (ListFold.buffers (body layout).program.code _ _ _ _).trans (by have := body_buffers layout; omega)
def result : Implementation .unit layout.state layout.value (fun value => value.2.2) :=
  (Implementation.second (by decide) layout.counter layout.payload layout.wordFits layout.state.representation.fits).then
    (Implementation.second (by decide) layout.boolean layout.value layout.wordFits layout.payload.representation.fits)
theorem result_buffers : (result layout).program.code.memBound ≤ 2 :=
  max_le (Implementation.second_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _)

def implementation : Implementation .unit layout.input layout.value (fun value => (value.2.2[value.1]?).getD value.2.1) :=
  (((prepare layout).then (loop layout)).then (result layout)).castFunction (by
    funext value
    exact indexStep_value value.2.2 value.1 value.2.1)
theorem buffers : (implementation layout).program.code.memBound ≤ 6 :=
  max_le (max_le (prepare_buffers layout) ((loop_buffers layout).trans (by decide))) ((result_buffers layout).trans (by decide))

end Signatures.Runtime.CaliperBackend.ListIndex
