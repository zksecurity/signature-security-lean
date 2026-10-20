import Signatures.Runtime.Caliper.WeightedExtractionLayout

/-! Executed transcript preparation, zero-accumulator creation and cache
retention. The mathematical row view only changes proof witnesses; the copied
bytes are exactly those consumed by the interactive row fold. -/
namespace Signatures.Runtime.CaliperBackend.WeightedExtraction
open Caliper BoundedSource
variable {w : Nat} {K M G F R : Type} (layout : Layouts w K M G F R)
    (coefficientDefault : layout.rows.accumulation.coefficient.Value)
    (initial : layout.rows.accumulation.cache.value.Value)

def rows : Implementation .unit layout.input layout.assembly.output
    (fun value => value.1.1.reverse.mapIdx (fun n token => (token, (value.1.2[n]?).getD coefficientDefault.val))) :=
  (Implementation.first (by decide) (TokenRows.input layout.assembly) layout.rows.accumulation.cache.lookup.table
    layout.rows.accumulation.cache.wordFits layout.input.representation.fits).then
    (TokenRows.implementation layout.assembly coefficientDefault)
def cache : Implementation .unit layout.input layout.rows.accumulation.cache.lookup.table Prod.snd :=
  Implementation.second (by decide) (TokenRows.input layout.assembly) layout.rows.accumulation.cache.lookup.table
    layout.rows.accumulation.cache.wordFits layout.input.representation.fits
def accumulator : Implementation .unit layout.input layout.rows.accumulation.cache.value (fun _ => initial.val) :=
  Implementation.constant layout.input layout.rows.accumulation.cache.value initial layout.rows.accumulation.cache.wordFits
theorem rows_buffers : (rows layout coefficientDefault).program.code.memBound ≤ 10 :=
  max_le ((Implementation.first_buffers _ _ _ _ _).trans (by decide)) (TokenRows.buffers _ _)
theorem cache_buffers : (cache layout).program.code.memBound ≤ 2 := Implementation.second_buffers _ _ _ _ _
theorem accumulator_buffers : (accumulator layout initial).program.code.memBound ≤ 2 := Implementation.constant_buffers _ _ _ _
def state : Implementation .unit layout.input layout.rows.state (fun value => (initial.val, value.2)) :=
  (accumulator layout initial).pair (cache layout) (by decide) layout.rows.accumulation.cache.wordFits
    (layout.rows.nameFits _ (accumulator_buffers layout initial) (by decide))
    (layout.rows.nameFits _ (cache_buffers layout) (by decide))
    (layout.fits_of_le (by have := layout.input_size; omega))
    (layout.fits_of_le (by have := layout.input_size; have := layout.base_sizes; omega)) layout.rows.state.representation.fits
theorem state_buffers : (state layout initial).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 2) _ _ _ _ _ _ _ _
    (accumulator_buffers layout initial) (cache_buffers layout)
def prepare : Implementation .unit layout.input layout.prepared
    (fun value => (value.1.1.reverse.mapIdx (fun n token => (token, (value.1.2[n]?).getD coefficientDefault.val)), initial.val, value.2)) :=
  (rows layout coefficientDefault).pair (state layout initial) (by decide) layout.rows.accumulation.cache.wordFits
    (layout.rows.nameFits _ (rows_buffers layout coefficientDefault) (by decide))
    (layout.rows.nameFits _ (state_buffers layout initial) (by decide))
    (layout.fits_of_le (by have := layout.input_size; omega))
    (layout.fits_of_le (by have := layout.input_size; have := layout.base_sizes; omega)) layout.prepared.representation.fits
theorem prepare_buffers : (prepare layout coefficientDefault initial).program.code.memBound ≤ 11 :=
  Implementation.pair_buffers (firstBuffers := 10) (secondBuffers := 3) _ _ _ _ _ _ _ _
    (rows_buffers layout coefficientDefault) (state_buffers layout initial)

def foldView (value : layout.prepared.Value) :
    BoundedList layout.rows.row.Value layout.capacity × layout.rows.state.Value :=
  let pair := productView layout.assembly.output layout.rows.state value
  (listView layout.rows.row layout.capacity pair.1, pair.2)
theorem foldView_bytes (value : layout.prepared.Value) :
    (InteractiveFold.frame layout.rows.row.representation layout.rows.state.representation layout.capacity layout.countFits layout.foldFits).encoding.encode
      (foldView layout value) = layout.prepared.representation.encoding.encode value := rfl
def preparedValue (value : layout.input.Value) : layout.prepared.Value :=
  ⟨(value.val.1.1.reverse.mapIdx (fun n token => (token, (value.val.1.2[n]?).getD coefficientDefault.val)), initial.val, value.val.2),
    (prepare layout coefficientDefault initial).preserves value.val value.property⟩
def foldValue (value : layout.input.Value) := foldView layout (preparedValue layout coefficientDefault initial value)
theorem foldValue_length (value : layout.input.Value) :
    (foldValue layout coefficientDefault initial value).1.val.length = value.val.1.1.length := by
  change (List.attachWith _ _ _).length = _
  rw [List.length_attachWith]
  change (value.val.1.1.reverse.mapIdx (fun n token => (token, (value.val.1.2[n]?).getD coefficientDefault.val))).length = _
  simp only [List.length_mapIdx, List.length_reverse]
theorem foldValue_rows (value : layout.input.Value) :
    ((foldValue layout coefficientDefault initial value).1.val.map Subtype.val) =
      value.val.1.1.reverse.mapIdx (fun n token => (token, (value.val.1.2[n]?).getD coefficientDefault.val)) :=
  listView_values layout.rows.row layout.capacity _
end Signatures.Runtime.CaliperBackend.WeightedExtraction
