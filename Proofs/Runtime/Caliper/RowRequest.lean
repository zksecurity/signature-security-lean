import Proofs.Runtime.Caliper.RowRequestLayout

/-! Executed row-to-request construction. The default is literal code, and
every projection and retained coefficient/accumulator is a charged copy. -/
namespace Signatures.Runtime.CaliperBackend.RowRequest
open Caliper BoundedSource
variable {w : Nat} {K G F R : Type} (layout : Layouts w K G F R)
    (default : layout.accumulation.cache.value.Value)

def row : Implementation .unit layout.input layout.row Prod.fst :=
  (Implementation.first (by decide) layout.row layout.state layout.accumulation.cache.wordFits _).restrictInput layout.ready
def state : Implementation .unit layout.input layout.state Prod.snd :=
  (Implementation.second (by decide) layout.row layout.state layout.accumulation.cache.wordFits _).restrictInput layout.ready
def token : Implementation .unit layout.input layout.token (fun value => value.1.1) :=
  (row layout).then (Implementation.first (by decide) layout.token layout.accumulation.coefficient layout.accumulation.cache.wordFits _)
def message : Implementation .unit layout.input layout.accumulation.cache.key (fun value => value.1.1.1) :=
  (token layout).then (Implementation.first (by decide) layout.accumulation.cache.key layout.point layout.accumulation.cache.wordFits _)
def coefficient : Implementation .unit layout.input layout.accumulation.coefficient (fun value => value.1.2) :=
  (row layout).then (Implementation.second (by decide) layout.token layout.accumulation.coefficient layout.accumulation.cache.wordFits _)
def accumulator : Implementation .unit layout.input layout.accumulation.cache.value (fun value => value.2.1) :=
  (state layout).then (Implementation.first (by decide) layout.accumulation.cache.value layout.accumulation.cache.lookup.table layout.accumulation.cache.wordFits _)
def table : Implementation .unit layout.input layout.accumulation.cache.lookup.table (fun value => value.2.2) :=
  (state layout).then (Implementation.second (by decide) layout.accumulation.cache.value layout.accumulation.cache.lookup.table layout.accumulation.cache.wordFits _)

theorem row_buffers : (row layout).program.code.memBound ≤ 2 :=
  Implementation.first_buffers (cost := .unit) (by decide) layout.row layout.state layout.accumulation.cache.wordFits layout.raw.representation.fits
theorem state_buffers : (state layout).program.code.memBound ≤ 2 :=
  Implementation.second_buffers (cost := .unit) (by decide) layout.row layout.state layout.accumulation.cache.wordFits layout.raw.representation.fits
theorem token_buffers : (token layout).program.code.memBound ≤ 2 := max_le (row_buffers layout) (Implementation.first_buffers _ _ _ _ _)
theorem message_buffers : (message layout).program.code.memBound ≤ 2 := max_le (token_buffers layout) (Implementation.first_buffers _ _ _ _ _)
theorem coefficient_buffers : (coefficient layout).program.code.memBound ≤ 2 := max_le (row_buffers layout) (Implementation.second_buffers _ _ _ _ _)
theorem accumulator_buffers : (accumulator layout).program.code.memBound ≤ 2 := max_le (state_buffers layout) (Implementation.first_buffers _ _ _ _ _)
theorem table_buffers : (table layout).program.code.memBound ≤ 2 := max_le (state_buffers layout) (Implementation.second_buffers _ _ _ _ _)

def tableTail : Implementation .unit layout.input layout.accumulation.cache.lookup.tableTail (fun value => (value.2.2, ())) :=
  (table layout).pair (DataImplementation.unit .unit (by decide) _ layout.accumulation.cache.wordFits)
    (by decide) layout.accumulation.cache.wordFits
    (layout.nameFits _ (table_buffers layout) (by decide))
    (by change 2 < 2 ^ w; have := layout.accumulation.cache.wordFits; omega)
    (layout.fits_of_le (by have := layout.sizes; rw [Layouts.input_words]; omega))
    (layout.fits_of_le (by have := layout.sizes; have := layout.accumulation.base_sizes; rw [Layouts.input_words]; omega)) _
theorem tableTail_buffers : (tableTail layout).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (table_buffers layout) (show _ ≤ 2 from le_rfl)

def valueTail : Implementation .unit layout.input layout.accumulation.cache.lookup.valueTail
    (fun value => (default.val, value.2.2, ())) :=
  (Implementation.constant layout.input layout.accumulation.cache.value default layout.accumulation.cache.wordFits).pair
    (tableTail layout) (by decide) layout.accumulation.cache.wordFits
    (layout.nameFits _ (Implementation.constant_buffers _ _ _ _) (by decide))
    (layout.nameFits _ (tableTail_buffers layout) (by decide))
    (layout.fits_of_le (by have := layout.sizes; rw [Layouts.input_words]; omega))
    (layout.fits_of_le (by have := layout.sizes; have := layout.accumulation.base_sizes; rw [Layouts.input_words]; omega)) _
theorem valueTail_buffers : (valueTail layout default).program.code.memBound ≤ 4 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (Implementation.constant_buffers _ _ _ _) (tableTail_buffers layout)

variable [DecidableEq K]
def cacheArguments : Implementation .unit layout.input layout.accumulation.cache.input
    (fun value => (value.1.1.1, default.val, value.2.2, ())) :=
  ((message layout).pair (valueTail layout default) (by decide) layout.accumulation.cache.wordFits
    (layout.nameFits _ (message_buffers layout) (by decide))
    (layout.nameFits _ (valueTail_buffers layout default) (by decide))
    (layout.fits_of_le (by have := layout.sizes; rw [Layouts.input_words]; omega))
    (layout.fits_of_le (by have := layout.sizes; rw [Layouts.input_words]; rw [Layouts.raw_words, Layouts.row_words, Layouts.state_words] at *; rw [Layouts.width_eq]; omega)) _).restrictOutput
      layout.accumulation.cache.admissible (fun _ valid _ => valid.2)
theorem cacheArguments_buffers : (cacheArguments layout default).program.code.memBound ≤ 5 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ layout.accumulation.cache.lookup.input.representation.fits (message_buffers layout) (valueTail_buffers layout default)

def saved : Implementation .unit layout.input layout.accumulation.saved (fun value => (value.1.2, value.2.1)) :=
  (coefficient layout).pair (accumulator layout) (by decide) layout.accumulation.cache.wordFits
    (layout.nameFits _ (coefficient_buffers layout) (by decide))
    (layout.nameFits _ (accumulator_buffers layout) (by decide))
    (layout.fits_of_le (by have := layout.sizes; rw [Layouts.input_words]; omega))
    (layout.fits_of_le (by have := layout.sizes; have := layout.accumulation.base_sizes; rw [Layouts.input_words]; omega)) _
omit [DecidableEq K] in
theorem saved_buffers : (saved layout).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (coefficient_buffers layout) (accumulator_buffers layout)

def prepare : Implementation .unit layout.input layout.accumulation.input
    (fun value => ((value.1.1.1, default.val, value.2.2, ()), value.1.2, value.2.1)) :=
  (cacheArguments layout default).pair (saved layout) (by decide) layout.accumulation.cache.wordFits
    (layout.nameFits _ (cacheArguments_buffers layout default) (by decide))
    (layout.nameFits _ (saved_buffers layout) (by decide))
    (layout.fits_of_le (by have := layout.sizes; rw [Layouts.input_words]; omega))
    (layout.fits_of_le (by have := layout.sizes; rw [Layouts.input_words]; change layout.accumulation.cache.lookup.input.representation.encoding.words + _ ≤ _; rw [LookupLayout.input_words]; have := layout.accumulation.base_sizes; omega)) _
theorem prepare_buffers : (prepare layout default).program.code.memBound ≤ 6 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (cacheArguments_buffers layout default) (saved_buffers layout)

end Signatures.Runtime.CaliperBackend.RowRequest
