import Proofs.Runtime.Caliper.CacheAccumulateLayout

/-! Executed continuation after a private cache read. It constructs the
coefficient/answer/accumulator arguments, runs their local update, and returns
the new accumulator with the updated cache. Every retained word is charged. -/

namespace Signatures.Runtime.CaliperBackend.CacheAccumulate
open Caliper BoundedSource
variable {w : Nat} {K F R : Type} (layout : Layouts w K F R)

def answer : Implementation .unit layout.returned layout.cache.value (fun value => value.1.1) :=
  (Implementation.first (by decide) (CacheRead.output layout.cache) layout.saved layout.cache.wordFits layout.returned.representation.fits).then
    (Implementation.first (by decide) layout.cache.value layout.cache.lookup.table layout.cache.wordFits (CacheRead.output layout.cache).representation.fits)
def table : Implementation .unit layout.returned layout.cache.lookup.table (fun value => value.1.2) :=
  (Implementation.first (by decide) (CacheRead.output layout.cache) layout.saved layout.cache.wordFits layout.returned.representation.fits).then
    (Implementation.second (by decide) layout.cache.value layout.cache.lookup.table layout.cache.wordFits (CacheRead.output layout.cache).representation.fits)
def coefficient : Implementation .unit layout.returned layout.coefficient (fun value => value.2.1) :=
  (Implementation.second (by decide) (CacheRead.output layout.cache) layout.saved layout.cache.wordFits layout.returned.representation.fits).then
    (Implementation.first (by decide) layout.coefficient layout.cache.value layout.cache.wordFits layout.saved.representation.fits)
def accumulator : Implementation .unit layout.returned layout.cache.value (fun value => value.2.2) :=
  (Implementation.second (by decide) (CacheRead.output layout.cache) layout.saved layout.cache.wordFits layout.returned.representation.fits).then
    (Implementation.second (by decide) layout.coefficient layout.cache.value layout.cache.wordFits layout.saved.representation.fits)
theorem answer_buffers : (answer layout).program.code.memBound ≤ 2 := max_le (Implementation.first_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _)
theorem table_buffers : (table layout).program.code.memBound ≤ 2 := max_le (Implementation.first_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _)
theorem coefficient_buffers : (coefficient layout).program.code.memBound ≤ 2 := max_le (Implementation.second_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _)
theorem accumulator_buffers : (accumulator layout).program.code.memBound ≤ 2 := max_le (Implementation.second_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _)
def operands : Implementation .unit layout.returned layout.pair (fun value => (value.1.1, value.2.2)) :=
  (answer layout).pair (accumulator layout) (by decide) layout.cache.wordFits
    (nameFits layout _ (answer_buffers layout) (by have := layout.cache.wordFits; omega))
    (nameFits layout _ (accumulator_buffers layout) (by have := layout.cache.wordFits; omega))
    (layout.fits_of_le (by have := layout.sizes; omega))
    (layout.fits_of_le (by have := layout.sizes; have := layout.base_sizes; omega)) layout.pair.representation.fits
theorem operands_buffers : (operands layout).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 2) _ _ _ _ _ _ _ _ (answer_buffers layout) (accumulator_buffers layout)
def arguments : Implementation .unit layout.returned layout.combine (fun value => (value.2.1, value.1.1, value.2.2)) :=
  (coefficient layout).pair (operands layout) (by decide) layout.cache.wordFits
    (nameFits layout _ (coefficient_buffers layout) (by have := layout.cache.wordFits; omega))
    (nameFits layout _ (operands_buffers layout) (by have := layout.cache.wordFits; omega))
    (layout.fits_of_le (by have := layout.sizes; omega))
    (layout.fits_of_le (by have := layout.sizes; have := layout.base_sizes; omega)) layout.combine.representation.fits
theorem arguments_buffers : (arguments layout).program.code.memBound ≤ 4 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 3) _ _ _ _ _ _ _ _ (coefficient_buffers layout) (operands_buffers layout)

variable {combine : F × (R × R) → R} (update : Implementation .unit layout.combine layout.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
def updated : Implementation .unit layout.returned layout.cache.value (fun value => combine (value.2.1, value.1.1, value.2.2)) :=
  (arguments layout).then update
include updateBuffers in
theorem updated_buffers : (updated layout update).program.code.memBound ≤ max 4 slots :=
  max_le ((arguments_buffers layout).trans (Nat.le_max_left _ _)) (updateBuffers.trans (Nat.le_max_right _ _))
def finish : Implementation .unit layout.returned (CacheRead.output layout.cache)
    (fun value => (combine (value.2.1, value.1.1, value.2.2), value.1.2)) :=
  (updated layout update).pair (table layout) (by decide) layout.cache.wordFits
    (nameFits layout _ (updated_buffers layout update updateBuffers) (by have := layout.cache.wordFits; omega))
    (nameFits layout _ (table_buffers layout) (by have := layout.cache.wordFits; omega))
    (layout.fits_of_le (by have := layout.sizes; omega))
    (layout.fits_of_le (by have := layout.sizes; have := layout.base_sizes; omega)) (CacheRead.output layout.cache).representation.fits
theorem finish_buffers : (finish layout update updateBuffers reserve).program.code.memBound ≤ max 4 slots + 1 :=
  (Implementation.pair_buffers (firstBuffers := max 4 slots) (secondBuffers := 2) _ _ _ _ _ _ _ _
    (updated_buffers layout update updateBuffers) (table_buffers layout)).trans (by omega)

end Signatures.Runtime.CaliperBackend.CacheAccumulate
