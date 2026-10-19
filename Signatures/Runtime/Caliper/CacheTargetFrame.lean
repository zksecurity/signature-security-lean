import Signatures.Runtime.Caliper.CacheAccumulateFinishNames
import Signatures.Runtime.Caliper.EncodedConstant

/-! Executed packing of a final private lookup after transcript evaluation.
The incoming frame contains the returned sum/cache and the saved target/scalar.
Every projection, saved copy and literal default is actual Caliper code. -/
namespace Signatures.Runtime.CaliperBackend.CacheTargetFrame
open Caliper BoundedSource
variable {w : Nat} {K F R : Type} (layout : CacheAccumulate.Layouts w K F R)

theorem key_size : layout.cache.key.representation.encoding.words ≤ layout.width := by
  dsimp only [CacheAccumulate.Layouts.width]
  rw [layout.cache_width]
  omega
def context : Layout w (K × F) := layout.cache.key.prod layout.coefficient
  (layout.fits_of_le (by have := key_size layout; have := layout.base_sizes; omega))
def returned : Layout w ((R × List (K × R)) × (K × F)) :=
  (CacheRead.output layout.cache).prod (context layout)
    (layout.fits_of_le (by
      change (_ + _) + (_ + _) ≤ _
      dsimp only [CacheAccumulate.Layouts.width]
      rw [layout.cache_width]
      omega))
def packed : Layout w (CacheLayout.Input K R × (F × R)) :=
  layout.cache.lookup.input.prod layout.saved
    (layout.fits_of_le (by rw [LookupLayout.input_words]; have := layout.sizes; have := layout.base_sizes; omega))
theorem sizes : (context layout).representation.encoding.words ≤ layout.width ∧
    (returned layout).representation.encoding.words ≤ layout.width ∧
    (packed layout).representation.encoding.words ≤ layout.width ∧
    layout.cache.lookup.tableTail.representation.encoding.words ≤ layout.width ∧
    layout.cache.lookup.valueTail.representation.encoding.words ≤ layout.width ∧
    layout.cache.lookup.input.representation.encoding.words ≤ layout.width := by
  change (layout.cache.key.representation.encoding.words + layout.coefficient.representation.encoding.words) ≤ layout.width ∧
    ((layout.cache.value.representation.encoding.words + layout.cache.lookup.table.representation.encoding.words) +
      (layout.cache.key.representation.encoding.words + layout.coefficient.representation.encoding.words)) ≤ layout.width ∧
    (layout.cache.lookup.input.representation.encoding.words +
      (layout.coefficient.representation.encoding.words + layout.cache.value.representation.encoding.words)) ≤ layout.width ∧
    (layout.cache.lookup.table.representation.encoding.words + 0) ≤ layout.width ∧
    (layout.cache.value.representation.encoding.words + (layout.cache.lookup.table.representation.encoding.words + 0)) ≤ layout.width ∧
    layout.cache.lookup.input.representation.encoding.words ≤ layout.width
  rw [LookupLayout.input_words]
  dsimp only [CacheAccumulate.Layouts.width]
  rw [layout.cache_width]
  omega

def result : Implementation .unit (returned layout) layout.cache.value (fun value => value.1.1) :=
  (Implementation.first (by decide) (CacheRead.output layout.cache) (context layout) layout.cache.wordFits _).then
    (Implementation.first (by decide) layout.cache.value layout.cache.lookup.table layout.cache.wordFits _)
def table : Implementation .unit (returned layout) layout.cache.lookup.table (fun value => value.1.2) :=
  (Implementation.first (by decide) (CacheRead.output layout.cache) (context layout) layout.cache.wordFits _).then
    (Implementation.second (by decide) layout.cache.value layout.cache.lookup.table layout.cache.wordFits _)
def target : Implementation .unit (returned layout) layout.cache.key (fun value => value.2.1) :=
  (Implementation.second (by decide) (CacheRead.output layout.cache) (context layout) layout.cache.wordFits _).then
    (Implementation.first (by decide) layout.cache.key layout.coefficient layout.cache.wordFits _)
def coefficient : Implementation .unit (returned layout) layout.coefficient (fun value => value.2.2) :=
  (Implementation.second (by decide) (CacheRead.output layout.cache) (context layout) layout.cache.wordFits _).then
    (Implementation.second (by decide) layout.cache.key layout.coefficient layout.cache.wordFits _)
theorem result_buffers : (result layout).program.code.memBound ≤ 2 := max_le (Implementation.first_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _)
theorem table_buffers : (table layout).program.code.memBound ≤ 2 := max_le (Implementation.first_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _)
theorem target_buffers : (target layout).program.code.memBound ≤ 2 := max_le (Implementation.second_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _)
theorem coefficient_buffers : (coefficient layout).program.code.memBound ≤ 2 := max_le (Implementation.second_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _)

def unit : Implementation .unit (returned layout) layout.cache.lookup.unit (fun _ => ()) :=
  Implementation.constant (returned layout) layout.cache.lookup.unit ⟨(), trivial⟩ layout.cache.wordFits
theorem unit_buffers : (unit layout).program.code.memBound ≤ 2 := Implementation.constant_buffers _ _ _ _
def tableTail : Implementation .unit (returned layout) layout.cache.lookup.tableTail (fun value => (value.1.2, ())) :=
  (table layout).pair (unit layout) (by decide) layout.cache.wordFits
    (CacheAccumulate.nameFits layout _ (table_buffers layout) (by have := layout.cache.wordFits; omega))
    (CacheAccumulate.nameFits layout _ (unit_buffers layout) (by have := layout.cache.wordFits; omega))
    (layout.fits_of_le (by have := sizes layout; omega))
    (layout.fits_of_le (by have := sizes layout; have := layout.base_sizes; omega)) _
theorem tableTail_buffers : (tableTail layout).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 2) _ _ _ _ _ _ _ _ (table_buffers layout) (unit_buffers layout)

variable (fallback : layout.cache.value.Value)
def defaultValue : Implementation .unit (returned layout) layout.cache.value (fun _ => fallback.val) :=
  Implementation.constant (returned layout) layout.cache.value fallback layout.cache.wordFits
theorem defaultValue_buffers : (defaultValue layout fallback).program.code.memBound ≤ 2 := Implementation.constant_buffers _ _ _ _
def valueTail : Implementation .unit (returned layout) layout.cache.lookup.valueTail (fun value => (fallback.val, value.1.2, ())) :=
  (defaultValue layout fallback).pair (tableTail layout) (by decide) layout.cache.wordFits
    (CacheAccumulate.nameFits layout _ (defaultValue_buffers layout fallback) (by have := layout.cache.wordFits; omega))
    (CacheAccumulate.nameFits layout _ (tableTail_buffers layout) (by have := layout.cache.wordFits; omega))
    (layout.fits_of_le (by have := sizes layout; omega))
    (layout.fits_of_le (by have := sizes layout; have := layout.base_sizes; omega)) _
theorem valueTail_buffers : (valueTail layout fallback).program.code.memBound ≤ 4 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 3) _ _ _ _ _ _ _ _ (defaultValue_buffers layout fallback) (tableTail_buffers layout)
def request : Implementation .unit (returned layout) layout.cache.lookup.input (fun value => (value.2.1, fallback.val, value.1.2, ())) :=
  (target layout).pair (valueTail layout fallback) (by decide) layout.cache.wordFits
    (CacheAccumulate.nameFits layout _ (target_buffers layout) (by have := layout.cache.wordFits; omega))
    (CacheAccumulate.nameFits layout _ (valueTail_buffers layout fallback) (by have := layout.cache.wordFits; omega))
    (layout.fits_of_le (by have := sizes layout; omega))
    (layout.fits_of_le (by have := sizes layout; have := key_size layout; omega)) _
theorem request_buffers : (request layout fallback).program.code.memBound ≤ 5 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 4) _ _ _ _ _ _ _ _ (target_buffers layout) (valueTail_buffers layout fallback)
def saved : Implementation .unit (returned layout) layout.saved (fun value => (value.2.2, value.1.1)) :=
  (coefficient layout).pair (result layout) (by decide) layout.cache.wordFits
    (CacheAccumulate.nameFits layout _ (coefficient_buffers layout) (by have := layout.cache.wordFits; omega))
    (CacheAccumulate.nameFits layout _ (result_buffers layout) (by have := layout.cache.wordFits; omega))
    (layout.fits_of_le (by have := sizes layout; omega))
    (layout.fits_of_le (by have := sizes layout; have := layout.base_sizes; omega)) _
theorem saved_buffers : (saved layout).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 2) _ _ _ _ _ _ _ _ (coefficient_buffers layout) (result_buffers layout)
def pack : Implementation .unit (returned layout) (packed layout)
    (fun value => ((value.2.1, fallback.val, value.1.2, ()), value.2.2, value.1.1)) :=
  (request layout fallback).pair (saved layout) (by decide) layout.cache.wordFits
    (CacheAccumulate.nameFits layout _ (request_buffers layout fallback) (by have := layout.cache.wordFits; omega))
    (CacheAccumulate.nameFits layout _ (saved_buffers layout) (by have := layout.cache.wordFits; omega))
    (layout.fits_of_le (by have := sizes layout; omega))
    (layout.fits_of_le (by have := sizes layout; omega)) _
theorem pack_buffers : (pack layout fallback).program.code.memBound ≤ 6 :=
  Implementation.pair_buffers (firstBuffers := 5) (secondBuffers := 3) _ _ _ _ _ _ _ _ (request_buffers layout fallback) (saved_buffers layout)

variable [DecidableEq K]
def admissible (value : (R × List (K × R)) × (K × F)) : Prop :=
  layout.cache.admissible (value.2.1, fallback.val, value.1.2, ())
instance (value : (R × List (K × R)) × (K × F)) : Decidable (admissible layout fallback value) :=
  inferInstanceAs (Decidable (layout.cache.admissible _))
def input : Layout w ((R × List (K × R)) × (K × F)) := (returned layout).restrict (admissible layout fallback)
def implementation : Implementation .unit (input layout fallback) layout.input
    (fun value => ((value.2.1, fallback.val, value.1.2, ()), value.2.2, value.1.1)) where
  preserves value valid :=
    let result := (pack layout fallback).preserves value valid.1
    ⟨⟨result.1, valid.2⟩, result.2⟩
  program := ((pack layout fallback).restrictInput (admissible layout fallback)).program.viewOutput
    layout.input.representation _ (fun _ => rfl)
theorem implementation_buffers : (implementation layout fallback).program.code.memBound ≤ 6 := pack_buffers layout fallback
theorem admissible_of_room (value : (returned layout).Value) (room : value.val.1.2.length ≤ layout.cache.capacityPred) :
    admissible layout fallback value.val := fun _ => room
end Signatures.Runtime.CaliperBackend.CacheTargetFrame
