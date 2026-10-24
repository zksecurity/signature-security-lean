import Proofs.Runtime.Caliper.CacheAccumulateFinishNames

/-! A private lookup may return a pair even though extraction returns one
scalar. This executed continuation constructs the scalar routine's arguments
and returns its result with the complete updated cache. -/
namespace Signatures.Runtime.CaliperBackend.CacheScalarResult
open Caliper BoundedSource
variable {w : Nat} {K F R : Type} (layout : CacheAccumulate.Layouts w K F R)

abbrev output : Layout w (F × List (K × R)) := layout.coefficient.prod layout.cache.lookup.table
  (layout.fits_of_le (by have := layout.base_sizes; omega))

variable {combine : F × (R × R) → F} (update : Implementation .unit layout.combine layout.coefficient combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
def updated : Implementation .unit layout.returned layout.coefficient (fun value => combine (value.2.1, value.1.1, value.2.2)) :=
  (CacheAccumulate.arguments layout).then update
include updateBuffers in
theorem updated_buffers : (updated layout update).program.code.memBound ≤ max 4 slots :=
  max_le ((CacheAccumulate.arguments_buffers layout).trans (Nat.le_max_left _ _)) (updateBuffers.trans (Nat.le_max_right _ _))
def finish : Implementation .unit layout.returned (output layout)
    (fun value => (combine (value.2.1, value.1.1, value.2.2), value.1.2)) :=
  (updated layout update).pair (CacheAccumulate.table layout) (by decide) layout.cache.wordFits
    (CacheAccumulate.nameFits layout _ (updated_buffers layout update updateBuffers) (by have := layout.cache.wordFits; omega))
    (CacheAccumulate.nameFits layout _ (CacheAccumulate.table_buffers layout) (by have := layout.cache.wordFits; omega))
    (layout.fits_of_le (by have := layout.sizes; omega))
    (layout.fits_of_le (by have := layout.sizes; have := layout.base_sizes; omega)) (output layout).representation.fits
theorem finish_buffers : (finish layout update updateBuffers reserve).program.code.memBound ≤ max 4 slots + 1 :=
  (Implementation.pair_buffers (firstBuffers := max 4 slots) (secondBuffers := 2) _ _ _ _ _ _ _ _
    (updated_buffers layout update updateBuffers) (CacheAccumulate.table_buffers layout)).trans (by omega)

variable {updateTime updateCode : Nat} (bound : update.BoundedBy updateTime updateCode)
include bound in
theorem updated_bounded : (updated layout update).BoundedBy (256 * layout.width + updateTime)
    (832 * layout.width + 336 + updateCode) := by
  apply ((CacheAccumulate.arguments_bounded layout).then bound).mono <;> omega
include bound in
theorem finish_bounded : (finish layout update updateBuffers reserve).BoundedBy
    (376 * layout.width + updateTime) (1222 * layout.width + 489 + updateCode) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (updated_bounded layout update bound) (CacheAccumulate.table_bounded layout)).mono
  all_goals have := layout.sizes; have := layout.base_sizes; omega

variable {names : Nat} (updateNames : NamesAccounted update.program.code names)
include updateNames in
theorem finish_names : NamesAccounted (finish layout update updateBuffers reserve).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ ((CacheAccumulate.arguments_names layout names).seq updateNames)
    (CacheAccumulate.table_names layout names)
end Signatures.Runtime.CaliperBackend.CacheScalarResult
