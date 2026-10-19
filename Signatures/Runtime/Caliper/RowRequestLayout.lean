import Signatures.Runtime.Caliper.CacheAccumulateLayout
import Signatures.Runtime.Caliper.EncodedConstant

/-! A represented coefficient row and private accumulator/cache frame. Points
remain in the stored row even though the private lookup uses its message only. -/
namespace Signatures.Runtime.CaliperBackend.RowRequest
open Caliper BoundedSource

structure Layouts (w : Nat) (K G F R : Type) where
  accumulation : CacheAccumulate.Layouts w K F R
  point : Layout w G
  storageFits : 16 * (accumulation.width + point.representation.encoding.words) < 2 ^ w

namespace Layouts
variable {w : Nat} {K G F R : Type} (layout : Layouts w K G F R)
def width : Nat := layout.accumulation.width + layout.point.representation.encoding.words
theorem fits_of_le {words : Nat} (bound : words ≤ 16 * layout.width) : words < 2 ^ w :=
  bound.trans_lt layout.storageFits
theorem width_eq : layout.width = layout.accumulation.cache.key.representation.encoding.words +
    layout.point.representation.encoding.words + layout.accumulation.coefficient.representation.encoding.words +
    2 * layout.accumulation.cache.value.representation.encoding.words +
    layout.accumulation.cache.lookup.table.representation.encoding.words := by
  dsimp only [width, CacheAccumulate.Layouts.width]
  rw [CacheAccumulate.Layouts.cache_width]
  omega
def token : Layout w (K × G) := layout.accumulation.cache.key.prod layout.point
  (layout.fits_of_le (by rw [width_eq]; omega))
def row : Layout w ((K × G) × F) := layout.token.prod layout.accumulation.coefficient
  (layout.fits_of_le (by change (_ + _) + _ ≤ _; rw [width_eq]; omega))
abbrev state : Layout w (R × List (K × R)) := CacheRead.output layout.accumulation.cache
def raw : Layout w (((K × G) × F) × (R × List (K × R))) := layout.row.prod layout.state
  (layout.fits_of_le (by change ((_ + _) + _) + (_ + _) ≤ _; rw [width_eq]; omega))
def ready (value : ((K × G) × F) × (R × List (K × R))) : Prop :=
  value.2.2.length ≤ layout.accumulation.cache.capacityPred
instance (value : ((K × G) × F) × (R × List (K × R))) : Decidable (layout.ready value) :=
  inferInstanceAs (Decidable (_ ≤ _))
def input := layout.raw.restrict layout.ready

@[simp] theorem token_words : layout.token.representation.encoding.words =
    layout.accumulation.cache.key.representation.encoding.words + layout.point.representation.encoding.words := rfl
@[simp] theorem row_words : layout.row.representation.encoding.words =
    layout.accumulation.cache.key.representation.encoding.words + layout.point.representation.encoding.words +
      layout.accumulation.coefficient.representation.encoding.words := rfl
@[simp] theorem state_words : layout.state.representation.encoding.words =
    layout.accumulation.cache.value.representation.encoding.words + layout.accumulation.cache.lookup.table.representation.encoding.words := rfl
@[simp] theorem raw_words : layout.raw.representation.encoding.words =
    layout.row.representation.encoding.words + layout.state.representation.encoding.words := rfl
@[simp] theorem input_words : layout.input.representation.encoding.words = layout.raw.representation.encoding.words := rfl

theorem sizes : layout.token.representation.encoding.words ≤ layout.width ∧
    layout.row.representation.encoding.words ≤ layout.width ∧
    layout.state.representation.encoding.words ≤ layout.width ∧
    layout.raw.representation.encoding.words ≤ layout.width ∧
    layout.accumulation.width ≤ layout.width := by
  simp only [token_words, row_words, state_words, raw_words]
  have := layout.width_eq
  dsimp only [width] at *
  omega

include layout in
theorem nameFits {A B : Type} {input : Layout w A} {output : Layout w B} {f : A → B}
    (body : Implementation .unit input output f) {buffers : Nat}
    (bound : body.program.code.memBound ≤ buffers) (small : buffers ≤ 16) : body.program.savedBuffer < 2 ^ w :=
  CacheAccumulate.nameFits layout.accumulation body bound (small.trans_lt layout.accumulation.cache.wordFits)
end Layouts
end Signatures.Runtime.CaliperBackend.RowRequest
