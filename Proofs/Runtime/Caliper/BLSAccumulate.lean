import Proofs.Runtime.Caliper.BLSResponseMemory
import Proofs.Runtime.LazyAGMEvaluate

/-! Executed BLS extraction accumulator updates. Only individual field
multiplication and addition routines are supplied. Both coordinates of the bad
branch are constructed from those same scalar routines, with charged copies. -/

namespace Signatures.Runtime.CaliperBackend.BLSAccumulate
open Caliper BoundedSource

structure Layouts (w : Nat) (F : Type) where
  scalar : Layout w F
  wordFits : 16 < 2 ^ w
  storageFits : 32 * scalar.representation.encoding.words < 2 ^ w

namespace Layouts
variable {w : Nat} {F : Type} (layout : Layouts w F)
def arithmetic : BLSResponse.Layouts w F F :=
  ⟨layout.scalar, layout.scalar, layout.wordFits, by have := layout.storageFits; omega⟩
@[simp] theorem arithmetic_scalar : layout.arithmetic.scalar = layout.scalar := rfl
@[simp] theorem arithmetic_point : layout.arithmetic.point = layout.scalar := rfl
def pair := layout.arithmetic.points
def good := layout.arithmetic.config
theorem fits_of_le {words : Nat} (bound : words ≤ 32 * layout.scalar.representation.encoding.words) : words < 2 ^ w :=
  bound.trans_lt layout.storageFits
def pairs : Layout w ((F × F) × (F × F)) := layout.pair.prod layout.pair
  (layout.fits_of_le (by change (layout.scalar.representation.encoding.words + layout.scalar.representation.encoding.words) +
    (layout.scalar.representation.encoding.words + layout.scalar.representation.encoding.words) ≤ _; omega))
def bad : Layout w (F × ((F × F) × (F × F))) := layout.scalar.prod layout.pairs
  (layout.fits_of_le (by change layout.scalar.representation.encoding.words +
    ((layout.scalar.representation.encoding.words + layout.scalar.representation.encoding.words) +
      (layout.scalar.representation.encoding.words + layout.scalar.representation.encoding.words)) ≤ _; omega))
@[simp] theorem pair_words : layout.pair.representation.encoding.words = 2 * layout.scalar.representation.encoding.words := by
  change layout.scalar.representation.encoding.words + layout.scalar.representation.encoding.words = _; omega
@[simp] theorem good_words : layout.good.representation.encoding.words = 3 * layout.scalar.representation.encoding.words := by
  change layout.scalar.representation.encoding.words + (layout.scalar.representation.encoding.words + layout.scalar.representation.encoding.words) = _; omega
@[simp] theorem pairs_words : layout.pairs.representation.encoding.words = 4 * layout.scalar.representation.encoding.words := by
  change (layout.scalar.representation.encoding.words + layout.scalar.representation.encoding.words) +
    (layout.scalar.representation.encoding.words + layout.scalar.representation.encoding.words) = _; omega
@[simp] theorem bad_words : layout.bad.representation.encoding.words = 5 * layout.scalar.representation.encoding.words := by
  change layout.scalar.representation.encoding.words +
    ((layout.scalar.representation.encoding.words + layout.scalar.representation.encoding.words) +
      (layout.scalar.representation.encoding.words + layout.scalar.representation.encoding.words)) = _; omega
include layout in
theorem nameFits {A B : Type} {input : Layout w A} {output : Layout w B} {f : A → B}
    (body : Implementation .unit input output f) {buffers : Nat}
    (bound : body.program.code.memBound ≤ buffers) (fits : buffers < 2 ^ w) : body.program.savedBuffer < 2 ^ w := by
  have := layout.wordFits
  dsimp only [Realizer.savedBuffer]
  omega
end Layouts

variable {w : Nat} {F : Type} (layout : Layouts w F)
def coefficient : Implementation .unit layout.bad layout.scalar Prod.fst :=
  Implementation.first (by decide) layout.scalar layout.pairs layout.wordFits layout.bad.representation.fits
def pairSelect (second : Bool) : Implementation .unit layout.pairs layout.pair
    (fun value => if second then value.2 else value.1) := by
  cases second
  · exact Implementation.first (by decide) layout.pair layout.pair layout.wordFits layout.pairs.representation.fits
  · exact Implementation.second (by decide) layout.pair layout.pair layout.wordFits layout.pairs.representation.fits
def coordinate (accumulator second : Bool) : Implementation .unit layout.bad layout.scalar
    (fun value => if second then (if accumulator then value.2.2 else value.2.1).2
      else (if accumulator then value.2.2 else value.2.1).1) :=
  ((Implementation.second (by decide) layout.scalar layout.pairs layout.wordFits layout.bad.representation.fits).then
    (pairSelect layout accumulator)).then (BLSResponse.pointSelect layout.arithmetic second)
theorem coefficient_buffers : (coefficient layout).program.code.memBound ≤ 2 := Implementation.first_buffers _ _ _ _ _
theorem pairSelect_buffers (second : Bool) : (pairSelect layout second).program.code.memBound ≤ 2 := by
  cases second
  · exact Implementation.first_buffers _ _ _ _ _
  · exact Implementation.second_buffers _ _ _ _ _
theorem coordinate_buffers (accumulator second : Bool) : (coordinate layout accumulator second).program.code.memBound ≤ 2 :=
  max_le (max_le (Implementation.second_buffers _ _ _ _ _) (pairSelect_buffers layout accumulator))
    (BLSResponse.pointSelect_buffers layout.arithmetic second)
def coordinatePair (second : Bool) : Implementation .unit layout.bad layout.pair
    (fun value => (if second then value.2.1.2 else value.2.1.1, if second then value.2.2.2 else value.2.2.1)) :=
  (coordinate layout false second).pair (coordinate layout true second) (by decide) layout.wordFits
    (layout.nameFits _ (coordinate_buffers layout false second) (by have := layout.wordFits; omega))
    (layout.nameFits _ (coordinate_buffers layout true second) (by have := layout.wordFits; omega))
    (layout.fits_of_le (by rw [Layouts.bad_words]; omega))
    (layout.fits_of_le (by rw [Layouts.bad_words]; omega)) layout.pair.representation.fits
theorem coordinatePair_buffers (second : Bool) : (coordinatePair layout second).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 2) _ _ _ _ _ _ _ layout.pair.representation.fits
    (coordinate_buffers layout false second) (coordinate_buffers layout true second)
def coordinateInput (second : Bool) : Implementation .unit layout.bad layout.good
    (fun value => (value.1, (if second then value.2.1.2 else value.2.1.1), if second then value.2.2.2 else value.2.2.1)) :=
  (coefficient layout).pair (coordinatePair layout second) (by decide) layout.wordFits
    (layout.nameFits _ (coefficient_buffers layout) (by have := layout.wordFits; omega))
    (layout.nameFits _ (coordinatePair_buffers layout second) (by have := layout.wordFits; omega))
    (layout.fits_of_le (by rw [Layouts.bad_words]; omega))
    (layout.fits_of_le (by rw [Layouts.bad_words]; omega)) layout.good.representation.fits
theorem coordinateInput_buffers (second : Bool) : (coordinateInput layout second).program.code.memBound ≤ 4 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 3) _ _ _ _ _ _ _ _
    (coefficient_buffers layout) (coordinatePair_buffers layout second)

variable [Mul F] [Add F]
    (mul : Implementation .unit layout.pair layout.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.pair layout.scalar (fun value => value.1 + value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)

def term : Implementation .unit layout.good layout.scalar (fun value => value.1 * value.2.1) :=
  (BLSResponse.goodArguments layout.arithmetic false).then mul
include mulBuffers in
omit [Add F] in
theorem term_buffers : (term layout mul).program.code.memBound ≤ max 3 slots :=
  max_le ((BLSResponse.goodArguments_buffers layout.arithmetic false).trans (Nat.le_max_left _ _))
    (mulBuffers.trans (Nat.le_max_right _ _))
def addArgs : Implementation .unit layout.good layout.pair (fun value => (value.2.2, value.1 * value.2.1)) :=
  (BLSResponse.goodPoint layout.arithmetic true).pair (term layout mul) (by decide) layout.wordFits
    (layout.nameFits _ (BLSResponse.goodPoint_buffers layout.arithmetic true) (by have := layout.wordFits; omega))
    (layout.nameFits _ (term_buffers layout mul mulBuffers) (by have := layout.wordFits; omega))
    (layout.fits_of_le (by simp only [BLSResponse.Layouts.config_words, Layouts.arithmetic_scalar, Layouts.arithmetic_point]; omega))
    (layout.fits_of_le (by simp only [BLSResponse.Layouts.config_words, Layouts.arithmetic_scalar, Layouts.arithmetic_point]; omega)) layout.pair.representation.fits
def good : Implementation .unit layout.good layout.scalar (fun value => value.2.2 + value.1 * value.2.1) :=
  (addArgs layout mul mulBuffers reserve).then add
omit [Add F] in
theorem addArgs_buffers : (addArgs layout mul mulBuffers reserve).program.code.memBound ≤ max 3 slots + 1 :=
  (Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := max 3 slots) _ _ _ _ _ _ _ _
    (BLSResponse.goodPoint_buffers layout.arithmetic true) (term_buffers layout mul mulBuffers)).trans (by omega)

variable (addBuffers : add.program.code.memBound ≤ slots)
include addBuffers in
theorem good_buffers : (good layout mul add mulBuffers reserve).program.code.memBound ≤ max 3 slots + 1 :=
  max_le (addArgs_buffers layout mul mulBuffers reserve) (addBuffers.trans (by omega))
def component (second : Bool) := (coordinateInput layout second).then (good layout mul add mulBuffers reserve)
include addBuffers in
theorem component_buffers (second : Bool) : (component layout mul add mulBuffers reserve second).program.code.memBound ≤ max 3 slots + 1 :=
  max_le ((coordinateInput_buffers layout second).trans (by omega)) (good_buffers layout mul add mulBuffers reserve addBuffers)
def bad : Implementation .unit layout.bad layout.pair
    (fun value => (value.2.2.1 + value.1 * value.2.1.1, value.2.2.2 + value.1 * value.2.1.2)) :=
  (component layout mul add mulBuffers reserve false).pair (component layout mul add mulBuffers reserve true) (by decide) layout.wordFits
    (layout.nameFits _ (component_buffers layout mul add mulBuffers reserve addBuffers false) (by have := layout.wordFits; omega))
    (layout.nameFits _ (component_buffers layout mul add mulBuffers reserve addBuffers true) (by have := layout.wordFits; omega))
    (layout.fits_of_le (by rw [Layouts.bad_words]; omega))
    (layout.fits_of_le (by rw [Layouts.bad_words]; omega)) layout.pair.representation.fits
theorem bad_buffers : (bad layout mul add mulBuffers reserve addBuffers).program.code.memBound ≤ max 3 slots + 2 :=
  (Implementation.pair_buffers (firstBuffers := max 3 slots + 1) (secondBuffers := max 3 slots + 1) _ _ _ _ _ _ _ _
    (component_buffers layout mul add mulBuffers reserve addBuffers false)
    (component_buffers layout mul add mulBuffers reserve addBuffers true)).trans (by omega)

end Signatures.Runtime.CaliperBackend.BLSAccumulate
