import Signatures.Runtime.Caliper.BLSAccumulate

/-! Scalar-primitive budgets imply budgets for both complete accumulator
updates. Pair updates invoke multiplication and addition twice; all routing,
retention and copied payload words contribute explicit overhead. -/

namespace Signatures.Runtime.CaliperBackend.BLSAccumulate
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : Layouts w F)

theorem coefficient_bounded : (coefficient layout).BoundedBy
    (8 * layout.scalar.representation.encoding.words) (26 * layout.scalar.representation.encoding.words + 14) :=
  Implementation.first_boundedBy _ _ _ _
theorem pairSelect_bounded (second : Bool) : (pairSelect layout second).BoundedBy
    (16 * layout.scalar.representation.encoding.words) (52 * layout.scalar.representation.encoding.words + 14) := by
  cases second
  · apply (Implementation.first_boundedBy _ _ _ _).mono
    all_goals rw [Layouts.pair_words]; omega
  · apply (Implementation.second_boundedBy _ _ _ _).mono
    all_goals rw [Layouts.pair_words]; omega
theorem coordinate_bounded (accumulator second : Bool) : (coordinate layout accumulator second).BoundedBy
    (56 * layout.scalar.representation.encoding.words) (182 * layout.scalar.representation.encoding.words + 44) := by
  apply (((Implementation.second_boundedBy layout.scalar layout.pairs layout.wordFits _).then
    (pairSelect_bounded layout accumulator)).then (BLSResponse.pointSelect_bounded layout.arithmetic second)).mono
  all_goals simp only [Layouts.pairs_words, Layouts.arithmetic_point]; omega
theorem coordinatePair_bounded (second : Bool) : (coordinatePair layout second).BoundedBy
    (424 * layout.scalar.representation.encoding.words) (1378 * layout.scalar.representation.encoding.words + 212) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (coordinate_bounded layout false second) (coordinate_bounded layout true second)).mono
  all_goals rw [Layouts.bad_words]; omega
theorem coordinateInput_bounded (second : Bool) : (coordinateInput layout second).BoundedBy
    (760 * layout.scalar.representation.encoding.words) (2470 * layout.scalar.representation.encoding.words + 350) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (coefficient_bounded layout) (coordinatePair_bounded layout second)).mono
  all_goals simp only [Layouts.bad_words, Layouts.pair_words]; omega

variable [Mul F] [Add F]
    (mul : Implementation .unit layout.pair layout.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.pair layout.scalar (fun value => value.1 + value.2))
    {mulTime mulCode addTime addCode : Nat}
    (mulBound : mul.BoundedBy mulTime mulCode) (addBound : add.BoundedBy addTime addCode)
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)

def goodTime (mulTime addTime : Nat) : Nat := mulTime + addTime + 472 * layout.scalar.representation.encoding.words
def goodCode (mulCode addCode : Nat) : Nat := mulCode + addCode + 1534 * layout.scalar.representation.encoding.words + 322
def badTime (mulTime addTime : Nat) : Nat := 2 * mulTime + 2 * addTime + 2776 * layout.scalar.representation.encoding.words
def badCode (mulCode addCode : Nat) : Nat := 2 * mulCode + 2 * addCode + 9022 * layout.scalar.representation.encoding.words + 1470

include mulBound in
omit [Add F] in
theorem term_bounded : (term layout mul).BoundedBy
    (240 * layout.scalar.representation.encoding.words + mulTime)
    (780 * layout.scalar.representation.encoding.words + 168 + mulCode) := by
  apply ((BLSResponse.goodArguments_bounded layout.arithmetic false).then mulBound).mono
  all_goals simp only [Layouts.arithmetic_scalar, Layouts.arithmetic_point]; omega
include mulBound in
omit [Add F] in
theorem addArgs_bounded : (addArgs layout mul mulBuffers reserve).BoundedBy
    (472 * layout.scalar.representation.encoding.words + mulTime)
    (1534 * layout.scalar.representation.encoding.words + 321 + mulCode) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _
    (BLSResponse.goodPoint_bounded layout.arithmetic true) (term_bounded layout mul mulBound)).mono
  all_goals simp only [BLSResponse.Layouts.config_words, Layouts.arithmetic_scalar, Layouts.arithmetic_point]; omega
include mulBound addBound in
theorem good_bounded : (good layout mul add mulBuffers reserve).BoundedBy (goodTime layout mulTime addTime) (goodCode layout mulCode addCode) := by
  apply ((addArgs_bounded layout mul mulBound mulBuffers reserve).then addBound).mono
  all_goals dsimp only [goodTime, goodCode]; omega
include mulBound addBound in
theorem component_bounded (second : Bool) : (component layout mul add mulBuffers reserve second).BoundedBy
    (1232 * layout.scalar.representation.encoding.words + mulTime + addTime)
    (4004 * layout.scalar.representation.encoding.words + 673 + mulCode + addCode) := by
  apply ((coordinateInput_bounded layout second).then (good_bounded layout mul add mulBound addBound mulBuffers reserve)).mono
  all_goals dsimp only [goodTime, goodCode]; omega
variable (addBuffers : add.program.code.memBound ≤ slots)
include mulBound addBound in
theorem bad_bounded : (bad layout mul add mulBuffers reserve addBuffers).BoundedBy (badTime layout mulTime addTime) (badCode layout mulCode addCode) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _
    (component_bounded layout mul add mulBound addBound mulBuffers reserve false)
    (component_bounded layout mul add mulBound addBound mulBuffers reserve true)).mono
  all_goals simp only [Layouts.bad_words]; dsimp only [badTime, badCode]; omega

end Signatures.Runtime.CaliperBackend.BLSAccumulate
