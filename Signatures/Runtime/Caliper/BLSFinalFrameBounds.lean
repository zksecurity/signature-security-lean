import Signatures.Runtime.Caliper.BLSFinalFrame

/-! The final BLS frame charges the numerator addition, all retained data and
cache/default packing. Only the named scalar addition supplies a budget. -/
namespace Signatures.Runtime.CaliperBackend.BLSFinalFrame
open Caliper BoundedSource
variable {w : Nat} {M F : Type} (layout : BLSPrivateAccumulate.Layouts w M F)

theorem target_bounded : (target layout).BoundedBy (16 * layout.good.width) (52 * layout.good.width + 29) := by
  apply ((Implementation.second_boundedBy _ _ _ _).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals
    have := sizes layout
    have := CacheTargetFrame.key_size layout.good
    simp only [context, Layout.prod_words, BLSPrivateAccumulate.Layouts.good] at *
    omega
theorem operands_bounded : (operands layout).BoundedBy (16 * layout.good.width) (52 * layout.good.width + 29) := by
  apply ((Implementation.second_boundedBy _ _ _ _).then (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals have := sizes layout; simp only [context, Layout.prod_words] at *; omega
theorem evaluated_bounded : (evaluated layout).BoundedBy (8 * layout.good.width) (26 * layout.good.width + 14) := by
  apply (Implementation.first_boundedBy _ _ _ _).mono
  all_goals have := layout.good.sizes; simp only [BLSPrivateAccumulate.Layouts.good, CacheRead.output, Layout.prod_words] at *; omega

variable [Add F] (add : Implementation .unit layout.arithmetic.pair layout.cache.value (fun value => value.1 + value.2))
    {slots : Nat} (addBuffers : add.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)
    {addTime addWords : Nat} (bound : add.BoundedBy addTime addWords)
include bound in
theorem numerator_bounded : (numerator layout add).BoundedBy (16 * layout.good.width + addTime)
    (52 * layout.good.width + 30 + addWords) := by
  apply ((operands_bounded layout).then bound).mono <;> omega
include bound in
theorem saved_bounded : (saved layout add addBuffers reserve).BoundedBy (136 * layout.good.width + addTime)
    (442 * layout.good.width + 183 + addWords) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (target_bounded layout) (numerator_bounded layout add bound)).mono
  all_goals
    have := sizes layout
    have := CacheTargetFrame.key_size layout.good
    have := layout.good.base_sizes
    simp only [BLSPrivateAccumulate.Layouts.good] at *
    omega
include bound in
theorem normalize_bounded : (normalize layout add addBuffers reserve).BoundedBy (248 * layout.good.width + addTime)
    (806 * layout.good.width + 321 + addWords) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (evaluated_bounded layout) (saved_bounded layout add addBuffers reserve bound)).mono
  all_goals
    have := sizes layout
    have := layout.good.sizes
    have := CacheTargetFrame.sizes layout.good
    simp only [BLSPrivateAccumulate.Layouts.good] at *
    omega

variable [Zero F] [DecidableEq M] (zeroValid : layout.cache.value.valid 0)
include bound in
theorem prepared_bounded : (prepared layout add addBuffers reserve zeroValid).BoundedBy
    (248 * layout.good.width + addTime) (806 * layout.good.width + 321 + addWords) :=
  ⟨fun value => (normalize_bounded layout add addBuffers reserve bound).time_le ⟨value.val, value.property.1⟩,
    (normalize_bounded layout add addBuffers reserve bound).code_le⟩
def goodTime (addTime : Nat) : Nat := 864 * layout.good.width + addTime
def goodWords (addWords : Nat) : Nat := 2808 * layout.good.width + 1116 + addWords
include bound in
theorem good_bounded : (good layout add addBuffers reserve zeroValid).BoundedBy (goodTime layout addTime) (goodWords layout addWords) := by
  apply ((prepared_bounded layout add addBuffers reserve bound zeroValid).then
    (CacheTargetFrame.implementation_bounded layout.good (zero layout zeroValid))).mono
  all_goals dsimp only [goodTime, goodWords, CacheTargetFrame.timeBudget, CacheTargetFrame.codeBudget]; omega
omit [Add F] in
theorem bad_bounded : (bad layout zeroValid).BoundedBy (CacheTargetFrame.timeBudget layout.bad) (CacheTargetFrame.codeBudget layout.bad) :=
  CacheTargetFrame.implementation_bounded _ _
end Signatures.Runtime.CaliperBackend.BLSFinalFrame
