import Proofs.Runtime.Caliper.BLSExtractArithmetic

/-! Derived costs of the terminal BLS arithmetic, including every projection,
saved input and constructed argument. Only named scalar primitives supply
local budgets; neither extraction branch is supplied as an implementation. -/
namespace Signatures.Runtime.CaliperBackend.BLSExtractArithmetic
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : BLSAccumulate.Layouts w F)

theorem numerator_bounded : (numerator layout).BoundedBy
    (8 * layout.scalar.representation.encoding.words) (26 * layout.scalar.representation.encoding.words + 14) :=
  Implementation.first_boundedBy _ _ _ _
theorem differenceArgs_bounded : (differenceArgs layout).BoundedBy
    (16 * layout.scalar.representation.encoding.words) (52 * layout.scalar.representation.encoding.words + 14) := by
  apply (Implementation.second_boundedBy _ _ _ _).mono
  all_goals rw [BLSAccumulate.Layouts.pair_words]; omega

def goodTime (subTime divTime : Nat) : Nat := 232 * layout.scalar.representation.encoding.words + subTime + divTime
def goodCode (subCode divCode : Nat) : Nat := 754 * layout.scalar.representation.encoding.words + 154 + subCode + divCode
def badTime (subTime negTime divTime : Nat) : Nat := 1160 * layout.scalar.representation.encoding.words + 2 * subTime + negTime + divTime
def badCode (subCode negCode divCode : Nat) : Nat := 3770 * layout.scalar.representation.encoding.words + 552 + 2 * subCode + negCode + divCode

section Subtract
variable [Sub F]
    (sub : Implementation .unit layout.pair layout.scalar (fun value => value.1 - value.2))
    {subTime subCode : Nat} (subBound : sub.BoundedBy subTime subCode)
    {slots : Nat} (subBuffers : sub.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
include subBound in
theorem denominator_bounded : (denominator layout sub).BoundedBy
    (16 * layout.scalar.representation.encoding.words + subTime)
    (52 * layout.scalar.representation.encoding.words + 15 + subCode) := by
  apply ((differenceArgs_bounded layout).then subBound).mono
  all_goals omega
include subBound in
theorem goodArguments_bounded : (goodArguments layout sub subBuffers reserve).BoundedBy
    (232 * layout.scalar.representation.encoding.words + subTime)
    (754 * layout.scalar.representation.encoding.words + 153 + subCode) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _
    (numerator_bounded layout) (denominator_bounded layout sub subBound)).mono
  all_goals rw [BLSAccumulate.Layouts.good_words]; omega
include subBound in
theorem difference_bounded (second : Bool) : (difference layout sub second).BoundedBy
    (424 * layout.scalar.representation.encoding.words + subTime)
    (1378 * layout.scalar.representation.encoding.words + 213 + subCode) := by
  apply (((BLSAccumulate.coordinatePair_bounded layout second).then subBound).castFunction _).mono
  all_goals omega

section Good
variable [Div F]
    (divide : Implementation .unit layout.pair layout.scalar (fun value => value.1 / value.2))
    {divTime divCode : Nat} (divBound : divide.BoundedBy divTime divCode)
include subBound divBound in
theorem good_bounded : (good layout sub subBuffers reserve divide).BoundedBy
    (goodTime layout subTime divTime) (goodCode layout subCode divCode) := by
  apply ((goodArguments_bounded layout sub subBound subBuffers reserve).then divBound).mono
  all_goals dsimp only [goodTime, goodCode]; omega
end Good

section Bad
variable [Neg F] (negate : Implementation .unit layout.scalar layout.scalar Neg.neg)
    {negTime negCode : Nat} (negBound : negate.BoundedBy negTime negCode)
    (negBuffers : negate.program.code.memBound ≤ slots)
include subBound negBound in
theorem negated_bounded : (negated layout sub negate).BoundedBy
    (424 * layout.scalar.representation.encoding.words + subTime + negTime)
    (1378 * layout.scalar.representation.encoding.words + 214 + subCode + negCode) := by
  apply ((difference_bounded layout sub subBound true).then negBound).mono
  all_goals omega
include subBound negBound in
theorem badArguments_bounded : (badArguments layout sub subBuffers reserve negate negBuffers).BoundedBy
    (1160 * layout.scalar.representation.encoding.words + 2 * subTime + negTime)
    (3770 * layout.scalar.representation.encoding.words + 551 + 2 * subCode + negCode) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _
    (negated_bounded layout sub subBound negate negBound) (difference_bounded layout sub subBound false)).mono
  all_goals rw [BLSAccumulate.Layouts.bad_words]; omega
variable [Div F]
    (divide : Implementation .unit layout.pair layout.scalar (fun value => value.1 / value.2))
    {divTime divCode : Nat} (divBound : divide.BoundedBy divTime divCode)
include subBound negBound divBound in
theorem bad_bounded : (bad layout sub subBuffers reserve negate negBuffers divide).BoundedBy
    (badTime layout subTime negTime divTime) (badCode layout subCode negCode divCode) := by
  apply ((badArguments_bounded layout sub subBound subBuffers reserve negate negBound negBuffers).then divBound).mono
  all_goals dsimp only [badTime, badCode]; omega
end Bad
end Subtract
end Signatures.Runtime.CaliperBackend.BLSExtractArithmetic
