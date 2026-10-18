import Signatures.Runtime.Caliper.BLSResponse

/-! Uniform budgets for the constructed BLS response code. The only supplied
budgets are for scalar multiplication and addition. All selection, retention
and copying is charged by the actual structural implementations. -/

namespace Signatures.Runtime.CaliperBackend.BLSResponse

open Caliper BoundedSource

variable {w : Nat} {F G : Type} (layout : Layouts w F G)

theorem pointSelect_bounded (second : Bool) : (pointSelect layout second).BoundedBy
    (8 * layout.point.representation.encoding.words) (26 * layout.point.representation.encoding.words + 14) := by
  cases second
  · exact Implementation.first_boundedBy _ _ _ _
  · exact Implementation.second_boundedBy _ _ _ _

theorem scalarSelect_bounded (first : Bool) : (scalarSelect layout first).BoundedBy
    (8 * layout.scalar.representation.encoding.words) (26 * layout.scalar.representation.encoding.words + 14) := by
  cases first
  · exact Implementation.second_boundedBy _ _ _ _
  · exact Implementation.first_boundedBy _ _ _ _

theorem goodScalar_bounded : (goodScalar layout).BoundedBy
    (8 * layout.scalar.representation.encoding.words) (26 * layout.scalar.representation.encoding.words + 14) :=
  Implementation.first_boundedBy _ _ _ _

theorem goodPoint_bounded (signing : Bool) : (goodPoint layout signing).BoundedBy
    (24 * layout.point.representation.encoding.words) (78 * layout.point.representation.encoding.words + 29) := by
  apply ((Implementation.second_boundedBy _ _ _ _).then (pointSelect_bounded layout signing)).mono
  all_goals simp only [Layouts.points_words]; omega

theorem badScalar_bounded (first : Bool) : (badScalar layout first).BoundedBy
    (24 * layout.scalar.representation.encoding.words) (78 * layout.scalar.representation.encoding.words + 29) := by
  apply ((Implementation.first_boundedBy _ _ _ _).then (scalarSelect_bounded layout first)).mono
  all_goals simp only [Layouts.scalars_words]; omega

theorem badPoint_bounded (first : Bool) : (badPoint layout first).BoundedBy
    (8 * layout.scalar.representation.encoding.words + 40 * layout.point.representation.encoding.words)
    (26 * layout.scalar.representation.encoding.words + 130 * layout.point.representation.encoding.words + 44) := by
  apply ((Implementation.second_boundedBy _ _ _ _).then (goodPoint_bounded layout first)).mono
  all_goals simp only [Layouts.config_words]; omega

theorem kappa_bounded : (kappa layout).BoundedBy
    (16 * layout.scalar.representation.encoding.words + 16 * layout.point.representation.encoding.words)
    (52 * layout.scalar.representation.encoding.words + 52 * layout.point.representation.encoding.words + 29) := by
  apply ((Implementation.second_boundedBy _ _ _ _).then (goodScalar_bounded layout)).mono
  all_goals simp only [Layouts.config_words]; omega

theorem goodArguments_bounded (signing : Bool) : (goodArguments layout signing).BoundedBy
    (96 * layout.scalar.representation.encoding.words + 144 * layout.point.representation.encoding.words)
    (312 * layout.scalar.representation.encoding.words + 468 * layout.point.representation.encoding.words + 167) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (goodScalar_bounded layout) (goodPoint_bounded layout signing)).mono
  all_goals simp only [Layouts.config_words]; omega

theorem termArguments_bounded (first : Bool) : (termArguments layout first).BoundedBy
    (224 * layout.scalar.representation.encoding.words + 160 * layout.point.representation.encoding.words)
    (728 * layout.scalar.representation.encoding.words + 520 * layout.point.representation.encoding.words + 197) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (badScalar_bounded layout first) (badPoint_bounded layout first)).mono
  all_goals simp only [Layouts.badInput_words]; omega

variable [SMul F G] [Add G]
    (scale : Implementation .unit layout.scaleArgs layout.point (fun value => value.1 • value.2))
    (add : Implementation .unit layout.points layout.point (fun value => value.1 + value.2))
    {scaleTime scaleWords addTime addWords : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (addBound : add.BoundedBy addTime addWords)

def goodTime (scaleTime : Nat) : Nat := scaleTime +
  96 * layout.scalar.representation.encoding.words + 144 * layout.point.representation.encoding.words
def goodWords (scaleWords : Nat) : Nat := scaleWords +
  312 * layout.scalar.representation.encoding.words + 468 * layout.point.representation.encoding.words + 168
def badTime (signing : Bool) (scaleTime addTime : Nat) : Nat :=
  if signing then 3 * scaleTime + addTime + 812 * layout.scalar.representation.encoding.words + 612 * layout.point.representation.encoding.words
  else 2 * scaleTime + addTime + 604 * layout.scalar.representation.encoding.words + 476 * layout.point.representation.encoding.words
def badWords (signing : Bool) (scaleWords addWords : Nat) : Nat :=
  if signing then 3 * scaleWords + addWords + 2639 * layout.scalar.representation.encoding.words + 1989 * layout.point.representation.encoding.words + 675
  else 2 * scaleWords + addWords + 1963 * layout.scalar.representation.encoding.words + 1547 * layout.point.representation.encoding.words + 521

include scaleBound in
omit [Add G] in
theorem good_bounded (signing : Bool) : (good layout scale signing).BoundedBy (goodTime layout scaleTime) (goodWords layout scaleWords) := by
  apply ((goodArguments_bounded layout signing).then scaleBound).mono
  all_goals dsimp only [goodTime, goodWords]; omega

include scaleBound in
omit [Add G] in
theorem term_bounded (first : Bool) : (term layout scale first).BoundedBy
    (scaleTime + 224 * layout.scalar.representation.encoding.words + 160 * layout.point.representation.encoding.words)
    (scaleWords + 728 * layout.scalar.representation.encoding.words + 520 * layout.point.representation.encoding.words + 198) := by
  apply ((termArguments_bounded layout first).then scaleBound).mono <;> omega

variable {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (reserve : slots + 3 < 2 ^ w)

include scaleBound in
omit [Add G] in
theorem pointArguments_bounded : (pointArguments layout scale scaleBuffers reserve).BoundedBy
    (2 * scaleTime + 604 * layout.scalar.representation.encoding.words + 476 * layout.point.representation.encoding.words)
    (2 * scaleWords + 1963 * layout.scalar.representation.encoding.words + 1547 * layout.point.representation.encoding.words + 520) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _
    (term_bounded layout scale scaleBound true) (term_bounded layout scale scaleBound false)).mono
  all_goals simp only [Layouts.badInput_words]; omega

include scaleBound addBound in
theorem point_bounded : (point layout scale add scaleBuffers reserve).BoundedBy
    (badTime layout false scaleTime addTime) (badWords layout false scaleWords addWords) := by
  apply ((pointArguments_bounded layout scale scaleBound scaleBuffers reserve).then addBound).mono
  all_goals simp only [badTime, badWords, Bool.false_eq_true, ↓reduceIte]; omega

variable (addBuffers : add.program.code.memBound ≤ slots)

include scaleBound addBound in
theorem signingArguments_bounded : (signingArguments layout scale add scaleBuffers reserve addBuffers).BoundedBy
    (2 * scaleTime + addTime + 812 * layout.scalar.representation.encoding.words + 612 * layout.point.representation.encoding.words)
    (2 * scaleWords + addWords + 2639 * layout.scalar.representation.encoding.words + 1989 * layout.point.representation.encoding.words + 674) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (kappa_bounded layout)
    (point_bounded layout scale add scaleBound addBound scaleBuffers reserve)).mono
  all_goals simp only [Layouts.badInput_words, badTime, badWords, Bool.false_eq_true, ↓reduceIte]; omega

include scaleBound addBound in
theorem bad_bounded (signing : Bool) : (bad layout scale add scaleBuffers reserve addBuffers signing).BoundedBy
    (badTime layout signing scaleTime addTime) (badWords layout signing scaleWords addWords) := by
  cases signing
  · exact point_bounded layout scale add scaleBound addBound scaleBuffers reserve
  · apply ((signingArguments_bounded layout scale add scaleBound addBound scaleBuffers reserve addBuffers).then scaleBound).mono
    all_goals simp only [badTime, badWords, ↓reduceIte]; omega

end Signatures.Runtime.CaliperBackend.BLSResponse
