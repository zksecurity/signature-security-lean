import Signatures.Runtime.Caliper.CoronResponse

/-! Uniform response budgets derived from the actual projection, test, branch,
pairing and group code. Local overhead is linear in the encoded input width. -/
namespace Signatures.Runtime.CaliperBackend.CoronResponse
open Caliper BoundedSource
variable {w qS : Nat} {F G : Type} (layout : Layouts w F G qS)

theorem scalarValue_bounded : (scalarValue layout).BoundedBy (24 * layout.width) (78 * layout.width + 44) := by
  apply ((Implementation.first_boundedBy _ _ _ _).then (Implementation.first_boundedBy _ _ _ _)).mono
  · change 8 * (layout.scalar.representation.encoding.words + 1) + 8 * layout.scalar.representation.encoding.words ≤ _
    unfold Layouts.width; omega
  · change 26 * (layout.scalar.representation.encoding.words + 1) + 14 + (26 * layout.scalar.representation.encoding.words + 14) + 1 ≤ _
    unfold Layouts.width; omega
theorem coinValue_bounded : (coinValue layout).BoundedBy (24 * layout.width) (78 * layout.width + 44) := by
  apply ((Implementation.first_boundedBy _ _ _ _).then (Implementation.second_boundedBy _ _ _ _)).mono
  · change 8 * (layout.scalar.representation.encoding.words + 1) + 8 * 1 ≤ _
    unfold Layouts.width; omega
  · change 26 * (layout.scalar.representation.encoding.words + 1) + 14 + (26 * 1 + 14) + 1 ≤ _
    unfold Layouts.width; omega

theorem configuration_bounded : (configuration layout).BoundedBy
    (24 * layout.point.representation.encoding.words) (78 * layout.point.representation.encoding.words + 14) := by
  apply (Implementation.second_boundedBy _ _ _ _).mono
  all_goals rw [Layouts.config_words]; omega
theorem tailPoints_bounded : (tailPoints layout).BoundedBy
    (40 * layout.point.representation.encoding.words) (130 * layout.point.representation.encoding.words + 29) := by
  apply ((configuration_bounded layout).then (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals rw [Layouts.points_words]; omega
theorem basePoint_bounded : (basePoint layout).BoundedBy (24 * layout.width) (78 * layout.width + 44) := by
  apply ((configuration_bounded layout).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals unfold Layouts.width; omega
theorem keyPoint_bounded : (keyPoint layout).BoundedBy (24 * layout.width) (78 * layout.width + 44) := by
  apply ((tailPoints_bounded layout).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals unfold Layouts.width; omega
theorem challengePoint_bounded : (challengePoint layout).BoundedBy (24 * layout.width) (78 * layout.width + 44) := by
  apply ((tailPoints_bounded layout).then (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals unfold Layouts.width; omega
theorem selectedPoint_bounded (signing : Bool) :
    (selectedPoint layout signing).BoundedBy (24 * layout.width) (78 * layout.width + 44) := by
  cases signing
  · exact basePoint_bounded layout
  · exact keyPoint_bounded layout
theorem test_bounded : (test layout).BoundedBy (24 * layout.width + 5) (78 * layout.width + 68) := by
  apply ((coinValue_bounded layout).then (Finite.isZero_bounded qS layout.wordFits layout.coinFits)).mono <;> omega
theorem arguments_bounded (signing : Bool) : (arguments layout signing).BoundedBy
    (152 * layout.width) (494 * layout.width + 212) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (scalarValue_bounded layout) (selectedPoint_bounded layout signing)).mono
  all_goals rw [Layouts.input_words]; unfold Layouts.width; omega

variable [Zero G] (zeroValid : layout.point.valid 0)

theorem zeroPoint_bounded : (zeroPoint layout zeroValid).BoundedBy (8 * layout.width) (26 * layout.width + 14) := by
  apply (Implementation.constant_bounded layout.input layout.point ⟨0, zeroValid⟩ layout.wordFits).mono
  all_goals unfold Layouts.width; omega
theorem offset_bounded : (offset layout zeroValid).BoundedBy (132 * layout.width + 48) (455 * layout.width + 430) := by
  have bounded := GuardedBranch.implementation_boundedBy (hw := layout.wordFits) (test layout)
    (nameFits layout _ (test_buffers layout) (by have := layout.wordFits; omega)) layout.duplicateFits layout.tagFits
    ((challengePoint layout).restrictInput (fun value => condition value = true))
    ((zeroPoint layout zeroValid).restrictInput (fun value => condition value = false))
    (test_bounded layout) ((challengePoint_bounded layout).restrictInput _)
    ((zeroPoint_bounded layout zeroValid).restrictInput _)
  apply (bounded.castFunction _).mono
  all_goals rw [Layouts.input_words]; omega

variable [SMul F G]
    (scale : Implementation .unit layout.scaleArgs layout.point (fun value => value.1 • value.2))
    {scaleTime scaleWords : Nat} (scaleBound : scale.BoundedBy scaleTime scaleWords)

include scaleBound in
omit [Zero G] in
theorem scaled_bounded (signing : Bool) : (scaled layout scale signing).BoundedBy
    (scaleTime + 152 * layout.width) (scaleWords + 494 * layout.width + 213) := by
  apply ((arguments_bounded layout signing).then scaleBound).mono <;> omega

def timeBudget (signing : Bool) (scaleTime addTime : Nat) : Nat :=
  if signing then scaleTime + 260 * layout.width + 48
  else scaleTime + addTime + 388 * layout.width + 48
def codeBudget (signing : Bool) (scaleWords addWords : Nat) : Nat :=
  if signing then scaleWords + 871 * layout.width + 599
  else scaleWords + addWords + 1287 * layout.width + 768

include scaleBound in
theorem sign_bounded : (sign layout zeroValid scale).BoundedBy
    (scaleTime + 260 * layout.width + 48) (scaleWords + 871 * layout.width + 599) := by
  have bounded := GuardedBranch.implementation_boundedBy (hw := layout.wordFits) (test layout)
    (nameFits layout _ (test_buffers layout) (by have := layout.wordFits; omega)) layout.duplicateFits layout.tagFits
    ((zeroPoint layout zeroValid).restrictInput (fun value => condition value = true))
    ((scaled layout scale true).restrictInput (fun value => condition value = false))
    (test_bounded layout) ((zeroPoint_bounded layout zeroValid).restrictInput _)
    ((scaled_bounded layout scale scaleBound true).restrictInput _)
  apply (bounded.castFunction _).mono
  all_goals rw [Layouts.input_words]; omega

variable {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (reserve : slots + 3 < 2 ^ w)

include scaleBound in
theorem hashArguments_bounded : (hashArguments layout zeroValid scale scaleBuffers reserve).BoundedBy
    (scaleTime + 388 * layout.width + 48) (scaleWords + 1287 * layout.width + 767) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _
    (scaled_bounded layout scale scaleBound false) (offset_bounded layout zeroValid)).mono
  all_goals rw [Layouts.input_words]; unfold Layouts.width; omega

variable [Add G] (add : Implementation .unit layout.points layout.point (fun value => value.1 + value.2))
    {addTime addWords : Nat} (addBound : add.BoundedBy addTime addWords)

include scaleBound addBound in
theorem reply_bounded (signing : Bool) : (reply layout zeroValid scale add scaleBuffers reserve signing).BoundedBy
    (timeBudget layout signing scaleTime addTime) (codeBudget layout signing scaleWords addWords) := by
  cases signing
  · apply ((hashArguments_bounded layout zeroValid scale scaleBound scaleBuffers reserve).then addBound).mono
    all_goals simp only [timeBudget, codeBudget, Bool.false_eq_true, ↓reduceIte]; omega
  · exact sign_bounded layout zeroValid scale scaleBound

end Signatures.Runtime.CaliperBackend.CoronResponse
