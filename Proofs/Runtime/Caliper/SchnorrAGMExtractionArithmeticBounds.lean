import Proofs.Runtime.Caliper.SchnorrAGMExtractionArithmetic
import Proofs.Runtime.Caliper.SchnorrAGMEntryReadSource

/-! Explicit bounds for the terminal quotient and its absent-explanation branch.
Both stored branches, all copies and each scalar primitive are accounted for. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.ExtractionArithmetic
open Caliper BoundedSource
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

theorem optional_words : layout.optionalAffine.representation.encoding.words = 2 * layout.scalar.representation.encoding.words + 1 := by
  change 1 + (_ + _) = _
  omega

theorem entry_bounded : (entry layout).BoundedBy
    (24 * layout.scalar.representation.encoding.words + 8) (78 * layout.scalar.representation.encoding.words + 40) := by
  apply (Implementation.first_boundedBy _ _ _ _).mono
  all_goals rw [Layouts.entry_words]; omega

theorem optional_bounded : (optional layout).BoundedBy
    (40 * layout.scalar.representation.encoding.words + 16) (130 * layout.scalar.representation.encoding.words + 81) := by
  apply ((entry_bounded layout).then (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals rw [optional_words]; omega

theorem affine_bounded : (affine layout).BoundedBy
    (56 * layout.scalar.representation.encoding.words + 16) (182 * layout.scalar.representation.encoding.words + 96) := by
  apply ((optional_bounded layout).then (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals rw [Layouts.affine_words]; omega

theorem challenge_bounded : (challenge layout).BoundedBy
    (32 * layout.scalar.representation.encoding.words + 8) (104 * layout.scalar.representation.encoding.words + 55) := by
  apply ((entry_bounded layout).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals omega

theorem constant_bounded : (constant layout).BoundedBy
    (64 * layout.scalar.representation.encoding.words + 16) (208 * layout.scalar.representation.encoding.words + 111) := by
  apply ((affine_bounded layout).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals omega

theorem secret_bounded : (secret layout).BoundedBy
    (64 * layout.scalar.representation.encoding.words + 16) (208 * layout.scalar.representation.encoding.words + 111) := by
  apply ((affine_bounded layout).then (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals omega

theorem response_bounded : (response layout).BoundedBy
    (8 * layout.scalar.representation.encoding.words + 0) (26 * layout.scalar.representation.encoding.words + 14) := by
  apply (Implementation.second_boundedBy _ _ _ _).mono
  all_goals omega

theorem present_bounded : (present layout).BoundedBy
    (40 * layout.scalar.representation.encoding.words + 24) (130 * layout.scalar.representation.encoding.words + 122) := by
  apply ((optional_bounded layout).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals rw [show layout.boolean.representation.encoding.words = 1 from rfl]

theorem subtractionArgs_bounded : (subtractionArgs layout).BoundedBy
    (332 * layout.scalar.representation.encoding.words + 68) (1079 * layout.scalar.representation.encoding.words + 418) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (response_bounded layout) (constant_bounded layout)).mono
  all_goals rw [input_words]; omega
theorem additionArgs_bounded : (additionArgs layout).BoundedBy
    (356 * layout.scalar.representation.encoding.words + 76) (1157 * layout.scalar.representation.encoding.words + 459) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (secret_bounded layout) (challenge_bounded layout)).mono
  all_goals rw [input_words]; omega

def timeBudget (addTime subTime divTime : Nat) : Nat :=
  1300 * layout.scalar.representation.encoding.words + 339 + addTime + subTime + divTime
def codeBudget (addWords subWords divWords : Nat) : Nat :=
  4329 * layout.scalar.representation.encoding.words + 1886 + addWords + subWords + divWords

section Bounds
variable [Add F] [Sub F] [Div F]
    (add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2))
    (sub : Implementation .unit layout.affine layout.scalar (fun value => value.1 - value.2))
    (divide : Implementation .unit layout.affine layout.scalar (fun value => value.1 / value.2))
    {slots : Nat} (addBuffers : add.program.code.memBound ≤ slots) (subBuffers : sub.program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w)
    {addTime addWords subTime subWords divTime divWords : Nat}
    (addBound : add.BoundedBy addTime addWords) (subBound : sub.BoundedBy subTime subWords)
    (divBound : divide.BoundedBy divTime divWords)
include subBound in
omit [Add F] [Div F] in
theorem numerator_bounded : (numerator layout sub).BoundedBy
    (332 * layout.scalar.representation.encoding.words + 68 + subTime)
    (1079 * layout.scalar.representation.encoding.words + 419 + subWords) := by
  apply ((subtractionArgs_bounded layout).then subBound).mono <;> omega
include addBound in
omit [Sub F] [Div F] in
theorem denominator_bounded : (denominator layout add).BoundedBy
    (356 * layout.scalar.representation.encoding.words + 76 + addTime)
    (1157 * layout.scalar.representation.encoding.words + 460 + addWords) := by
  apply ((additionArgs_bounded layout).then addBound).mono <;> omega
include addBound subBound in
omit [Div F] in
theorem quotientArgs_bounded : (quotientArgs layout add sub addBuffers subBuffers reserve).BoundedBy
    (948 * layout.scalar.representation.encoding.words + 196 + addTime + subTime)
    (3081 * layout.scalar.representation.encoding.words + 1172 + addWords + subWords) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _
    (numerator_bounded layout sub subBound) (denominator_bounded layout add addBound)).mono
  all_goals rw [input_words]; omega
include addBound subBound divBound in
theorem quotient_bounded : (quotient layout add sub divide addBuffers subBuffers reserve).BoundedBy
    (948 * layout.scalar.representation.encoding.words + 196 + addTime + subTime + divTime)
    (3081 * layout.scalar.representation.encoding.words + 1173 + addWords + subWords + divWords) := by
  apply ((quotientArgs_bounded layout add sub addBuffers subBuffers reserve addBound subBound).then divBound).mono <;> omega

variable [Zero F] (zeroValid : layout.scalar.valid 0)
include addBound subBound divBound in
theorem bounded : (implementation layout add sub divide addBuffers subBuffers reserve zeroValid).BoundedBy
    (timeBudget layout addTime subTime divTime) (codeBudget layout addWords subWords divWords) := by
  apply (GuardedBranch.implementation_boundedBy (hw := layout.wordFits) (present layout)
    (smallNameFits layout _ (present_buffers layout)) (duplicateFits layout) (tagFits layout)
    ((quotient layout add sub divide addBuffers subBuffers reserve).restrictInput (fun value => value.1.2.1 = true))
    (Implementation.constant _ layout.scalar ⟨0, zeroValid⟩ layout.wordFits)
    (present_bounded layout)
    ((quotient_bounded layout add sub divide addBuffers subBuffers reserve addBound subBound divBound).restrictInput _)
    (Implementation.constant_bounded _ _ _ _)).mono
  all_goals rw [input_words]; dsimp only [timeBudget, codeBudget]; omega
end Bounds

section Names
variable (slotsNamed : Nat)

theorem entry_names : NamesAccounted (entry layout).program.code slotsNamed :=
  Implementation.first_names _ _ _ _ slotsNamed

theorem optional_names : NamesAccounted (optional layout).program.code slotsNamed :=
  (entry_names layout slotsNamed).seq (Implementation.second_names _ _ _ _ slotsNamed)

theorem affine_names : NamesAccounted (affine layout).program.code slotsNamed :=
  (optional_names layout slotsNamed).seq (Implementation.second_names _ _ _ _ slotsNamed)

theorem challenge_names : NamesAccounted (challenge layout).program.code slotsNamed :=
  (entry_names layout slotsNamed).seq (Implementation.first_names _ _ _ _ slotsNamed)

theorem constant_names : NamesAccounted (constant layout).program.code slotsNamed :=
  (affine_names layout slotsNamed).seq (Implementation.first_names _ _ _ _ slotsNamed)

theorem secret_names : NamesAccounted (secret layout).program.code slotsNamed :=
  (affine_names layout slotsNamed).seq (Implementation.second_names _ _ _ _ slotsNamed)

theorem response_names : NamesAccounted (response layout).program.code slotsNamed :=
  Implementation.second_names _ _ _ _ slotsNamed

theorem present_names : NamesAccounted (present layout).program.code slotsNamed :=
  (optional_names layout slotsNamed).seq (Implementation.first_names _ _ _ _ slotsNamed)

theorem subtractionArgs_names : NamesAccounted (subtractionArgs layout).program.code slotsNamed :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (response_names layout slotsNamed) (constant_names layout slotsNamed)
theorem additionArgs_names : NamesAccounted (additionArgs layout).program.code slotsNamed :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (secret_names layout slotsNamed) (challenge_names layout slotsNamed)

variable [Add F] [Sub F] [Div F]
    (add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2))
    (sub : Implementation .unit layout.affine layout.scalar (fun value => value.1 - value.2))
    (divide : Implementation .unit layout.affine layout.scalar (fun value => value.1 / value.2))
    {slots : Nat} (addBuffers : add.program.code.memBound ≤ slots) (subBuffers : sub.program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w)
    (addNames : NamesAccounted add.program.code slotsNamed) (subNames : NamesAccounted sub.program.code slotsNamed)
    (divNames : NamesAccounted divide.program.code slotsNamed)
include addNames subNames in
omit [Div F] in
theorem quotientArgs_names : NamesAccounted (quotientArgs layout add sub addBuffers subBuffers reserve).program.code slotsNamed :=
  Implementation.pair_names _ _ _ _ _ _ _ _
    ((subtractionArgs_names layout slotsNamed).seq subNames) ((additionArgs_names layout slotsNamed).seq addNames)
include addNames subNames divNames in
theorem quotient_names : NamesAccounted (quotient layout add sub divide addBuffers subBuffers reserve).program.code slotsNamed :=
  (quotientArgs_names layout slotsNamed add sub addBuffers subBuffers reserve addNames subNames).seq divNames
variable [Zero F] (zeroValid : layout.scalar.valid 0)
include addNames subNames divNames in
theorem names : NamesAccounted (implementation layout add sub divide addBuffers subBuffers reserve zeroValid).program.code slotsNamed :=
  GuardedBranch.implementation_names (hw := layout.wordFits) (present layout)
    (smallNameFits layout _ (present_buffers layout)) (duplicateFits layout) (tagFits layout)
    ((quotient layout add sub divide addBuffers subBuffers reserve).restrictInput (fun value => value.1.2.1 = true))
    (Implementation.constant _ layout.scalar ⟨0, zeroValid⟩ layout.wordFits) (present_names layout slotsNamed)
    (quotient_names layout slotsNamed add sub divide addBuffers subBuffers reserve addNames subNames divNames)
    (Implementation.constant_names _ _ _ _ slotsNamed)
end Names

variable [Field F]
theorem value_encode (entry : Schnorr.AGM.Reduction.Entry F) (z : F) :
    value (Signatures.Runtime.SchnorrAGM.Native.encodeEntry entry, z) = Signatures.Runtime.SchnorrAGM.entrySolution z entry := by
  rcases entry with ⟨challenge, affine⟩
  cases affine <;> rfl

end Signatures.Runtime.CaliperBackend.SchnorrAGM.ExtractionArithmetic
