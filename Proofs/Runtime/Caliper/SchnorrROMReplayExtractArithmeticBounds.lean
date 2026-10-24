import Proofs.Runtime.Caliper.SchnorrROMReplayExtractArithmetic

/-! Uniform time, stored-code, buffer and name bounds for the executed
extraction arithmetic. Both equality scans, every projection, the retained
copies of the guarded branches, the pair of differences and both primitive
contracts are charged. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Extract
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

/-- Time and stored-code budgets of the field primitives. -/
structure Arithmetic.Budget [Sub F] [Div F] (arith : Arithmetic config) where
  subTime : Nat
  subWords : Nat
  divideTime : Nat
  divideWords : Nat
  sub : arith.sub.BoundedBy subTime subWords
  divide : arith.divide.BoundedBy divideTime divideWords

theorem points_words : (points config).representation.encoding.words = 2 * config.point.representation.encoding.words := by
  change config.point.representation.encoding.words + config.point.representation.encoding.words = _
  omega

theorem commitments_bounded : (commitments config).BoundedBy
    (16 * config.point.representation.encoding.words) (52 * config.point.representation.encoding.words + 14) := by
  apply (Implementation.first_boundedBy _ _ _ _).mono <;> rw [points_words] <;> omega
theorem rest_bounded : (rest config).BoundedBy 32 118 :=
  Implementation.second_boundedBy _ _ _ _
theorem responses_bounded : (responses config).BoundedBy 48 185 :=
  (rest_bounded config).then (Implementation.first_boundedBy _ _ _ _)
theorem challenges_bounded : (challenges config).BoundedBy 48 185 :=
  (rest_bounded config).then (Implementation.second_boundedBy _ _ _ _)

section Equality
variable [DecidableEq F] [DecidableEq G]
omit [DecidableEq F] in
theorem sameCommitment_bounded : (sameCommitment config).BoundedBy
    (22 * config.point.representation.encoding.words + 3) (82 * config.point.representation.encoding.words + 28) := by
  have same : config.handler.core.arithmetic.point.representation.encoding.words = config.point.representation.encoding.words := rfl
  apply ((commitments_bounded config).then (EncodedEquality.implementation_boundedBy _ _ _)).mono <;> omega
omit [DecidableEq G] in
theorem sameChallenge_bounded : (sameChallenge config).BoundedBy 57 229 :=
  (challenges_bounded config).then (EncodedEquality.implementation_boundedBy _ _ _)
end Equality

theorem inject_bounded : (inject config).BoundedBy 16 66 := by
  constructor
  · intro value
    exact inr_time config.handler.sampler.tape.unit.representation config.handler.sampler.tape.scalar.representation
      config.sampler.wordFits (choiceFits config) value
  · exact inr_words config.handler.sampler.tape.unit.representation config.handler.sampler.tape.scalar.representation
      config.sampler.wordFits (choiceFits config)
theorem fallbackConstant_bounded {A : Type} (input : Layout w A) : (fallbackConstant config input).BoundedBy 16 66 :=
  Implementation.constant_bounded _ _ _ _

def coreTime (subTime divideTime : Nat) : Nat :=
  430 * config.point.representation.encoding.words + 1200 + 2 * subTime + divideTime
def coreWords (subWords divideWords : Nat) : Nat :=
  1520 * config.point.representation.encoding.words + 4600 + 2 * subWords + divideWords

section Arithmetic
variable [Sub F] [Div F] (arith : Arithmetic config) (budget : Arithmetic.Budget config arith)

theorem numerator_bounded : (numerator config arith).BoundedBy (48 + budget.subTime) (186 + budget.subWords) := by
  apply ((responses_bounded config).then budget.sub).mono <;> omega
theorem denominator_bounded : (denominator config arith).BoundedBy (48 + budget.subTime) (186 + budget.subWords) := by
  apply ((challenges_bounded config).then budget.sub).mono <;> omega
theorem quotient_bounded : (quotient config arith).BoundedBy
    (2 * budget.subTime + budget.divideTime + 52 * (quad config).representation.encoding.words + 148)
    (2 * budget.subWords + budget.divideWords + 169 * (quad config).representation.encoding.words + 666) := by
  have paired := Implementation.pair_boundedBy (numerator config arith) (denominator config arith) config.sampler.wordFits
    (nameFits config arith _ (numerator_buffers config arith)) (nameFits config arith _ (denominator_buffers config arith))
    (duplicateFits config) (middleFits config)
    (config.handler.core.arithmetic.fits_of_le (by change 1 + 1 ≤ 16 * (1 + config.point.representation.encoding.words); omega))
    (numerator_bounded config arith budget) (denominator_bounded config arith budget)
  have one : config.handler.core.scalar.representation.encoding.words = 1 := rfl
  apply (paired.then budget.divide).mono <;> omega
theorem extracted_bounded : (extracted config arith).BoundedBy
    (2 * budget.subTime + budget.divideTime + 52 * (quad config).representation.encoding.words + 164)
    (2 * budget.subWords + budget.divideWords + 169 * (quad config).representation.encoding.words + 733) := by
  apply ((quotient_bounded config arith budget).then (inject_bounded config)).mono <;> omega

variable [DecidableEq F] [DecidableEq G]
theorem inner_bounded : (inner config arith).BoundedBy
    (2 * budget.subTime + budget.divideTime + 128 * (quad config).representation.encoding.words + 280)
    (2 * budget.subWords + budget.divideWords + 442 * (quad config).representation.encoding.words + 1332) := by
  have bounded := GuardedBranch.implementation_boundedBy (hw := config.sampler.wordFits)
    ((sameChallenge config).restrictInput (fun value => sameCommitmentTest value = true))
    (smallNameFits config _ (sameChallenge_buffers config)) (duplicateFits config) (tagFits config)
    (fallbackConstant config _)
    (((extracted config arith).restrictInput (fun value => sameCommitmentTest value = true)).restrictInput
      (fun value => sameChallengeTest value = false))
    ((sameChallenge_bounded config).restrictInput _) (fallbackConstant_bounded config _)
    (((extracted_bounded config arith budget).restrictInput _).restrictInput _)
  apply bounded.mono
  · change 57 + 16 + _ + 76 * (quad config).representation.encoding.words + 43 ≤ _
    omega
  · change 229 + 66 + _ + 273 * (quad config).representation.encoding.words + 304 ≤ _
    omega
theorem guarded_bounded : (guarded config arith).BoundedBy
    (coreTime config budget.subTime budget.divideTime) (coreWords config budget.subWords budget.divideWords) := by
  have bounded := GuardedBranch.implementation_boundedBy (hw := config.sampler.wordFits) (sameCommitment config)
    (smallNameFits config _ (sameCommitment_buffers config)) (duplicateFits config) (tagFits config)
    (inner config arith) (fallbackConstant config _)
    (sameCommitment_bounded config) (inner_bounded config arith budget) (fallbackConstant_bounded config _)
  have size := quad_words config
  apply bounded.mono
  · unfold coreTime
    omega
  · unfold coreWords
    omega
theorem core_bounded : (core config arith).BoundedBy
    (coreTime config budget.subTime budget.divideTime) (coreWords config budget.subWords budget.divideWords) :=
  (guarded_bounded config arith budget).castFunction _
end Arithmetic

section Buffers
variable [DecidableEq F] [DecidableEq G] [Sub F] [Div F] (arith : Arithmetic config)
theorem core_buffers : (core config arith).program.code.memBound ≤ max 6 (arith.slots + 1) := by
  have innerBound := GuardedBranch.implementation_buffers (hw := config.sampler.wordFits)
    ((sameChallenge config).restrictInput (fun value => sameCommitmentTest value = true))
    (smallNameFits config _ (sameChallenge_buffers config)) (duplicateFits config) (tagFits config)
    (fallbackConstant config _)
    (((extracted config arith).restrictInput (fun value => sameCommitmentTest value = true)).restrictInput
      (fun value => sameChallengeTest value = false))
    (sameChallenge_buffers config) (Implementation.constant_buffers _ _ _ _) (extracted_buffers config arith)
  have outerBound := GuardedBranch.implementation_buffers (hw := config.sampler.wordFits) (sameCommitment config)
    (smallNameFits config _ (sameCommitment_buffers config)) (duplicateFits config) (tagFits config)
    (inner config arith) (fallbackConstant config _)
    (sameCommitment_buffers config) innerBound (Implementation.constant_buffers _ _ _ _)
  exact outerBound.trans (by omega)
end Buffers

section Names
variable [Sub F] [Div F] (arith : Arithmetic config)

/-- All extractor arithmetic names fit within the primitive reservation. -/
def nameSlots : Nat := max 5 arith.slots

theorem commitments_names : NamesAccounted (commitments config).program.code (nameSlots config arith) :=
  Implementation.first_names _ _ _ _ _
theorem responses_names : NamesAccounted (responses config).program.code (nameSlots config arith) :=
  (Implementation.second_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _)
theorem challenges_names : NamesAccounted (challenges config).program.code (nameSlots config arith) :=
  (Implementation.second_names _ _ _ _ _).seq (Implementation.second_names _ _ _ _ _)
variable [DecidableEq F] [DecidableEq G]
omit [DecidableEq F] in
theorem sameCommitment_names : NamesAccounted (sameCommitment config).program.code (nameSlots config arith) :=
  (commitments_names config arith).seq
    ((EncodedEquality.implementation_names _ _ _ _).accounted.mono (by unfold nameSlots; omega))
omit [DecidableEq G] in
theorem sameChallenge_names : NamesAccounted (sameChallenge config).program.code (nameSlots config arith) :=
  (challenges_names config arith).seq
    ((EncodedEquality.implementation_names _ _ _ _).accounted.mono (by unfold nameSlots; omega))
omit [DecidableEq F] [DecidableEq G] in
theorem extracted_names : NamesAccounted (extracted config arith).program.code (nameSlots config arith) := by
  have sub := arith.subNames.accounted.mono (b := nameSlots config arith) (by unfold nameSlots; omega)
  have divide := arith.divideNames.accounted.mono (b := nameSlots config arith) (by unfold nameSlots; omega)
  have injected := (inr_names config.handler.sampler.tape.unit.representation config.handler.sampler.tape.scalar.representation
    config.sampler.wordFits (choiceFits config)).accounted.mono (b := nameSlots config arith) (by unfold nameSlots; omega)
  exact ((Implementation.pair_names _ _ _ _ _ _ _ _ ((responses_names config arith).seq sub)
    ((challenges_names config arith).seq sub)).seq divide).seq injected
theorem core_names : NamesAccounted (core config arith).program.code (nameSlots config arith) := by
  have innerNames := GuardedBranch.implementation_names (hw := config.sampler.wordFits)
    ((sameChallenge config).restrictInput (fun value => sameCommitmentTest value = true))
    (smallNameFits config _ (sameChallenge_buffers config)) (duplicateFits config) (tagFits config)
    (fallbackConstant config _)
    (((extracted config arith).restrictInput (fun value => sameCommitmentTest value = true)).restrictInput
      (fun value => sameChallengeTest value = false))
    (sameChallenge_names config arith) (Implementation.constant_names _ _ _ _ _) (extracted_names config arith)
  exact GuardedBranch.implementation_names (hw := config.sampler.wordFits) (sameCommitment config)
    (smallNameFits config _ (sameCommitment_buffers config)) (duplicateFits config) (tagFits config)
    (inner config arith) (fallbackConstant config _)
    (sameCommitment_names config arith) innerNames (Implementation.constant_names _ _ _ _ _)
end Names

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Extract
