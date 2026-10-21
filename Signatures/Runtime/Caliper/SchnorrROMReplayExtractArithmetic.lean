import Signatures.Runtime.Caliper.SchnorrROMReplayExtractLayout

/-! Executed extraction arithmetic on the routed commitment/response/challenge
frame. Commitment and challenge equality run `EncodedEquality` on the stored
representations; `GuardedBranch` retains the frame and dispatches on the written
Boolean. Field subtraction and division are explicit local implementation
contracts, exactly like the scalar primitives of the AGM extractor. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Extract
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

/-- Field primitives used by the extractor, with buffer-name bounds. -/
structure Arithmetic [Sub F] [Div F] where
  sub : Implementation .unit config.handler.core.arithmetic.scalars config.handler.core.scalar (fun value => value.1 - value.2)
  divide : Implementation .unit config.handler.core.arithmetic.scalars config.handler.core.scalar (fun value => value.1 / value.2)
  slots : Nat
  subNames : NamesBound sub.program.code slots
  divideNames : NamesBound divide.program.code slots
  reserve : slots + 3 < 2 ^ w

theorem choiceFits : 1 + max config.handler.sampler.tape.unit.representation.encoding.words
    config.handler.sampler.tape.scalar.representation.encoding.words < 2 ^ w := by
  change 1 + max 0 1 < 2 ^ w; have := config.sampler.wordFits; omega
def choiceLayout : Layout w (Unit ⊕ F) :=
  config.handler.sampler.tape.unit.sum config.handler.sampler.tape.scalar (width_pos config.sampler.wordFits) (choiceFits config)
def choiceView (value : (choiceLayout config).Value) : Choice config :=
  sumView config.handler.sampler.tape.unit config.handler.sampler.tape.scalar value

theorem quad_small : 2 * (quad config).representation.encoding.words + 2 ≤
    16 * (config.handler.core.arithmetic.scalar.representation.encoding.words +
      config.handler.core.arithmetic.point.representation.encoding.words) := by
  rw [quad_words]
  change _ ≤ 16 * (1 + config.point.representation.encoding.words)
  omega
theorem duplicateFits : (quad config).representation.encoding.words + (quad config).representation.encoding.words < 2 ^ w :=
  config.handler.core.arithmetic.fits_of_le (by have := quad_small config; omega)
theorem tagFits : 1 + (quad config).representation.encoding.words < 2 ^ w :=
  config.handler.core.arithmetic.fits_of_le (by have := quad_small config; omega)
theorem middleFits : config.handler.core.scalar.representation.encoding.words + (quad config).representation.encoding.words < 2 ^ w :=
  config.handler.core.arithmetic.fits_of_le (by have := quad_small config; change 1 + _ ≤ _; omega)

def commitments : Implementation .unit (quad config) (points config) Prod.fst :=
  Implementation.first (by decide) (points config) (pairs config) config.sampler.wordFits _
def rest : Implementation .unit (quad config) (pairs config) Prod.snd :=
  Implementation.second (by decide) (points config) (pairs config) config.sampler.wordFits _
def responses : Implementation .unit (quad config) (scalars config) (fun value => value.2.1) :=
  (rest config).then (Implementation.first (by decide) (scalars config) (scalars config) config.sampler.wordFits _)
def challenges : Implementation .unit (quad config) (scalars config) (fun value => value.2.2) :=
  (rest config).then (Implementation.second (by decide) (scalars config) (scalars config) config.sampler.wordFits _)

section Equality
variable [DecidableEq F] [DecidableEq G]
def sameCommitment : Implementation .unit (quad config) (DataImplementation.boolLayout w (width_pos config.sampler.wordFits))
    (fun value => decide (value.1.1 = value.1.2)) :=
  (commitments config).then (EncodedEquality.implementation .unit config.point config.sampler.wordFits
    (config.handler.core.arithmetic.fits_of_le (by
      change config.point.representation.encoding.words + config.point.representation.encoding.words ≤
        16 * (1 + config.point.representation.encoding.words); omega)))
def sameChallenge : Implementation .unit (quad config) (DataImplementation.boolLayout w (width_pos config.sampler.wordFits))
    (fun value => decide (value.2.2.1 = value.2.2.2)) :=
  (challenges config).then (EncodedEquality.implementation .unit config.handler.core.scalar config.sampler.wordFits
    (config.handler.core.arithmetic.fits_of_le (by
      change 1 + 1 ≤ 16 * (1 + config.point.representation.encoding.words); omega)))
end Equality

theorem commitments_buffers : (commitments config).program.code.memBound ≤ 2 := Implementation.first_buffers _ _ _ _ _
theorem rest_buffers : (rest config).program.code.memBound ≤ 2 := Implementation.second_buffers _ _ _ _ _
theorem responses_buffers : (responses config).program.code.memBound ≤ 2 :=
  max_le (rest_buffers config) (Implementation.first_buffers _ _ _ _ _)
theorem challenges_buffers : (challenges config).program.code.memBound ≤ 2 :=
  max_le (rest_buffers config) (Implementation.second_buffers _ _ _ _ _)

section Equality
variable [DecidableEq F] [DecidableEq G]
omit [DecidableEq F] in
theorem sameCommitment_buffers : (sameCommitment config).program.code.memBound ≤ 5 :=
  max_le ((commitments_buffers config).trans (by omega)) (EncodedEquality.implementation_names _ _ _ _).buffers
omit [DecidableEq G] in
theorem sameChallenge_buffers : (sameChallenge config).program.code.memBound ≤ 5 :=
  max_le ((challenges_buffers config).trans (by omega)) (EncodedEquality.implementation_names _ _ _ _).buffers
end Equality

include config in
theorem smallNameFits {A B : Type} {i : Layout w A} {o : Layout w B} {f : A → B}
    (body : Implementation .unit i o f) (bound : body.program.code.memBound ≤ 5) : body.program.savedBuffer < 2 ^ w := by
  have := config.sampler.wordFits
  change max 2 body.program.code.memBound < _
  omega

section Arithmetic
variable [Sub F] [Div F] (arith : Arithmetic config)

def numerator : Implementation .unit (quad config) config.handler.core.scalar (fun value => value.2.1.1 - value.2.1.2) :=
  (responses config).then arith.sub
def denominator : Implementation .unit (quad config) config.handler.core.scalar (fun value => value.2.2.1 - value.2.2.2) :=
  (challenges config).then arith.sub
theorem numerator_buffers : (numerator config arith).program.code.memBound ≤ max 2 arith.slots :=
  max_le_max (responses_buffers config) arith.subNames.buffers
theorem denominator_buffers : (denominator config arith).program.code.memBound ≤ max 2 arith.slots :=
  max_le_max (challenges_buffers config) arith.subNames.buffers

theorem nameFits {A B : Type} {i : Layout w A} {o : Layout w B} {f : A → B}
    (body : Implementation .unit i o f) (bound : body.program.code.memBound ≤ max 2 arith.slots) : body.program.savedBuffer < 2 ^ w := by
  have := config.sampler.wordFits
  have := arith.reserve
  change max 2 body.program.code.memBound < _
  omega

def quotientArgs : Implementation .unit (quad config) (scalars config)
    (fun value => (value.2.1.1 - value.2.1.2, value.2.2.1 - value.2.2.2)) :=
  (numerator config arith).pair (denominator config arith) (by decide) config.sampler.wordFits
    (nameFits config arith _ (numerator_buffers config arith)) (nameFits config arith _ (denominator_buffers config arith))
    (duplicateFits config) (middleFits config) _
def quotient : Implementation .unit (quad config) config.handler.core.scalar
    (fun value => (value.2.1.1 - value.2.1.2) / (value.2.2.1 - value.2.2.2)) :=
  (quotientArgs config arith).then arith.divide
theorem quotientArgs_buffers : (quotientArgs config arith).program.code.memBound ≤ max 2 arith.slots + 1 :=
  (Implementation.pair_buffers _ _ _ _ _ _ _ _ (numerator_buffers config arith) (denominator_buffers config arith)).trans
    (by omega)
theorem quotient_buffers : (quotient config arith).program.code.memBound ≤ max 2 arith.slots + 1 :=
  max_le (quotientArgs_buffers config arith) (arith.divideNames.buffers.trans (by omega))
end Arithmetic

/-- The quotient is tagged by executed tag-construction code. -/
def inject : Implementation .unit config.handler.core.scalar (choiceLayout config) Sum.inr where
  preserves _ valid := valid
  program := (inrRealizer .unit (by decide) config.handler.sampler.tape.unit.representation
    config.handler.sampler.tape.scalar.representation config.sampler.wordFits (choiceFits config)).viewOutput
      (choiceLayout config).representation
      (fun value : config.handler.sampler.tape.scalar.Value => (⟨.inr value.val, value.property⟩ : (choiceLayout config).Value))
      (fun _ => rfl)
def fallbackConstant {A : Type} (input : Layout w A) : Implementation .unit input (choiceLayout config) (fun _ => .inl ()) :=
  Implementation.constant input (choiceLayout config) ⟨.inl (), trivial⟩ config.sampler.wordFits

section Core
variable [DecidableEq F] [DecidableEq G] [Sub F] [Div F] (arith : Arithmetic config)

def sameCommitmentTest (value : Quad F G) : Bool := decide (value.1.1 = value.1.2)
def sameChallengeTest (value : Quad F G) : Bool := decide (value.2.2.1 = value.2.2.2)

/-- `(z₁ - z₂) / (c₁ - c₂)` when commitments agree and challenges differ;
otherwise the uniform-fallback tag. -/
def coreValue (value : Quad F G) : Unit ⊕ F :=
  if value.1.1 = value.1.2 ∧ value.2.2.1 ≠ value.2.2.2 then
    .inr ((value.2.1.1 - value.2.1.2) / (value.2.2.1 - value.2.2.2))
  else .inl ()

def agreeing := GuardedBranch.yesInput (quad config) sameCommitmentTest

def extracted : Implementation .unit (quad config) (choiceLayout config)
    (fun value => Sum.inr ((value.2.1.1 - value.2.1.2) / (value.2.2.1 - value.2.2.2))) :=
  (quotient config arith).then (inject config)
omit [DecidableEq F] [DecidableEq G] in
theorem extracted_buffers : (extracted config arith).program.code.memBound ≤ max 2 arith.slots + 1 :=
  max_le (quotient_buffers config arith) ((inr_names config.handler.sampler.tape.unit.representation
    config.handler.sampler.tape.scalar.representation config.sampler.wordFits (choiceFits config)).buffers.trans (by omega))

def inner : Implementation .unit (agreeing config) (choiceLayout config)
    (fun value => if sameChallengeTest value = true then .inl ()
      else Sum.inr ((value.2.1.1 - value.2.1.2) / (value.2.2.1 - value.2.2.2))) :=
  GuardedBranch.implementation (hw := config.sampler.wordFits)
    ((sameChallenge config).restrictInput (fun value => sameCommitmentTest value = true)) (by decide)
    (smallNameFits config _ (sameChallenge_buffers config)) (duplicateFits config) (tagFits config)
    (fallbackConstant config _)
    (((extracted config arith).restrictInput (fun value => sameCommitmentTest value = true)).restrictInput
      (fun value => sameChallengeTest value = false))

def guarded : Implementation .unit (quad config) (choiceLayout config)
    (fun value => if sameCommitmentTest value = true then
      (if sameChallengeTest value = true then .inl ()
        else Sum.inr ((value.2.1.1 - value.2.1.2) / (value.2.2.1 - value.2.2.2))) else .inl ()) :=
  GuardedBranch.implementation (hw := config.sampler.wordFits) (sameCommitment config) (by decide)
    (smallNameFits config _ (sameCommitment_buffers config)) (duplicateFits config) (tagFits config)
    (inner config arith) (fallbackConstant config _)

theorem guarded_value : (fun value : Quad F G => if sameCommitmentTest value = true then
      (if sameChallengeTest value = true then (Sum.inl () : Unit ⊕ F)
        else Sum.inr ((value.2.1.1 - value.2.1.2) / (value.2.2.1 - value.2.2.2))) else .inl ()) = coreValue := by
  funext value
  unfold sameCommitmentTest sameChallengeTest coreValue
  by_cases commitment : value.1.1 = value.1.2 <;> by_cases challenge : value.2.2.1 = value.2.2.2 <;>
    simp [commitment, challenge]

def core : Implementation .unit (quad config) (choiceLayout config) coreValue :=
  (guarded config arith).castFunction (guarded_value (F := F) (G := G))

end Core
end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Extract
