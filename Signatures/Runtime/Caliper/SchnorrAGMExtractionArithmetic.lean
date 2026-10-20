import Signatures.Runtime.Caliper.SchnorrAGMEntryRead
import Signatures.Runtime.Caliper.GuardedBranchBounds
import Signatures.Runtime.Caliper.EncodedConstant

/-! Executed terminal scalar arithmetic. The cached representation flag selects
between zero and the quotient. Only field addition, subtraction and division
are supplied; projections, input preservation, pairing and branching are code. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.ExtractionArithmetic
open Caliper BoundedSource
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

def input : Layout w (EncodedEntry F × F) := layout.entry.prod layout.scalar
  (layout.fits_of_le (by rw [Layouts.entry_words]; dsimp only [Layouts.width, storageWidth]; omega))
theorem input_words : (input layout).representation.encoding.words = 4 * layout.scalar.representation.encoding.words + 1 := by
  change layout.entry.representation.encoding.words + layout.scalar.representation.encoding.words = _
  rw [Layouts.entry_words]; omega
theorem sizes : (input layout).representation.encoding.words ≤ 2 * layout.width ∧
    layout.scalar.representation.encoding.words ≤ layout.width := by
  rw [input_words]; dsimp only [Layouts.width, storageWidth]; omega
theorem duplicateFits : (input layout).representation.encoding.words + (input layout).representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := sizes layout; omega)
theorem middleFits : layout.scalar.representation.encoding.words + (input layout).representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := sizes layout; omega)
theorem tagFits : 1 + (input layout).representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := sizes layout; have := input_words layout; omega)

def entry : Implementation .unit (input layout) layout.entry Prod.fst :=
  Implementation.first (by decide) layout.entry layout.scalar layout.wordFits _
def optional : Implementation .unit (input layout) layout.optionalAffine (fun value => value.1.2) :=
  (entry layout).then (Implementation.second (by decide) layout.scalar layout.optionalAffine layout.wordFits _)
def affine : Implementation .unit (input layout) layout.affine (fun value => value.1.2.2) :=
  (optional layout).then (Implementation.second (by decide) layout.boolean layout.affine layout.wordFits _)
def challenge : Implementation .unit (input layout) layout.scalar (fun value => value.1.1) :=
  (entry layout).then (Implementation.first (by decide) layout.scalar layout.optionalAffine layout.wordFits _)
def constant : Implementation .unit (input layout) layout.scalar (fun value => value.1.2.2.1) :=
  (affine layout).then (Implementation.first (by decide) layout.scalar layout.scalar layout.wordFits _)
def secret : Implementation .unit (input layout) layout.scalar (fun value => value.1.2.2.2) :=
  (affine layout).then (Implementation.second (by decide) layout.scalar layout.scalar layout.wordFits _)
def response : Implementation .unit (input layout) layout.scalar Prod.snd :=
  Implementation.second (by decide) layout.entry layout.scalar layout.wordFits _
def present : Implementation .unit (input layout) layout.boolean (fun value => value.1.2.1) :=
  (optional layout).then (Implementation.first (by decide) layout.boolean layout.affine layout.wordFits _)

theorem entry_buffers : (entry layout).program.code.memBound ≤ 2 :=
  Implementation.first_buffers _ _ _ _ _

theorem optional_buffers : (optional layout).program.code.memBound ≤ 2 :=
  max_le (entry_buffers layout) (Implementation.second_buffers _ _ _ _ _)

theorem affine_buffers : (affine layout).program.code.memBound ≤ 2 :=
  max_le (optional_buffers layout) (Implementation.second_buffers _ _ _ _ _)

theorem challenge_buffers : (challenge layout).program.code.memBound ≤ 2 :=
  max_le (entry_buffers layout) (Implementation.first_buffers _ _ _ _ _)

theorem constant_buffers : (constant layout).program.code.memBound ≤ 2 :=
  max_le (affine_buffers layout) (Implementation.first_buffers _ _ _ _ _)

theorem secret_buffers : (secret layout).program.code.memBound ≤ 2 :=
  max_le (affine_buffers layout) (Implementation.second_buffers _ _ _ _ _)

theorem response_buffers : (response layout).program.code.memBound ≤ 2 :=
  Implementation.second_buffers _ _ _ _ _

theorem present_buffers : (present layout).program.code.memBound ≤ 2 :=
  max_le (optional_buffers layout) (Implementation.first_buffers _ _ _ _ _)

include layout in
theorem smallNameFits {A B : Type} {i : Layout w A} {o : Layout w B} {f : A → B}
    (body : Implementation .unit i o f) (bound : body.program.code.memBound ≤ 2) : body.program.savedBuffer < 2 ^ w := by
  have := layout.wordFits
  change max 2 body.program.code.memBound < _
  omega

def subtractionArgs : Implementation .unit (input layout) layout.affine (fun value => (value.2, value.1.2.2.1)) :=
  (response layout).pair (constant layout) (by decide) layout.wordFits
    (smallNameFits layout _ (response_buffers layout)) (smallNameFits layout _ (constant_buffers layout))
    (duplicateFits layout) (middleFits layout) _
def additionArgs : Implementation .unit (input layout) layout.affine (fun value => (value.1.2.2.2, value.1.1)) :=
  (secret layout).pair (challenge layout) (by decide) layout.wordFits
    (smallNameFits layout _ (secret_buffers layout)) (smallNameFits layout _ (challenge_buffers layout))
    (duplicateFits layout) (middleFits layout) _
theorem subtractionArgs_buffers : (subtractionArgs layout).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (response_buffers layout) (constant_buffers layout)
theorem additionArgs_buffers : (additionArgs layout).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (secret_buffers layout) (challenge_buffers layout)

variable [Add F] [Sub F] [Div F]
    (add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2))
    (sub : Implementation .unit layout.affine layout.scalar (fun value => value.1 - value.2))
    (divide : Implementation .unit layout.affine layout.scalar (fun value => value.1 / value.2))
    {slots : Nat} (addBuffers : add.program.code.memBound ≤ slots) (subBuffers : sub.program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w)

def numerator : Implementation .unit (input layout) layout.scalar (fun value => value.2 - value.1.2.2.1) :=
  (subtractionArgs layout).then sub
def denominator : Implementation .unit (input layout) layout.scalar (fun value => value.1.2.2.2 + value.1.1) :=
  (additionArgs layout).then add
include subBuffers in
omit [Add F] [Div F] in
theorem numerator_buffers : (numerator layout sub).program.code.memBound ≤ max 3 slots :=
  max_le_max (subtractionArgs_buffers layout) subBuffers
include addBuffers in
omit [Sub F] [Div F] in
theorem denominator_buffers : (denominator layout add).program.code.memBound ≤ max 3 slots :=
  max_le_max (additionArgs_buffers layout) addBuffers

include layout reserve in
omit [Add F] [Sub F] [Div F] in
theorem nameFits {A B : Type} {i : Layout w A} {o : Layout w B} {f : A → B}
    (body : Implementation .unit i o f) (bound : body.program.code.memBound ≤ max 3 slots) : body.program.savedBuffer < 2 ^ w := by
  have := layout.wordFits
  change max 2 body.program.code.memBound < _
  omega

def quotientArgs : Implementation .unit (input layout) layout.affine
    (fun value => (value.2 - value.1.2.2.1, value.1.2.2.2 + value.1.1)) :=
  (numerator layout sub).pair (denominator layout add) (by decide) layout.wordFits
    (nameFits layout reserve _ (numerator_buffers layout sub subBuffers))
    (nameFits layout reserve _ (denominator_buffers layout add addBuffers))
    (duplicateFits layout) (middleFits layout) _
omit [Div F] in
theorem quotientArgs_buffers : (quotientArgs layout add sub addBuffers subBuffers reserve).program.code.memBound ≤ max 3 slots + 1 := by
  exact (Implementation.pair_buffers _ _ _ _ _ _ _ _
    (numerator_buffers layout sub subBuffers) (denominator_buffers layout add addBuffers)).trans (by omega)
def quotient : Implementation .unit (input layout) layout.scalar
    (fun value => (value.2 - value.1.2.2.1) / (value.1.2.2.2 + value.1.1)) :=
  (quotientArgs layout add sub addBuffers subBuffers reserve).then divide

theorem quotient_buffers (divBuffers : divide.program.code.memBound ≤ slots) :
    (quotient layout add sub divide addBuffers subBuffers reserve).program.code.memBound ≤ max 3 slots + 1 :=
  max_le (quotientArgs_buffers layout add sub addBuffers subBuffers reserve) (divBuffers.trans (by omega))

variable [Zero F] (zeroValid : layout.scalar.valid 0)
def value (args : EncodedEntry F × F) : F :=
  if args.1.2.1 then (args.2 - args.1.2.2.1) / (args.1.2.2.2 + args.1.1) else 0

def implementation : Implementation .unit (input layout) layout.scalar value :=
  GuardedBranch.implementation (hw := layout.wordFits) (present layout) (by decide)
    (smallNameFits layout _ (present_buffers layout)) (duplicateFits layout) (tagFits layout)
    ((quotient layout add sub divide addBuffers subBuffers reserve).restrictInput (fun value => value.1.2.1 = true))
    (Implementation.constant _ layout.scalar ⟨0, zeroValid⟩ layout.wordFits)

theorem buffers (divBuffers : divide.program.code.memBound ≤ slots) :
    (implementation layout add sub divide addBuffers subBuffers reserve zeroValid).program.code.memBound ≤ max 3 slots + 1 := by
  have bound := GuardedBranch.implementation_buffers (hw := layout.wordFits) (present layout)
    (smallNameFits layout _ (present_buffers layout)) (duplicateFits layout) (tagFits layout)
    ((quotient layout add sub divide addBuffers subBuffers reserve).restrictInput (fun value => value.1.2.1 = true))
    (Implementation.constant _ layout.scalar ⟨0, zeroValid⟩ layout.wordFits)
    (present_buffers layout) (quotient_buffers layout add sub divide addBuffers subBuffers reserve divBuffers)
    (Implementation.constant_buffers _ _ _ _)
  exact bound.trans (by omega)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.ExtractionArithmetic
