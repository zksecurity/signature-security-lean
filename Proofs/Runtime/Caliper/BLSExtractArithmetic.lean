import Proofs.Runtime.Caliper.BLSAccumulateSource

/-! The terminal BLS scalar arithmetic, constructed from named subtraction,
negation and division routines. Good input is (numerator, target, signatures);
bad input is (beta, target pair, signatures pair). The bad branch ignores beta
but its stored bytes and all projections still count. Division is total. -/
namespace Signatures.Runtime.CaliperBackend.BLSExtractArithmetic
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : BLSAccumulate.Layouts w F)

def numerator : Implementation .unit layout.good layout.scalar Prod.fst :=
  Implementation.first (by decide) layout.scalar layout.pair layout.wordFits layout.good.representation.fits
def differenceArgs : Implementation .unit layout.good layout.pair Prod.snd :=
  Implementation.second (by decide) layout.scalar layout.pair layout.wordFits layout.good.representation.fits
theorem numerator_buffers : (numerator layout).program.code.memBound ≤ 2 := Implementation.first_buffers _ _ _ _ _
theorem differenceArgs_buffers : (differenceArgs layout).program.code.memBound ≤ 2 := Implementation.second_buffers _ _ _ _ _

section Good
variable [Sub F] (sub : Implementation .unit layout.pair layout.scalar (fun value => value.1 - value.2))
    {slots : Nat} (subBuffers : sub.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
def denominator : Implementation .unit layout.good layout.scalar (fun value => value.2.1 - value.2.2) :=
  (differenceArgs layout).then sub
include subBuffers in
theorem denominator_buffers : (denominator layout sub).program.code.memBound ≤ max 2 slots :=
  max_le ((differenceArgs_buffers layout).trans (Nat.le_max_left _ _)) (subBuffers.trans (Nat.le_max_right _ _))
def goodArguments : Implementation .unit layout.good layout.pair (fun value => (value.1, value.2.1 - value.2.2)) :=
  (numerator layout).pair (denominator layout sub) (by decide) layout.wordFits
    (layout.nameFits _ (numerator_buffers layout) (by have := layout.wordFits; omega))
    (layout.nameFits _ (denominator_buffers layout sub subBuffers) (by have := layout.wordFits; omega))
    (layout.fits_of_le (by rw [BLSAccumulate.Layouts.good_words]; omega))
    (layout.fits_of_le (by rw [BLSAccumulate.Layouts.good_words]; omega)) layout.pair.representation.fits
theorem goodArguments_buffers : (goodArguments layout sub subBuffers reserve).program.code.memBound ≤ max 2 slots + 1 :=
  (Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := max 2 slots) _ _ _ _ _ _ _ _
    (numerator_buffers layout) (denominator_buffers layout sub subBuffers)).trans (by omega)
variable [Div F] (divide : Implementation .unit layout.pair layout.scalar (fun value => value.1 / value.2))
def good : Implementation .unit layout.good layout.scalar (fun value => value.1 / (value.2.1 - value.2.2)) :=
  (goodArguments layout sub subBuffers reserve).then divide
theorem good_buffers (divBuffers : divide.program.code.memBound ≤ slots) :
    (good layout sub subBuffers reserve divide).program.code.memBound ≤ max 2 slots + 1 :=
  max_le (goodArguments_buffers layout sub subBuffers reserve) (divBuffers.trans (by omega))
end Good

section Bad
variable [Sub F] (sub : Implementation .unit layout.pair layout.scalar (fun value => value.1 - value.2))
    {slots : Nat} (subBuffers : sub.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
def difference (second : Bool) : Implementation .unit layout.bad layout.scalar
    (fun value => if second then value.2.1.2 - value.2.2.2 else value.2.1.1 - value.2.2.1) :=
  ((BLSAccumulate.coordinatePair layout second).then sub).castFunction (by funext value; cases second <;> rfl)
include subBuffers in
theorem difference_buffers (second : Bool) : (difference layout sub second).program.code.memBound ≤ max 3 slots :=
  max_le ((BLSAccumulate.coordinatePair_buffers layout second).trans (Nat.le_max_left _ _)) (subBuffers.trans (Nat.le_max_right _ _))
variable [Neg F] (negate : Implementation .unit layout.scalar layout.scalar Neg.neg)
    (negBuffers : negate.program.code.memBound ≤ slots)
def negated : Implementation .unit layout.bad layout.scalar (fun value => -(value.2.1.2 - value.2.2.2)) :=
  (difference layout sub true).then negate
include subBuffers negBuffers in
theorem negated_buffers : (negated layout sub negate).program.code.memBound ≤ max 3 slots :=
  max_le (difference_buffers layout sub subBuffers true) (negBuffers.trans (Nat.le_max_right _ _))
def badArguments : Implementation .unit layout.bad layout.pair
    (fun value => (-(value.2.1.2 - value.2.2.2), value.2.1.1 - value.2.2.1)) :=
  (negated layout sub negate).pair (difference layout sub false) (by decide) layout.wordFits
    (layout.nameFits _ (negated_buffers layout sub subBuffers negate negBuffers) (by have := layout.wordFits; omega))
    (layout.nameFits _ (difference_buffers layout sub subBuffers false) (by have := layout.wordFits; omega))
    (layout.fits_of_le (by rw [BLSAccumulate.Layouts.bad_words]; omega))
    (layout.fits_of_le (by rw [BLSAccumulate.Layouts.bad_words]; omega)) layout.pair.representation.fits
theorem badArguments_buffers : (badArguments layout sub subBuffers reserve negate negBuffers).program.code.memBound ≤ max 3 slots + 1 :=
  (Implementation.pair_buffers (firstBuffers := max 3 slots) (secondBuffers := max 3 slots) _ _ _ _ _ _ _ _
    (negated_buffers layout sub subBuffers negate negBuffers) (difference_buffers layout sub subBuffers false)).trans (by omega)
variable [Div F] (divide : Implementation .unit layout.pair layout.scalar (fun value => value.1 / value.2))
def bad : Implementation .unit layout.bad layout.scalar
    (fun value => -(value.2.1.2 - value.2.2.2) / (value.2.1.1 - value.2.2.1)) :=
  (badArguments layout sub subBuffers reserve negate negBuffers).then divide
theorem bad_buffers (divBuffers : divide.program.code.memBound ≤ slots) :
    (bad layout sub subBuffers reserve negate negBuffers divide).program.code.memBound ≤ max 3 slots + 1 :=
  max_le (badArguments_buffers layout sub subBuffers reserve negate negBuffers) (divBuffers.trans (by omega))
end Bad
end Signatures.Runtime.CaliperBackend.BLSExtractArithmetic
