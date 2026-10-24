import Proofs.Runtime.Caliper.BLSExtractArithmeticBounds

/-! Name accounting for the constructed BLS extraction arithmetic. -/
namespace Signatures.Runtime.CaliperBackend.BLSExtractArithmetic
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : BLSAccumulate.Layouts w F) (names : Nat)

theorem numerator_names : NamesAccounted (numerator layout).program.code names := Implementation.first_names _ _ _ _ names
theorem differenceArgs_names : NamesAccounted (differenceArgs layout).program.code names := Implementation.second_names _ _ _ _ names

section Subtract
variable [Sub F]
    (sub : Implementation .unit layout.pair layout.scalar (fun value => value.1 - value.2))
    (subNames : NamesAccounted sub.program.code names)
    {slots : Nat} (subBuffers : sub.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
include subNames in
theorem denominator_names : NamesAccounted (denominator layout sub).program.code names :=
  (differenceArgs_names layout names).seq subNames
include subNames in
theorem goodArguments_names : NamesAccounted (goodArguments layout sub subBuffers reserve).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (numerator_names layout names) (denominator_names layout names sub subNames)
include subNames in
theorem difference_names (second : Bool) : NamesAccounted (difference layout sub second).program.code names :=
  (BLSAccumulate.coordinatePair_names layout names second).seq subNames

section Good
variable [Div F]
    (divide : Implementation .unit layout.pair layout.scalar (fun value => value.1 / value.2))
    (divNames : NamesAccounted divide.program.code names)
include subNames divNames in
theorem good_names : NamesAccounted (good layout sub subBuffers reserve divide).program.code names :=
  (goodArguments_names layout names sub subNames subBuffers reserve).seq divNames
end Good

section Bad
variable [Neg F] (negate : Implementation .unit layout.scalar layout.scalar Neg.neg)
    (negNames : NamesAccounted negate.program.code names) (negBuffers : negate.program.code.memBound ≤ slots)
include subNames negNames in
theorem negated_names : NamesAccounted (negated layout sub negate).program.code names :=
  (difference_names layout names sub subNames true).seq negNames
include subNames negNames in
theorem badArguments_names : NamesAccounted (badArguments layout sub subBuffers reserve negate negBuffers).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _
    (negated_names layout names sub subNames negate negNames) (difference_names layout names sub subNames false)
variable [Div F]
    (divide : Implementation .unit layout.pair layout.scalar (fun value => value.1 / value.2))
    (divNames : NamesAccounted divide.program.code names)
include subNames negNames divNames in
theorem bad_names : NamesAccounted (bad layout sub subBuffers reserve negate negBuffers divide).program.code names :=
  (badArguments_names layout names sub subNames subBuffers reserve negate negNames negBuffers).seq divNames
end Bad
end Subtract
end Signatures.Runtime.CaliperBackend.BLSExtractArithmetic
