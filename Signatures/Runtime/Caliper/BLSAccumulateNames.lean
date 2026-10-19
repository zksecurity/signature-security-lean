import Signatures.Runtime.Caliper.BLSAccumulateBounds

/-! Name accounting for accumulator updates, derived from the selected scalar
routine names and the executed structural code. -/

namespace Signatures.Runtime.CaliperBackend.BLSAccumulate
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : Layouts w F) (names : Nat)

theorem coefficient_names : NamesAccounted (coefficient layout).program.code names := Implementation.first_names _ _ _ _ names
theorem pairSelect_names (second : Bool) : NamesAccounted (pairSelect layout second).program.code names := by
  cases second
  · exact Implementation.first_names _ _ _ _ names
  · exact Implementation.second_names _ _ _ _ names
theorem coordinate_names (accumulator second : Bool) : NamesAccounted (coordinate layout accumulator second).program.code names :=
  ((Implementation.second_names _ _ _ _ names).seq (pairSelect_names layout names accumulator)).seq
    (BLSResponse.pointSelect_names layout.arithmetic names second)
theorem coordinatePair_names (second : Bool) : NamesAccounted (coordinatePair layout second).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (coordinate_names layout names false second) (coordinate_names layout names true second)
theorem coordinateInput_names (second : Bool) : NamesAccounted (coordinateInput layout second).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (coefficient_names layout names) (coordinatePair_names layout names second)

variable [Mul F] [Add F]
    (mul : Implementation .unit layout.pair layout.scalar (fun value => value.1 * value.2))
    (add : Implementation .unit layout.pair layout.scalar (fun value => value.1 + value.2))
    (mulNames : NamesAccounted mul.program.code names) (addNames : NamesAccounted add.program.code names)
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)

include mulNames in
omit [Add F] in
theorem term_names : NamesAccounted (term layout mul).program.code names :=
  (BLSResponse.goodArguments_names layout.arithmetic names false).seq mulNames
include mulNames in
omit [Add F] in
theorem addArgs_names : NamesAccounted (addArgs layout mul mulBuffers reserve).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (BLSResponse.goodPoint_names layout.arithmetic names true) (term_names layout names mul mulNames)
include mulNames addNames in
theorem good_names : NamesAccounted (good layout mul add mulBuffers reserve).program.code names :=
  (addArgs_names layout names mul mulNames mulBuffers reserve).seq addNames
include mulNames addNames in
theorem component_names (second : Bool) : NamesAccounted (component layout mul add mulBuffers reserve second).program.code names :=
  (coordinateInput_names layout names second).seq (good_names layout names mul add mulNames addNames mulBuffers reserve)
variable (addBuffers : add.program.code.memBound ≤ slots)
include mulNames addNames in
theorem bad_names : NamesAccounted (bad layout mul add mulBuffers reserve addBuffers).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _
    (component_names layout names mul add mulNames addNames mulBuffers reserve false)
    (component_names layout names mul add mulNames addNames mulBuffers reserve true)

end Signatures.Runtime.CaliperBackend.BLSAccumulate
