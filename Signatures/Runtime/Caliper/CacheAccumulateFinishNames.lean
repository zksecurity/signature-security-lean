import Signatures.Runtime.Caliper.CacheAccumulateFinishBounds

/-! All generated continuation names are accounted for from the local update. -/
namespace Signatures.Runtime.CaliperBackend.CacheAccumulate
open Caliper BoundedSource
variable {w : Nat} {K F R : Type} (layout : Layouts w K F R) (names : Nat)
theorem answer_names : NamesAccounted (answer layout).program.code names :=
  (Implementation.first_names _ _ _ _ names).seq (Implementation.first_names _ _ _ _ names)
theorem table_names : NamesAccounted (table layout).program.code names :=
  (Implementation.first_names _ _ _ _ names).seq (Implementation.second_names _ _ _ _ names)
theorem coefficient_names : NamesAccounted (coefficient layout).program.code names :=
  (Implementation.second_names _ _ _ _ names).seq (Implementation.first_names _ _ _ _ names)
theorem accumulator_names : NamesAccounted (accumulator layout).program.code names :=
  (Implementation.second_names _ _ _ _ names).seq (Implementation.second_names _ _ _ _ names)
theorem operands_names : NamesAccounted (operands layout).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (answer_names layout names) (accumulator_names layout names)
theorem arguments_names : NamesAccounted (arguments layout).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (coefficient_names layout names) (operands_names layout names)
variable {combine : F × (R × R) → R} (update : Implementation .unit layout.combine layout.cache.value combine)
    (updateNames : NamesAccounted update.program.code names)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
include updateNames in
theorem finish_names : NamesAccounted (finish layout update updateBuffers reserve).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ ((arguments_names layout names).seq updateNames) (table_names layout names)
end Signatures.Runtime.CaliperBackend.CacheAccumulate
