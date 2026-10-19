import Signatures.Runtime.Caliper.CacheTargetFrameBounds

/-! Stored register and buffer names of the final-request constructor. -/
namespace Signatures.Runtime.CaliperBackend.CacheTargetFrame
open Caliper BoundedSource
variable {w : Nat} {K F R : Type} (layout : CacheAccumulate.Layouts w K F R) (names : Nat)
theorem result_names : NamesAccounted (result layout).program.code names :=
  (Implementation.first_names _ _ _ _ names).seq (Implementation.first_names _ _ _ _ names)
theorem table_names : NamesAccounted (table layout).program.code names :=
  (Implementation.first_names _ _ _ _ names).seq (Implementation.second_names _ _ _ _ names)
theorem target_names : NamesAccounted (target layout).program.code names :=
  (Implementation.second_names _ _ _ _ names).seq (Implementation.first_names _ _ _ _ names)
theorem coefficient_names : NamesAccounted (coefficient layout).program.code names :=
  (Implementation.second_names _ _ _ _ names).seq (Implementation.second_names _ _ _ _ names)
theorem unit_names : NamesAccounted (unit layout).program.code names := Implementation.constant_names _ _ _ _ names
theorem tableTail_names : NamesAccounted (tableTail layout).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (table_names layout names) (unit_names layout names)
theorem saved_names : NamesAccounted (saved layout).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (coefficient_names layout names) (result_names layout names)
variable (fallback : layout.cache.value.Value)
theorem defaultValue_names : NamesAccounted (defaultValue layout fallback).program.code names := Implementation.constant_names _ _ _ _ names
theorem valueTail_names : NamesAccounted (valueTail layout fallback).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (defaultValue_names layout names fallback) (tableTail_names layout names)
theorem request_names : NamesAccounted (request layout fallback).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (target_names layout names) (valueTail_names layout names fallback)
theorem pack_names : NamesAccounted (pack layout fallback).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (request_names layout names fallback) (saved_names layout names)
variable [DecidableEq K]
theorem implementation_names : NamesAccounted (implementation layout fallback).program.code names := pack_names layout names fallback
end Signatures.Runtime.CaliperBackend.CacheTargetFrame
