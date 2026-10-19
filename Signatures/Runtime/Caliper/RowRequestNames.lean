import Signatures.Runtime.Caliper.RowRequestBounds

/-! Names used by the constructed row request, with no supplied controller. -/
namespace Signatures.Runtime.CaliperBackend.RowRequest
open Caliper BoundedSource
variable {w : Nat} {K G F R : Type} (layout : Layouts w K G F R)
    (default : layout.accumulation.cache.value.Value) (names : Nat)
theorem row_names : NamesAccounted (row layout).program.code names :=
  Implementation.first_names layout.row layout.state layout.accumulation.cache.wordFits layout.raw.representation.fits names
theorem state_names : NamesAccounted (state layout).program.code names :=
  Implementation.second_names layout.row layout.state layout.accumulation.cache.wordFits layout.raw.representation.fits names
theorem token_names : NamesAccounted (token layout).program.code names :=
  (row_names layout names).seq (Implementation.first_names _ _ _ _ names)
theorem message_names : NamesAccounted (message layout).program.code names :=
  (token_names layout names).seq (Implementation.first_names _ _ _ _ names)
theorem coefficient_names : NamesAccounted (coefficient layout).program.code names :=
  (row_names layout names).seq (Implementation.second_names _ _ _ _ names)
theorem accumulator_names : NamesAccounted (accumulator layout).program.code names :=
  (state_names layout names).seq (Implementation.first_names _ _ _ _ names)
theorem table_names : NamesAccounted (table layout).program.code names :=
  (state_names layout names).seq (Implementation.second_names _ _ _ _ names)
theorem tableTail_names : NamesAccounted (tableTail layout).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (table_names layout names) (DataImplementation.unit_names _ _ names)
theorem valueTail_names : NamesAccounted (valueTail layout default).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (Implementation.constant_names _ _ _ _ names) (tableTail_names layout names)
theorem saved_names : NamesAccounted (saved layout).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (coefficient_names layout names) (accumulator_names layout names)
variable [DecidableEq K]
theorem cacheArguments_names : NamesAccounted (cacheArguments layout default).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ layout.accumulation.cache.lookup.input.representation.fits
    (message_names layout names) (valueTail_names layout default names)
theorem prepare_names : NamesAccounted (prepare layout default).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (cacheArguments_names layout default names) (saved_names layout names)
end Signatures.Runtime.CaliperBackend.RowRequest
