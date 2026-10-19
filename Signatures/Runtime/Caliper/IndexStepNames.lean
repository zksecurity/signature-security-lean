import Signatures.Runtime.Caliper.IndexStepBounds
import Signatures.Runtime.Caliper.StructuralNames

/-! Register and buffer names of the constructed index scan are accounted for by
its stored code. There is no supplied implementation or name-budget contract. -/

namespace Signatures.Runtime.CaliperBackend.ListIndex
open Caliper BoundedSource
variable {w : Nat} {V : Type} (layout : Layouts w V) (slots : Nat)

theorem current_names : NamesAccounted (current layout).program.code slots :=
  (Implementation.second_names _ _ _ _ slots).seq (Implementation.first_names _ _ _ _ slots)
theorem entry_names : NamesAccounted (entry layout).program.code slots := Implementation.first_names _ _ _ _ slots
theorem remaining_names : NamesAccounted (remaining layout).program.code slots :=
  (current_names layout slots).seq (Implementation.first_names _ _ _ _ slots)
theorem payload_names : NamesAccounted (payload layout).program.code slots :=
  (current_names layout slots).seq (Implementation.second_names _ _ _ _ slots)
theorem found_names : NamesAccounted (found layout).program.code slots :=
  (payload_names layout slots).seq (Implementation.first_names _ _ _ _ slots)
theorem zero_names : NamesAccounted (zero layout).program.code slots := Implementation.constant_names _ _ _ _ slots
theorem one_names : NamesAccounted (one layout).program.code slots := Implementation.constant_names _ _ _ _ slots
theorem yes_names : NamesAccounted (yes layout).program.code slots := Implementation.constant_names _ _ _ _ slots
theorem zeroArgs_names : NamesAccounted (zeroArgs layout).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (remaining_names layout slots) (zero_names layout slots)
theorem zeroTest_names : NamesAccounted (zeroTest layout).program.code slots := by
  apply (zeroArgs_names layout slots).seq
  constructor
  · change 3 ≤ slots + 27; omega
  · change 1 ≤ slots + 27; omega
theorem subtractionArgs_names : NamesAccounted (subtractionArgs layout).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (remaining_names layout slots) (one_names layout slots)
theorem decrement_names : NamesAccounted (decrement layout).program.code slots := by
  apply (subtractionArgs_names layout slots).seq
  constructor
  · change 4 ≤ slots + 38; omega
  · change 1 ≤ slots + 38; omega
theorem selected_names : NamesAccounted (selected layout).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (yes_names layout slots) (entry_names layout slots)
theorem hit_names : NamesAccounted (hit layout).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (zero_names layout slots) (selected_names layout slots)
theorem miss_names : NamesAccounted (miss layout).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (decrement_names layout slots) (payload_names layout slots)
theorem search_names : NamesAccounted (search layout).program.code slots :=
  Implementation.checkedBranch_names _ _ _ layout.bodyDuplicate layout.bodyTag
    (zeroTest_names layout slots) (hit_names layout slots) (miss_names layout slots) (search layout)
    (Option.eq_some_of_isSome (search_accepted layout))
theorem body_names : NamesAccounted (body layout).program.code slots :=
  Implementation.checkedBranch_names _ _ _ layout.bodyDuplicate layout.bodyTag
    (found_names layout slots) (current_names layout slots) (search_names layout slots)
    ((bodyCompiled layout).get (body_accepted layout)) (Option.eq_some_of_isSome (body_accepted layout))

end Signatures.Runtime.CaliperBackend.ListIndex
