import Proofs.Runtime.Caliper.BLSFinalFrameBounds

/-! Final BLS frame names are derived from the single scalar addition routine. -/
namespace Signatures.Runtime.CaliperBackend.BLSFinalFrame
open Caliper BoundedSource
variable {w : Nat} {M F : Type} (layout : BLSPrivateAccumulate.Layouts w M F) (names : Nat)
theorem target_names : NamesAccounted (target layout).program.code names :=
  (Implementation.second_names _ _ _ _ names).seq (Implementation.first_names _ _ _ _ names)
theorem operands_names : NamesAccounted (operands layout).program.code names :=
  (Implementation.second_names _ _ _ _ names).seq (Implementation.second_names _ _ _ _ names)
theorem evaluated_names : NamesAccounted (evaluated layout).program.code names := Implementation.first_names _ _ _ _ names
variable [Add F] (add : Implementation .unit layout.arithmetic.pair layout.cache.value (fun value => value.1 + value.2))
    (addNames : NamesAccounted add.program.code names)
    {slots : Nat} (addBuffers : add.program.code.memBound ≤ slots) (reserve : slots + 4 < 2 ^ w)
include addNames in
theorem numerator_names : NamesAccounted (numerator layout add).program.code names := (operands_names layout names).seq addNames
include addNames in
theorem saved_names : NamesAccounted (saved layout add addBuffers reserve).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (target_names layout names) (numerator_names layout names add addNames)
include addNames in
theorem normalize_names : NamesAccounted (normalize layout add addBuffers reserve).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (evaluated_names layout names) (saved_names layout names add addNames addBuffers reserve)
variable [Zero F] [DecidableEq M] (zeroValid : layout.cache.value.valid 0)
include addNames in
theorem good_names : NamesAccounted (good layout add addBuffers reserve zeroValid).program.code names :=
  (normalize_names layout names add addNames addBuffers reserve).seq
    (CacheTargetFrame.implementation_names layout.good names (zero layout zeroValid))
omit [Add F] in
theorem bad_names : NamesAccounted (bad layout zeroValid).program.code names := CacheTargetFrame.implementation_names _ names _
end Signatures.Runtime.CaliperBackend.BLSFinalFrame
