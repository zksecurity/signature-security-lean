import Proofs.Runtime.Caliper.WeightedSecurity
import Signatures.Proximity.Spec.LazyAGM

/-! Caliper parameters specialized to the original Proximity index and message types.
Local routine costs and caller allowances determine both full reduction budgets.
The shared construction derives challenge coverage and reuses one attacker. -/
namespace Proximity.CaliperAGM
open Signatures.Runtime
variable (F G PK Slot : Type) [Field F] [SampleableType F] [DecidableEq Slot]
    [AddCommGroup G] [Module F G] [AddCommGroup PK] [Module F PK]
    (dimension : Nat) (queries : WeightedCaliper.QueryAllowance) (generator : G) (keyGenerator : PK)
abbrev Parameters := WeightedCaliper.Parameters F G PK (Option (Fin dimension) × Slot) ((Fin dimension → F) × Slot)
  queries (LazyAGM.terms) generator keyGenerator
end Proximity.CaliperAGM
