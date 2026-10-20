import Signatures.Runtime.Caliper.WeightedSecurity
import Signatures.OOPS.Spec.LazyAGM

/-! Caliper parameters specialized to the original OOPS index and message types.
Local routine costs and caller allowances determine both full reduction budgets.
The shared construction derives challenge coverage and reuses one attacker. -/
namespace OOPS.CaliperAGM
open Signatures.Runtime
variable (F G PK Topic : Type) [Field F] [SampleableType F] [DecidableEq Topic]
    [AddCommGroup G] [Module F G] [AddCommGroup PK] [Module F PK]
    (degree : Nat) (queries : WeightedCaliper.QueryAllowance) (generator : G) (keyGenerator : PK)
abbrev Parameters := WeightedCaliper.Parameters F G PK (Topic × Fin (degree + 1)) (F × Topic)
  queries (LazyAGM.terms degree) generator keyGenerator
end OOPS.CaliperAGM
