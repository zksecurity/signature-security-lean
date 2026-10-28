import Proofs.Runtime.Caliper.SyncWrapSecurity

/-! Caliper parameters specialized to synchronized PS: the inner single-signer interface
(period hashes, period/message signing), the wrapper's capacities and routines for the two
weighted schemes, one scalar sampler and numeric caller allowances. All four reduction budgets
are derived; the attacker supplies one local caller and source witness. -/
namespace SynchronizedPS.CaliperAGM
open Signatures.Runtime
variable (F G₁ G₂ Period : Type) [Field F] [SampleableType F] [DecidableEq Period]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    (queries : WeightedCaliper.QueryAllowance) (generator : G₁) (keyGenerator : G₂)
abbrev Parameters := SyncWrapCaliper.Parameters F G₁ G₂ Period queries generator keyGenerator
end SynchronizedPS.CaliperAGM
