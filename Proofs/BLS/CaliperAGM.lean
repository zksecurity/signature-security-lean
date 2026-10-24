import Signatures.BLS.CaliperAGMParameters

/-! Construct the public Caliper DLog witnesses from the fixed component
contracts and the attacker's local code. Caller allowances are fixed by the
parameter record, so both solver budgets are independent of attacker choice. -/
namespace BLS.CaliperAGM
open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
variable {F G K M : Type} [Field F] [SampleableType F]
    [AddCommGroup G] [Module F G] [AddCommGroup K] [Module F K] [DecidableEq M]
    {queries : QueryAllowance} {generator : G} {keyGenerator : K}
    (P : Parameters F G K M queries generator keyGenerator) (A : AlgebraicAdversary P)

theorem reductions_within :
    P.within P.goodTime (BLS.LazyAGM.Reduction.goodReductionList A.proofView) ∧
    P.within P.badTime (BLS.LazyAGM.Reduction.badReductionList A.proofView) := by
  have good := BLSFull.good_dlogWithin (base := base F M) (key := messageTy) (val := scalarTy)
    P.layout P.routines P.primitiveBounds A.caller (AlgebraicAdversary.bounds (P := P) A)
    (primitives F M) comparison (comparison_correct F M) P.sampler queries.total P.scalarSource P.samplerCorrect
    P.samplerTime P.samplerWords P.samplerNames P.samplerFits P.addresses P.scalarLaw A.invariant P.logRoom P.cacheRoom
    A.correspondence A.proofView A.source_eq ⟨generator, P.generatorValid⟩ ⟨keyGenerator, P.keyGeneratorValid⟩
  have bad := BLSFull.bad_dlogWithin (base := base F M) (key := messageTy) (val := scalarTy)
    P.layout P.routines P.primitiveBounds A.caller (AlgebraicAdversary.bounds (P := P) A)
    (primitives F M) comparison (comparison_correct F M) P.sampler queries.total P.scalarSource P.samplerCorrect
    P.samplerTime P.samplerWords P.samplerNames P.samplerFits P.addresses P.scalarLaw A.invariant P.logRoom P.cacheRoom
    A.correspondence A.proofView A.source_eq ⟨generator, P.generatorValid⟩ ⟨keyGenerator, P.keyGeneratorValid⟩
  exact ⟨good.mono (Nat.le_max_left _ _) (Nat.le_max_left _ _) le_rfl,
    bad.mono (Nat.le_max_right _ _) (Nat.le_max_right _ _) le_rfl⟩
end BLS.CaliperAGM
