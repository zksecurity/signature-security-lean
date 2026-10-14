import Signatures.BLS.Spec.LazyAGMReduction
import VCVio.OracleComp.QueryTracking.ListCache

/-! A finite association-list representation for the lazy AGM private cache.
Lookup scans stored entries only. A miss samples once and prepends one entry;
a hit preserves the list. Runtime accounting is a separate compiler obligation. -/

open OracleComp OracleSpec Model.LazyAGM

namespace BLS.LazyAGM.Reduction

variable {F M R G₁ G₂ : Type}

noncomputable def privateListOracle [DecidableEq M] [SampleableType R] :
    QueryImpl (baseSpec M R) (StateT (List (M × R)) ProbComp) :=
  (fun n => StateT.mk fun cache =>
    (fun r => (r, cache)) <$> (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))) +
    QueryImpl.ListCache.handler (uniformSampleImpl (spec := M →ₒ R))

variable [Field F] [SampleableType F] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

noncomputable def goodReductionList (A : Adversary F M M G₁ G₂) :
    AlgebraicGroupModel.DLog11Adversary F G₁ G₂ := fun g X _ pk =>
  (simulateQ (privateListOracle (M := M) (R := F)) (goodProgram g X pk A)).run' []

noncomputable def badReductionList (A : Adversary F M M G₁ G₂) :
    AlgebraicGroupModel.DLog11Adversary F G₁ G₂ := fun g X g₂ _ => do
  let kappa ← ($ᵗ F : ProbComp F)
  (simulateQ (privateListOracle (M := M) (R := F × F))
    (badProgram g X (kappa • g₂) kappa A)).run' []

end BLS.LazyAGM.Reduction
