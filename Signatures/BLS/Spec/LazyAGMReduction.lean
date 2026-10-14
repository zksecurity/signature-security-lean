import Signatures.BLS.Spec.LazyAGM
import Signatures.BLS.CoCDH.Spec.Coron

/-! Lazy private-table BLS AGM solvers. Only encountered messages are queried.
The shared cache covers hashing, signing, transcript extraction, and the final
target; extraction queries do not add attacker-visible representation tokens.
Correspondence and quantitative compilation are separate proof obligations. -/

open OracleComp OracleSpec Model.LazyAGM

namespace BLS.LazyAGM.Reduction

variable {F M R G₁ G₂ : Type}

/-- Coefficients are indexed by actual reply occurrences. Missing coefficients
are zero and extra coefficients have no matching token, as in the source game. -/
def traceTerms [Zero F] (coeff : List F) (tr : List (M × G₁)) : List (M × F) :=
  tr.mapIdx fun n p => (p.1, tokenCoeff coeff n)

def privateOracle (hash sign : R → G₁) :
    QueryImpl (advSpec M M G₁) (StateT (Transcript M M G₁) (OracleComp (baseSpec M R))) :=
  handler (fun n => (liftM ((baseSpec M R).query (.inl n)) : OracleComp (baseSpec M R) _))
    (fun m => hash <$> (liftM ((baseSpec M R).query (.inr m)) : OracleComp (baseSpec M R) R))
    (fun m => sign <$> (liftM ((baseSpec M R).query (.inr m)) : OracleComp (baseSpec M R) R))

def privateRun (hash sign : R → G₁) (A : Adversary F M M G₁ G₂) (pk : G₂) :
    OracleComp (baseSpec M R) (Output F M × Transcript M M G₁) :=
  (simulateQ (privateOracle hash sign) (A.main pk)).run ([], [])

variable [Field F] [SampleableType F] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

def goodProgram (g X : G₁) (pk : G₂) (A : Adversary F M M G₁ G₂) :
    OracleComp (baseSpec M F) F := do
  let (out, tr) ← privateRun (fun rho : F => rho • g) (fun rho => rho • X) A pk
  let hashes ← evalTerms (traceTerms out.γ tr.1)
  let signatures ← evalTerms (traceTerms out.ξ tr.2)
  let target ← (liftM ((baseSpec M F).query (.inr out.mstar)) : OracleComp (baseSpec M F) F)
  pure ((out.β + hashes) / (target - signatures))

def badProgram (g X : G₁) (pk : G₂) (kappa : F) (A : Adversary F M M G₁ G₂) :
    OracleComp (baseSpec M (F × F)) F := do
  let point := fun masks : F × F => masks.1 • X + masks.2 • g
  let (out, tr) ← privateRun point (fun masks => kappa • point masks) A pk
  let signatures ← evalTerms (traceTerms out.ξ tr.2)
  let target ← (liftM ((baseSpec M (F × F)).query (.inr out.mstar)) :
    OracleComp (baseSpec M (F × F)) (F × F))
  pure (-(target.2 - signatures.2) / (target.1 - signatures.1))

/-- Good branch with one persistent lazy scalar cache. No finite-message
instance or full-domain initialization is required. -/
noncomputable def goodReductionLazy (A : Adversary F M M G₁ G₂) :
    AlgebraicGroupModel.DLog11Adversary F G₁ G₂ := fun g X _ pk =>
  (simulateQ (CoCDH.lazyCoinImpl (D := M) (R := F)) (goodProgram g X pk A)).run' ∅

/-- Bad branch with a known fresh signing key and a persistent cache of
independent mask pairs. Field division retains the source's zero-denominator behavior. -/
noncomputable def badReductionLazy (A : Adversary F M M G₁ G₂) :
    AlgebraicGroupModel.DLog11Adversary F G₁ G₂ := fun g X g₂ _ => do
  let kappa ← ($ᵗ F : ProbComp F)
  (simulateQ (CoCDH.lazyCoinImpl (D := M) (R := F × F))
    (badProgram g X (kappa • g₂) kappa A)).run' ∅

end BLS.LazyAGM.Reduction
