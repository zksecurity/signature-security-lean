import Signatures.BLS.Spec.LazyAGMList

/-! Lazy AGM reductions for finite weighted lists of bases. The base-index and
message types are independent. Signing, extraction, and the final target share
one cache; no enumeration of either type occurs in these programs. -/

open OracleComp OracleSpec Model.LazyAGM

namespace Model.LazyAGM.WeightedReduction

variable {F ι M R G₁ G₂ : Type}

/-- Expand each actual signing-reply occurrence into its weighted bases.
Missing coefficients are zero; extra coefficients have no matching reply. -/
def signedTerms [MulZeroOneClass F] (terms : M → List (ι × F))
    (coeff : List F) (tr : List (M × G₁)) : List (ι × F) :=
  (tr.mapIdx fun n p => (terms p.1).map fun t => (t.1, tokenCoeff coeff n * t.2)).flatten

def privateOracle [AddCommMonoid R] [SMul F R]
    (terms : M → List (ι × F)) (hash sign : R → G₁) :
    QueryImpl (advSpec ι M G₁) (StateT (Transcript ι M G₁) (OracleComp (baseSpec ι R))) :=
  handler (fun n => (liftM ((baseSpec ι R).query (.inl n)) : OracleComp (baseSpec ι R) _))
    (fun i => hash <$> (liftM ((baseSpec ι R).query (.inr i)) : OracleComp (baseSpec ι R) R))
    (fun m => sign <$> evalTerms (terms m))

def privateRun [AddCommMonoid R] [SMul F R]
    (terms : M → List (ι × F)) (hash sign : R → G₁)
    (A : Adversary F ι M G₁ G₂) (pk : G₂) :
    OracleComp (baseSpec ι R) (Output F M × Transcript ι M G₁) :=
  (simulateQ (privateOracle terms hash sign) (A.main pk)).run ([], [])

variable [Field F] [AddCommGroup G₁] [Module F G₁]

def goodProgram (terms : M → List (ι × F)) (g X : G₁) (pk : G₂)
    (A : Adversary F ι M G₁ G₂) : OracleComp (baseSpec ι F) F := do
  let (out, tr) ← privateRun terms (fun rho : F => rho • g) (fun rho => rho • X) A pk
  let hashes ← evalTerms (BLS.LazyAGM.Reduction.traceTerms out.γ tr.1)
  let signatures ← evalTerms (signedTerms terms out.ξ tr.2)
  let target ← evalTerms (terms out.mstar)
  pure ((out.β + hashes) / (target - signatures))

def badProgram (terms : M → List (ι × F)) (g X : G₁) (pk : G₂) (kappa : F)
    (A : Adversary F ι M G₁ G₂) : OracleComp (baseSpec ι (F × F)) F := do
  let point := fun masks : F × F => masks.1 • X + masks.2 • g
  let (out, tr) ← privateRun terms point (fun masks => kappa • point masks) A pk
  let signatures ← evalTerms (signedTerms terms out.ξ tr.2)
  let target ← evalTerms (terms out.mstar)
  pure (-(target.2 - signatures.2) / (target.1 - signatures.1))

variable [SampleableType F] [DecidableEq ι]

noncomputable def goodReductionLazy (terms : M → List (ι × F))
    (A : Adversary F ι M G₁ G₂) : AlgebraicGroupModel.DLog11Adversary F G₁ G₂ :=
  fun g X _ pk =>
    (simulateQ (BLS.CoCDH.lazyCoinImpl (D := ι) (R := F))
      (goodProgram terms g X pk A)).run' ∅

noncomputable def goodReductionList (terms : M → List (ι × F))
    (A : Adversary F ι M G₁ G₂) : AlgebraicGroupModel.DLog11Adversary F G₁ G₂ :=
  fun g X _ pk =>
    (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := ι) (R := F))
      (goodProgram terms g X pk A)).run' []

variable [AddCommGroup G₂] [Module F G₂]

noncomputable def badReductionLazy (terms : M → List (ι × F))
    (A : Adversary F ι M G₁ G₂) : AlgebraicGroupModel.DLog11Adversary F G₁ G₂ :=
  fun g X g₂ _ => do
    let kappa ← ($ᵗ F : ProbComp F)
    (simulateQ (BLS.CoCDH.lazyCoinImpl (D := ι) (R := F × F))
      (badProgram terms g X (kappa • g₂) kappa A)).run' ∅

noncomputable def badReductionList (terms : M → List (ι × F))
    (A : Adversary F ι M G₁ G₂) : AlgebraicGroupModel.DLog11Adversary F G₁ G₂ :=
  fun g X g₂ _ => do
    let kappa ← ($ᵗ F : ProbComp F)
    (simulateQ (BLS.LazyAGM.Reduction.privateListOracle (M := ι) (R := F × F))
      (badProgram terms g X (kappa • g₂) kappa A)).run' []

end Model.LazyAGM.WeightedReduction
