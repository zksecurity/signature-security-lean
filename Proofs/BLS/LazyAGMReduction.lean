import Signatures.BLS.Spec.LazyAGMReduction
import Proofs.BLS.CoCDH.LazyCoin

/-! Proof-side fixed-table interpretations of the lazy AGM programs. Such tables
are used only to connect to the established probability proof; the new programs
query their shared caches on demand. -/

open OracleComp OracleSpec Model.LazyAGM

namespace BLS.LazyAGM.Reduction

variable {F M R G₁ G₂ : Type}

theorem table_random (table : M → R) (n : Nat) :
    CoCDH.coinTableImpl table (.inl n) = (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := rfl

theorem table_lookup (table : M → R) (m : M) :
    CoCDH.coinTableImpl table (.inr m) = pure (table m) := rfl

theorem privateRun_table (table : M → R) (hash sign : R → G₁)
    (A : Adversary F M M G₁ G₂) (pk : G₂) :
    simulateQ (CoCDH.coinTableImpl table) (privateRun hash sign A pk) =
      fixedRun A pk (hash ∘ table) (sign ∘ table) := by
  apply simulateQ_StateT_compose (privateOracle hash sign) (CoCDH.coinTableImpl table)
    (fixedImpl (hash ∘ table) (sign ∘ table)) _ (A.main pk) ([], [])
  intro q tr
  rcases q with ((n | m) | m) <;>
    simp [privateOracle, fixedImpl, handler, table_random, table_lookup]

theorem evalTerms_table [AddCommMonoid R] [SMul F R] (table : M → R) (terms : List (M × F)) :
    simulateQ (CoCDH.coinTableImpl table) (evalTerms terms) =
      pure ((terms.map fun p => p.2 • table p.1).sum) := by
  induction terms with
  | nil => simp [evalTerms]
  | cons p rest ih =>
      rcases p with ⟨m, c⟩
      simp [evalTerms, table_lookup, ih]

def traceValue [Zero F] [AddCommMonoid R] [SMul F R]
    (coeff : List F) (tr : List (M × G₁)) (table : M → R) : R :=
  ((traceTerms coeff tr).map fun p => p.2 • table p.1).sum

variable [Field F] [AddCommGroup G₁] [Module F G₁]

theorem goodProgram_table (rho : M → F) (g X : G₁) (pk : G₂) (A : Adversary F M M G₁ G₂) :
    simulateQ (CoCDH.coinTableImpl rho) (goodProgram g X pk A) = (do
      let (out, tr) ← fixedRun A pk (fun m => rho m • g) (fun m => rho m • X)
      pure ((out.β + traceValue out.γ tr.1 rho) / (rho out.mstar - traceValue out.ξ tr.2 rho))) := by
  simp [goodProgram, privateRun_table, evalTerms_table, table_lookup, traceValue,
    Function.comp_def]

theorem badProgram_table (masks : M → F × F) (g X : G₁) (pk : G₂) (kappa : F)
    (A : Adversary F M M G₁ G₂) :
    simulateQ (CoCDH.coinTableImpl masks) (badProgram g X pk kappa A) = (do
      let (out, tr) ← fixedRun A pk
        (fun m => (masks m).1 • X + (masks m).2 • g)
        (fun m => kappa • ((masks m).1 • X + (masks m).2 • g))
      let signed := traceValue out.ξ tr.2 masks
      pure (-((masks out.mstar).2 - signed.2) / ((masks out.mstar).1 - signed.1))) := by
  simp [badProgram, privateRun_table, evalTerms_table, table_lookup, traceValue,
    Function.comp_def]

end BLS.LazyAGM.Reduction
