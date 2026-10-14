import Signatures.Runtime.LazyAGMExtraction
import Signatures.BLS.Proofs.LazyAGMQueries

/-! The implemented extraction phases are exactly the suffixes of the lazy
source solvers. Their private-query bounds depend on transcript lengths, not
the message universe. These bounds supply cache-growth invariants; they do
not replace the separate bounds on local computation. -/

open OracleComp OracleSpec Model.LazyAGM BLS.LazyAGM.Reduction

namespace Signatures.Runtime.LazyAGM

variable {F G₁ G₂ M : Type} [Field F]

theorem goodProgram_finish [AddCommGroup G₁] [Module F G₁]
    (g X : G₁) (pk : G₂) (A : Adversary F M M G₁ G₂) :
    goodProgram g X pk A = (do
      let (out, tr) ← privateRun (fun rho : F => rho • g) (fun rho => rho • X) A pk
      goodFinish out tr) := rfl

theorem badProgram_finish [AddCommGroup G₁] [Module F G₁]
    (g X : G₁) (pk : G₂) (kappa : F) (A : Adversary F M M G₁ G₂) :
    badProgram g X pk kappa A = (do
      let point := fun masks : F × F => masks.1 • X + masks.2 • g
      let (out, tr) ← privateRun point (fun masks => kappa • point masks) A pk
      badFinish out tr) := rfl

theorem goodFinish_queries (out : Output F M) (tr : Transcript M M G₁) :
    IsTotalQueryBound (goodFinish out tr) (tr.1.length + tr.2.length + 1) := by
  unfold goodFinish
  have h := isTotalQueryBound_bind (evalTerms_queries (R := F) (traceTerms out.γ tr.1))
    (fun hashes => isTotalQueryBound_bind (evalTerms_queries (R := F) (traceTerms out.ξ tr.2))
      (fun signatures => show IsTotalQueryBound (do
        let target : F ← liftM ((baseSpec M F).query (.inr out.mstar))
        pure ((out.β + hashes) / (target - signatures))) 1 from by
          simp [IsTotalQueryBound]))
  simpa only [traceTerms, List.length_mapIdx, Nat.add_assoc] using h

theorem badFinish_queries (out : Output F M) (tr : Transcript M M G₁) :
    IsTotalQueryBound (badFinish out tr) (tr.2.length + 1) := by
  unfold badFinish
  have h := isTotalQueryBound_bind (evalTerms_queries (R := F × F) (traceTerms out.ξ tr.2))
    (fun signatures => show IsTotalQueryBound (do
      let target : F × F ← liftM ((baseSpec M (F × F)).query (.inr out.mstar))
      pure (-(target.2 - signatures.2) / (target.1 - signatures.1))) 1 from by
        simp [IsTotalQueryBound])
  simpa only [traceTerms, List.length_mapIdx] using h

end Signatures.Runtime.LazyAGM
