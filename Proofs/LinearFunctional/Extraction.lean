/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Proofs.LinearFunctional.PerfectSim
import Proofs.AlgebraicGroupModel.ForgeryGame
import Proofs.AlgebraicGroupModel.PairingExtraction
import Signatures.Model.DLog11
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# Linear-functional extraction ingredients

The adaptive proof uses the uniform linear-functional collision bound and the fixed-transcript
algebra below. These definitions impose no ordering on when the representation is produced.
-/

open BilinearGroup

open OracleComp AlgebraicGroupModel AlgebraicGroupModel.LinFunctional Finset

namespace AlgebraicGroupModel.LinFunctional

variable {F ι : Type} [Field F] [SampleableType F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]

/-- **Whole-vector forgery-functional collision.**  For a uniform table `ρ : ι → F` and a fixed
functional `L` with **some** nonzero coordinate `L_{jₖ}`, the relation `∑ᵢ Lᵢ ρᵢ = t` holds with
probability `≤ 1/|F|`.  The "nonzero functional of a uniform vector" kernel, as one clean statement. -/
theorem linear_functional_collision (L : ι → F) (jk : ι) (hLjk : L jk ≠ 0) (t : F) :
    Pr[fun ρ : ι → F => ∑ i, L i * ρ i = t | ($ᵗ (ι → F) : ProbComp (ι → F))]
      ≤ 1 / (Fintype.card F : ENNReal) := by
  have hsum : ∀ (g : ι → F) (u : F),
      (∑ i, L i * Function.update g jk u i) = L jk * u + ∑ i ∈ univ.erase jk, L i * g i := by
    intro g u
    rw [← Finset.add_sum_erase univ (fun i => L i * Function.update g jk u i) (mem_univ jk),
      Function.update_self]
    congr 1
    exact Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [probEvent_def, ← evalSPMF_uniformSample_bind_update (R := F) jk,
    DeferredSampling.evalSPMF_bind_comm, ← probEvent_def]
  simpa only [probEvent_bind_eq_tsum, probEvent_pure, hsum] using
    affine_uniform_collision ($ᵗ (ι → F)) (fun _ => L jk)
      (fun g => ∑ i ∈ univ.erase jk, L i * g i) (fun _ => t) (fun _ _ => hLjk)

/-! ## Fixed-transcript algebra -/

variable {M G₁ G₂ Gₜ : Type}
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] {Q : ℕ}

/-- A forged message, actual signing-query messages, and representation coefficients.
The adaptive runner supplies this data after interacting with the concrete public bases. -/
structure Forgery (F M ι : Type) (Q : ℕ) where
  /-- the forged message. -/
  mstar : M
  /-- the signing-query messages. -/
  v : Fin Q → M
  /-- coefficient on the generator `g₁`. -/
  β : F
  /-- coefficients on the base points. -/
  γ : ι → F
  /-- coefficients on the signatures. -/
  ξ : Fin Q → F

/-- The forged group element `σ* = β·g₁ + ∑ᵢ γᵢ·Hᵢ + ∑ⱼ ξⱼ·σⱼ` from base points `H` and a signing
oracle. -/
def forgeryElem (g₁ : G₁) (fo : Forgery F M ι Q) (H : ι → G₁) (signO : M → G₁) : G₁ :=
  fo.β • g₁ + (∑ i, fo.γ i • H i) + ∑ q, fo.ξ q • signO (fo.v q)

/-- The verification target as a group element `∑ᵢ wᵢ(m*)·Hᵢ` (`= μ*·g₁` in the reduction). -/
def targetElem (w : ι → M → F) (fo : Forgery F M ι Q) (H : ι → G₁) : G₁ :=
  ∑ i, w i fo.mstar • H i

/-- The reduction's representation `repr = ⟨A, B⟩` of the forgery: `A = β + ∑ᵢ γᵢ ρᵢ` (known `α`-free
part) and `B = ∑ⱼ ξⱼ μ(vⱼ)` (the `α`-coefficient). -/
def reprA (w : ι → M → F) (fo : Forgery F M ι Q) (ρ : ι → F) : AffineForm F :=
  ⟨fo.β + ∑ i, fo.γ i * ρ i, ∑ q, fo.ξ q * muW w ρ (fo.v q)⟩

omit [SampleableType F] [Fintype F] [DecidableEq F] [DecidableEq ι]
  [SampleableType G₁] [Fintype G₁] in
/-- Under the reduction (base points `ρᵢ·g₁`, simulator signing), the forged element is exactly
`repr.eval α · g₁`. -/
theorem forgeryElem_red (w : ι → M → F) (g₁ : G₁) (fo : Forgery F M ι Q) (α : F) (ρ : ι → F) :
    forgeryElem g₁ fo (fun i => ρ i • g₁) (simSign w (α • g₁) ρ)
      = (reprA w fo ρ).eval α • g₁ := by
  simp only [forgeryElem, simSign, reprA, AffineForm.eval, smul_smul, ← Finset.sum_smul, ← add_smul]
  congr 1
  rw [Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun x _ => by ring

omit [SampleableType F] [Fintype F] [DecidableEq F] [DecidableEq ι]
  [SampleableType G₁] [Fintype G₁] in
/-- Under the reduction, the verification target is `μ(m*)·g₁`. -/
theorem targetElem_red (w : ι → M → F) (g₁ : G₁) (fo : Forgery F M ι Q) (ρ : ι → F) :
    targetElem w fo (fun i => ρ i • g₁) = muW w ρ fo.mstar • g₁ := by
  simp only [targetElem, muW, Finset.sum_smul, smul_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]

omit [SampleableType F] [Fintype F] [DecidableEq F] [DecidableEq ι] in
/-- The non-degeneracy gap `μ* − repr.lin = Q(m*) − ∑ⱼ ξⱼ Q(vⱼ)` is the forgery functional
`∑ᵢ Lᵢ ρᵢ` of the topic vector (`Lᵢ = wᵢ(m*) − ∑ⱼ ξⱼ wᵢ(vⱼ)`). -/
theorem muW_sub_reprA_lin (w : ι → M → F) (fo : Forgery F M ι Q) (ρ : ι → F) :
    muW w ρ fo.mstar - (reprA w fo ρ).lin = ∑ i, Lcoeff w fo.mstar fo.v fo.ξ i * ρ i := by
  simp only [muW, reprA, Lcoeff, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q _ => by ring

end AlgebraicGroupModel.LinFunctional
