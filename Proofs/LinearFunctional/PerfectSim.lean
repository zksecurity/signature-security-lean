/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Signatures.LinearFunctional.Spec.Handle
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Perfect simulation for the linear-functional schemes (BLS / OOPS / Proximity)

The adaptive good-branch reduction answers signing queries **without the secret
key** `α`: it programs the public base points as `Hᵢ = ρᵢ·g₁` (known `ρᵢ`) and signs a message
`m` with

  `σ = μ(m)·(α·g₁) = (∑ᵢ ρᵢ wᵢ(m))·(α·g₁)`,         (simulator uses the DLog challenge `α·g₁`)

whereas a **real signer** holds `α` and computes

  `σ = α·(∑ᵢ wᵢ(m)·Hᵢ)`.                              (real — uses the secret `α`)

`functional_perfect_sim` proves these give the adversary an **identical view**: programming the base
points `Hᵢ = ρᵢ·g₁` for uniform `ρ` is distributed exactly like real uniform base points (a product
"one-time pad", `evalSPMF_map_bijective_uniform_cross`, needing `(·•g₁)` bijective), and under that
coupling the simulator's signature equals the real one (`simSign_eq_realSign`, the scheme-agnostic identity
`α·(c·g₁) = c·(α·g₁)`).  Hence the reduction is a *perfect* simulation of the real signing oracle.

BLS hash values, OOPS topic base points, and Proximity slot base points are sampled up front, so the
simulation reduces to a single product bijection plus the signing identity. Each scheme instantiates
this theorem through its end-to-end reduction.
-/

open OracleComp AlgebraicGroupModel AlgebraicGroupModel.LinFunctional Finset

namespace AlgebraicGroupModel.LinFunctional

variable {F M ι G₁ : Type} [Field F] [SampleableType F] [Fintype F]
  [AddCommGroup G₁] [Module F G₁] [Fintype G₁]
  [Fintype ι] [DecidableEq ι]

/-- The **real signer** for weight family `w`: secret key `α`, real base points `H : ι → G₁`, signs
`m` as `α·(∑ᵢ wᵢ(m)·Hᵢ)`. -/
def realSign (w : ι → M → F) (α : F) (H : ι → G₁) (m : M) : G₁ := α • ∑ i, w i m • H i

/-- The **reduction's simulator**: DLog challenge `α·g₁`, programmed base points `ρᵢ·g₁`, signs `m` as
`μ(m)·(α·g₁) = (∑ᵢ ρᵢ wᵢ(m))·(α·g₁)` — never touching the secret `α`. -/
def simSign (w : ι → M → F) (αg₁ : G₁) (ρ : ι → F) (m : M) : G₁ := muW w ρ m • αg₁

omit [SampleableType F] [Fintype F] [Fintype G₁] [DecidableEq ι] in
/-- **Signing perfect-simulation identity.**  Under the base-point coupling `Hᵢ = ρᵢ·g₁`, the
simulator's signature (DLog challenge, no secret) equals the real signature (secret key): the
scheme-agnostic `α·(c·g₁) = c·(α·g₁)` summed over the weights. -/
theorem simSign_eq_realSign (w : ι → M → F) (g₁ : G₁) (α : F) (ρ : ι → F) (m : M) :
    simSign w (α • g₁) ρ m = realSign w α (fun i => ρ i • g₁) m := by
  simp only [simSign, realSign, muW, Finset.smul_sum, smul_smul]
  rw [Finset.sum_mul, Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ => by congr 1; ring

/-- **Perfect simulation of the signing oracle.**  For any continuation `cont` (the rest of the
game — the adversary plus verification — receiving the base points and a signing oracle), running it
with the **reduction's** setup (programmed base points `ρᵢ·g₁`, simulator signing with the DLog
challenge `α·g₁`) is distributed **identically** to running it with the **real** setup (uniform base points,
signing with the secret `α`).  So the reduction is a perfect simulation: the adversary's forgery
probability is unchanged. -/
theorem functional_perfect_sim {γ : Type} [SampleableType (ι → F)] [SampleableType (ι → G₁)]
    (w : ι → M → F) (g₁ : G₁) (α : F) (hgen : Function.Bijective (fun ρ : F => ρ • g₁))
    (cont : (ι → G₁) → (M → G₁) → ProbComp γ) :
    𝒮[do let ρ ← ($ᵗ (ι → F) : ProbComp (ι → F)); cont (fun i => ρ i • g₁) (simSign w (α • g₁) ρ)]
      = 𝒮[do let H ← ($ᵗ (ι → G₁) : ProbComp (ι → G₁)); cont H (realSign w α H)] := by
  have hf : Function.Bijective (fun ρ : ι → F => fun i => ρ i • g₁) :=
    (Equiv.piCongrRight fun _ => Equiv.ofBijective _ hgen).bijective
  have hsign (ρ : ι → F) : simSign w (α • g₁) ρ = realSign w α (fun i => ρ i • g₁) :=
    funext fun m => simSign_eq_realSign w g₁ α ρ m
  simp_rw [hsign]
  exact evalSPMF_ext (probOutput_bind_bijective_uniform_cross (ι → F) _ hf
    (fun H => cont H (realSign w α H)))

end AlgebraicGroupModel.LinFunctional
