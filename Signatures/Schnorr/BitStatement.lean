import Proofs.Schnorr.ROM
import Proofs.Runtime.SchnorrBits
import Proofs.Model.Hardness

/-! Schnorr security against the concrete bit-heap machine. The reduction is
compiled from the certified source, its full online budget is proved, and the
fair-bit sampling error is included in the security inequality. -/

namespace Schnorr.Statement

open OracleComp DiffieHellman WeierstrassCurve
open Signatures.Runtime Signatures.Runtime.Schnorr
open scoped ENNReal

variable {r p₁ p₂ w : Nat} [Fact r.Prime] [Fact p₁.Prime] [Fact p₂.Prime]
  {W₁ : Affine (ZMod p₁)} {W₂ : Affine (ZMod p₂)} {K M : Type}
  (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
  (encodeK : K → BitVec w) (encodeM : M → BitVec w)
  [DecidableEq K] [DecidableEq M] [Module (ZMod r) H₁] [Module (ZMod r) H₂]
  [SampleableType (ZMod r)] [SampleableType H₁]

/-- Hardness is for precompiled bit packages on encoded challenges. All online
loads, arithmetic, memory scans, replay, and bounded fair-bit sampling are
charged. Hardness also limits stored code/data to the compiled package's cells.
Neither the compiler nor the mathematical success test runs as part of the
solver. The added error is the probability of any sampler exhaustion. -/
theorem schnorr_eufcma_of_dlog_bit_hardness
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    (g : H₁) (hgen : Function.Bijective (fun x : ZMod r => x • g))
    {adv : Schnorr.ROM.Adversary (F := ZMod r) (M := M) g}
    (qS qH : Nat) (hQ : ∀ pk, FiatShamir.signHashQueryBound (M := M) (oa := adv.main pk) qS qH)
    {cost : PrimitiveCosts} (sampling : Machine.SamplingCosts)
    (hsampling : ∀ n, n < 2^(sampling.uniform n))
    {randomBound localTime : Nat} {queries : Fin 3 → Nat}
    (cert : SourceCertificate (G₂ := H₂) (K := K) cost randomBound localTime queries adv.main)
    (k bits : Nat) (hqH : qH < 2^bits) (hdata : NaturalRange.ValueBound bits cert.data)
    (hwidth : bits+cert.targetBudget sampling qH ≤ w) (epsilon : ℝ≥0∞)
    (hhard : Model.HardWithin (HeapMachine.dlogAdvantage (r := r) w g)
      (HeapMachine.dlogWithin w H₁
        (cert.bitCode H₁ H₂ encodeK encodeM k g qH).cells)
      ((cert.targetBudget sampling qH+4)*cert.bitFactor (w := w) H₁ H₂ sampling k qH) epsilon) :
    let eps := 𝒟[Schnorr.ROM.game g adv] {true} -
      (qS : ℝ≥0∞)*(qS+qH)*(Nat.card (ZMod r) : ℝ≥0∞)⁻¹
    eps * (eps/(qH+1 : ℝ≥0∞) - (Nat.card (ZMod r) : ℝ≥0∞)⁻¹) ≤
      epsilon + cert.targetBudget sampling qH*(1/2 : ℝ≥0∞)^k := by
  let pack := cert.bitCode H₁ H₂ encodeK encodeM k g qH
  have hcost : HeapMachine.dlogWithin w H₁ pack.cells
      ((cert.targetBudget sampling qH+4)*cert.bitFactor (w := w) H₁ H₂ sampling k qH) pack := by
    refine ⟨le_refl _, ?_⟩
    intro pk out hout
    have h := cert.bitCode_costed H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm
      sampling hsampling g pk k qH bits hqH hdata hwidth
    obtain ⟨source, _, h⟩ := h.support_left out hout
    simpa only [Nat.add_comm 3, Nat.add_assoc] using h.2.2.2
  have herror (x : ZMod r) := cert.bitCode_error H₁ H₂ encodeK encodeM
    hr h₁ h₂ hr' h₁' h₂' hk hm sampling hsampling g (x • g) k qH bits hqH hdata hwidth
  have hevent (x : ZMod r) :=
    (MarkedProbability.event_le_add_bad (herror x).1 (fun y => decide (y = x))).trans
      (add_le_add (le_refl _) (herror x).2)
  have hprob : 𝒟[dlogExperiment g (Schnorr.dlogReduction (ZMod r) H₁ g M adv qH)] {true} ≤
      HeapMachine.dlogAdvantage (r := r) w g pack +
        cert.targetBudget sampling qH*(1/2 : ℝ≥0∞)^k := by
    rw [MachineSampling.ideal_measure, PMF.toMeasure_apply_singleton _ true (by simp)]
    simp only [dlogExperiment, simulateQ_bind, simulateQ_pure, MachineSampling.uniformSample_law,
      HeapMachine.dlogAdvantage, PMF.bind_apply]
    calc
      _ ≤ ∑' x : ZMod r, PMF.uniformOfFintype (ZMod r) x *
          (((HeapMachine.scalarLaw r w pack ((x • g : H₁) : W₁.Point)).map
            (fun out => decide (out.1 = x))) true + cert.targetBudget sampling qH*(1/2 : ℝ≥0∞)^k) := by
        apply ENNReal.tsum_le_tsum
        intro x
        apply mul_le_mul' (le_refl _)
        simpa only [bind_pure_comp, PMF.monad_map_eq_map] using hevent x
      _ = _ := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hsecurity := Schnorr.ROM.Proofs.security g hgen adv qS qH hQ
  simpa only [Nat.card_eq_fintype_card] using hsecurity.trans
    (hprob.trans (add_le_add (hhard pack hcost) (le_refl _)))

end Schnorr.Statement
