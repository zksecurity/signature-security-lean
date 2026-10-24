import Proofs.Runtime.HeapDLog
import Proofs.Runtime.SchnorrSeededMachineCorrectness

/-! The source-derived fully seeded Schnorr reduction compiled to bit operations.
Both the online cost and the probability comparison with ideal randomness are
proved. Bounded rejection contributes an explicit accumulated error. -/

namespace Signatures.Runtime.Schnorr

open HeapBits SharedHeap OracleComp WeierstrassCurve

variable {r p₁ p₂ w : Nat} [Fact r.Prime] [Fact p₁.Prime] [Fact p₂.Prime]
  {W₁ : Affine (ZMod p₁)} {W₂ : Affine (ZMod p₂)} {K M : Type}
  (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
  (encodeK : K → BitVec w) (encodeM : M → BitVec w)
  [DecidableEq K] [DecidableEq M] [Module (ZMod r) H₁] [Module (ZMod r) H₂]
  [SampleableType (ZMod r)] [SampleableType H₁]

def SourceCertificate.seededTargetBudget {cost : PrimitiveCosts} {randomBound localTime : Nat}
    {queries : Fin 3 → Nat} {adv}
    (cert : SourceCertificate (F := ZMod r) (G₁ := H₁) (G₂ := H₂) (K := K) (M := M)
      cost randomBound localTime queries adv) (sampling : Machine.SamplingCosts) (g : H₁) (qH : Nat) : Nat :=
  SeedTape.packagePrice cost sampling qH randomBound cert.code localTime queries g cert.data

/-- A static bit program for both passes, including fixed adversary data. -/
def SourceCertificate.seededBitCode {cost : PrimitiveCosts} {randomBound localTime : Nat}
    {queries : Fin 3 → Nat} {adv}
    (cert : SourceCertificate (F := ZMod r) (G₁ := H₁) (G₂ := H₂) (K := K) (M := M)
      cost randomBound localTime queries adv) (k : Nat) (g : H₁) (qH : Nat) : HeapMachine.Package :=
  HeapMachine.compilePackage H₁ H₂ encodeK encodeM k (SeedTape.forkPackage qH randomBound cert.code localTime queries g cert.data)

def SourceCertificate.seededBitFactor {cost : PrimitiveCosts} {randomBound localTime : Nat}
    {queries : Fin 3 → Nat} {adv}
    (cert : SourceCertificate (F := ZMod r) (G₁ := H₁) (G₂ := H₂) (K := K) (M := M)
      cost randomBound localTime queries adv) (sampling : Machine.SamplingCosts) (g : H₁) (k qH : Nat) : Nat :=
  HeapMachine.packageFactor w r k (3+cert.seededTargetBudget H₁ H₂ sampling g qH) 3 (SeedTape.sourceForkCode qH randomBound cert.code localTime queries)

set_option maxHeartbeats 1000000 in
/-- For every bit path, the concrete extractor returns the marked reference
value and uses at most `(seededTargetBudget + 4) * bitFactor` bit-cell steps. The four
extra source units cover loading the one challenge register and sequencing. -/
theorem SourceCertificate.seededBitCode_costed
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    {cost : PrimitiveCosts} (sampling : Machine.SamplingCosts)
    (hsampling : ∀ n, n < 2^(sampling.uniform n))
    {randomBound localTime : Nat} {queries : Fin 3 → Nat} (g pk : H₁)
    {adv : _root_.Schnorr.ROM.Adversary (F := ZMod r) (M := M) g}
    (cert : SourceCertificate (G₂ := H₂) (K := K) cost randomBound localTime queries adv.main)
    (k qH bits : Nat) (hdata : NaturalRange.ValueBound bits cert.data)
    (hwidth : bits+cert.seededTargetBudget H₁ H₂ sampling g qH ≤ w) :
    QueryTreeRel (fun actual source =>
      HeapExpression.ResultSpec (t := scalar) w (3*w+1) (atomRep H₁ H₂ encodeK encodeM) []
        (3+source.1.steps) source.1.value actual.1 ∧ actual.2 = source.2 ∧
      actual.1.steps ≤ (3+source.1.steps+1)*cert.seededBitFactor (w := w) H₁ H₂ sampling g k qH ∧
      actual.1.steps ≤ (3+cert.seededTargetBudget H₁ H₂ sampling g qH+1)*cert.seededBitFactor (w := w) H₁ H₂ sampling g k qH)
      ((cert.seededBitCode H₁ H₂ encodeK encodeM k g qH).run
        (HeapData.encodeEnv (r := r) (Γ := [point₁]) H₁ H₂ encodeK encodeM (pk, ())))
      (HeapMachine.packageSemantics H₁ H₂ (w := w) k cost sampling
        (SeedTape.forkPackage qH randomBound cert.code localTime queries g cert.data) (pk, ())) := by
  apply HeapMachine.compilePackage_costed H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm
    cost k sampling hsampling (SeedTape.forkPackage qH randomBound cert.code localTime queries g cert.data) (pk, ())
    bits (cert.seededTargetBudget H₁ H₂ sampling g qH) ⟨trivial, trivial⟩ ⟨trivial, hdata, trivial⟩ hwidth
  intro out hout
  have hb := SeedTape.forkPackage_bound cost sampling qH randomBound cert.code pk g cert.data
    localTime queries (cert.budget pk) out hout
  exact hb

open scoped ENNReal

set_option maxHeartbeats 1000000 in
/-- Success probabilities now concern the actual compiled two-pass extractor.
The error allowance is derived from its original machine budget, including
adaptive sampling in either pass, rather than an assumed sampler count. -/
theorem SourceCertificate.seededBitCode_error
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    {cost : PrimitiveCosts} (sampling : Machine.SamplingCosts)
    (hsampling : ∀ n, n < 2^(sampling.uniform n))
    {randomBound localTime : Nat} {queries : Fin 3 → Nat} (g pk : H₁)
    {adv : _root_.Schnorr.ROM.Adversary (F := ZMod r) (M := M) g}
    (cert : SourceCertificate (G₂ := H₂) (K := K) cost randomBound localTime queries adv.main)
    (k qH bits : Nat) (hdata : NaturalRange.ValueBound bits cert.data)
    (hwidth : bits+cert.seededTargetBudget H₁ H₂ sampling g qH ≤ w) :
    let law := HeapMachine.scalarLaw r w (cert.seededBitCode H₁ H₂ encodeK encodeM k g qH) (pk : W₁.Point)
    MarkedProbability.GoodLe law
      (simulateQ MachineSampling.uniformNaturals (Seeded.dlogReduction cost randomBound localTime queries g adv cert qH g pk)) ∧
      MarkedProbability.bad law ≤
        cert.seededTargetBudget H₁ H₂ sampling g qH * (1/2 : ℝ≥0∞)^k := by
  have hfit : r ≤ 2^w := (Nat.le_mul_self r).trans hr
  have hcost := cert.seededBitCode_costed H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm
    sampling hsampling g pk k qH bits hdata hwidth
  have he := hcost.map_eq (fun out => (HeapMachine.scalarValue r out.1.value, out.2))
    (fun out => (out.1.value, out.2)) (fun actual source h =>
      Prod.ext (HeapMachine.scalarValue_eq H₁ H₂ encodeK encodeM hfit h.1) h.2.1)
  have he := congrArg (simulateQ HeapMachine.fairBits) he
  simp only [simulateQ_map, PMF.monad_map_eq_map] at he
  have hp := HeapMachine.package_error H₁ H₂ (w := w) k cost sampling
    (SeedTape.forkPackage qH randomBound cert.code localTime queries g cert.data) (pk, ()) (cert.seededTargetBudget H₁ H₂ sampling g qH)
    (by omega) hfit hsampling (fun out hout => by
      have hb := SeedTape.forkPackage_bound cost sampling qH randomBound cert.code pk g cert.data
        localTime queries (cert.budget pk) out hout
      exact hb)
  have hreduce : Run.value <$> (SeedTape.forkPackage qH randomBound cert.code localTime queries g cert.data).run cost sampling (pk, ()) =
      Seeded.dlogReduction cost randomBound localTime queries g adv cert qH g pk := by
    rw [Machine.Package.run_eq, Functor.map_map]
    exact SeedTape.sourceForkCode_reduction cost sampling qH randomBound cert.code localTime queries pk g cert.data
  have hideal := congrArg (simulateQ MachineSampling.uniformNaturals) hreduce
  simp only [simulateQ_map, PMF.monad_map_eq_map] at hideal
  change MarkedProbability.GoodLe _ _ ∧ MarkedProbability.bad _ ≤ _
  have he : HeapMachine.scalarLaw r w (cert.seededBitCode H₁ H₂ encodeK encodeM k g qH) (pk : W₁.Point) = _ := he
  constructor
  · simpa only [he, hideal] using hp.1.map Run.value
  · simpa only [he, MarkedProbability.bad_map] using hp.2

end Signatures.Runtime.Schnorr
