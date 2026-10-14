import Signatures.Runtime.HeapDLog
import Signatures.Runtime.SchnorrReduction

/-! The actual certified Schnorr two-pass reduction compiled to bit operations.
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

/-- A static bit program for both passes, including fixed adversary data. -/
def SourceCertificate.bitCode {cost : PrimitiveCosts} {randomBound localTime : Nat}
    {queries : Fin 3 → Nat} {adv}
    (cert : SourceCertificate (F := ZMod r) (G₁ := H₁) (G₂ := H₂) (K := K) (M := M)
      cost randomBound localTime queries adv) (k : Nat) (g : H₁) (qH : Nat) : HeapMachine.Package :=
  HeapMachine.compilePackage H₁ H₂ encodeK encodeM k (forkPackage randomBound cert.code g qH cert.data)

def SourceCertificate.bitFactor {cost : PrimitiveCosts} {randomBound localTime : Nat}
    {queries : Fin 3 → Nat} {adv}
    (cert : SourceCertificate (F := ZMod r) (G₁ := H₁) (G₂ := H₂) (K := K) (M := M)
      cost randomBound localTime queries adv) (sampling : Machine.SamplingCosts) (k qH : Nat) : Nat :=
  HeapMachine.packageFactor w r k (3+cert.targetBudget sampling qH) 4 (forkCode randomBound cert.code)

/-- For every bit path, the concrete extractor returns the marked reference
value and uses at most `(targetBudget + 4) * bitFactor` bit-cell steps. The four
extra source units cover loading the one challenge register and sequencing. -/
theorem SourceCertificate.bitCode_costed
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    {cost : PrimitiveCosts} (sampling : Machine.SamplingCosts)
    (hsampling : ∀ n, n < 2^(sampling.uniform n))
    {randomBound localTime : Nat} {queries : Fin 3 → Nat} (g pk : H₁)
    {adv : _root_.Schnorr.ROM.Adversary (F := ZMod r) (M := M) g}
    (cert : SourceCertificate (G₂ := H₂) (K := K) cost randomBound localTime queries adv.main)
    (k qH bits : Nat) (hqH : qH < 2^bits) (hdata : NaturalRange.ValueBound bits cert.data)
    (hwidth : bits+cert.targetBudget sampling qH ≤ w) :
    QueryTreeRel (fun actual source =>
      HeapExpression.ResultSpec (t := scalar) w (3*w+1) (atomRep H₁ H₂ encodeK encodeM) []
        (3+source.1.steps) source.1.value actual.1 ∧ actual.2 = source.2 ∧
      actual.1.steps ≤ (3+source.1.steps+1)*cert.bitFactor (w := w) H₁ H₂ sampling k qH ∧
      actual.1.steps ≤ (3+cert.targetBudget sampling qH+1)*cert.bitFactor (w := w) H₁ H₂ sampling k qH)
      ((cert.bitCode H₁ H₂ encodeK encodeM k g qH).run
        (HeapData.encodeEnv (r := r) (Γ := [point₁]) H₁ H₂ encodeK encodeM (pk, ())))
      (HeapMachine.packageSemantics H₁ H₂ (w := w) k cost sampling
        (forkPackage randomBound cert.code g qH cert.data) (pk, ())) := by
  apply HeapMachine.compilePackage_costed H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm
    cost k sampling hsampling (forkPackage randomBound cert.code g qH cert.data) (pk, ())
    bits (cert.targetBudget sampling qH) ⟨trivial, trivial⟩ ⟨trivial, hqH, hdata, trivial⟩ hwidth
  intro out hout
  have hb := forkPackage_bound cost sampling randomBound cert.code pk g qH cert.data
    localTime queries (cert.budget pk) out hout
  dsimp only [SourceCertificate.targetBudget, Env.load, Ty.load, point₁] at hb ⊢
  omega

open scoped ENNReal

/-- Success probabilities now concern the actual compiled two-pass extractor.
The error allowance is derived from its original machine budget, including
adaptive sampling in either pass, rather than an assumed sampler count. -/
theorem SourceCertificate.bitCode_error
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    {cost : PrimitiveCosts} (sampling : Machine.SamplingCosts)
    (hsampling : ∀ n, n < 2^(sampling.uniform n))
    {randomBound localTime : Nat} {queries : Fin 3 → Nat} (g pk : H₁)
    {adv : _root_.Schnorr.ROM.Adversary (F := ZMod r) (M := M) g}
    (cert : SourceCertificate (G₂ := H₂) (K := K) cost randomBound localTime queries adv.main)
    (k qH bits : Nat) (hqH : qH < 2^bits) (hdata : NaturalRange.ValueBound bits cert.data)
    (hwidth : bits+cert.targetBudget sampling qH ≤ w) :
    let law := HeapMachine.scalarLaw r w (cert.bitCode H₁ H₂ encodeK encodeM k g qH) (pk : W₁.Point)
    MarkedProbability.GoodLe law
      (simulateQ MachineSampling.uniformNaturals (_root_.Schnorr.dlogReduction (ZMod r) H₁ g M adv qH g pk)) ∧
      MarkedProbability.bad law ≤
        cert.targetBudget sampling qH * (1/2 : ℝ≥0∞)^k := by
  have hfit : r ≤ 2^w := (Nat.le_mul_self r).trans hr
  have hcost := cert.bitCode_costed H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm
    sampling hsampling g pk k qH bits hqH hdata hwidth
  have he := hcost.map_eq (fun out => (HeapMachine.scalarValue r out.1.value, out.2))
    (fun out => (out.1.value, out.2)) (fun actual source h =>
      Prod.ext (HeapMachine.scalarValue_eq H₁ H₂ encodeK encodeM hfit h.1) h.2.1)
  have he := congrArg (simulateQ HeapMachine.fairBits) he
  simp only [simulateQ_map, PMF.monad_map_eq_map] at he
  have hp := HeapMachine.package_error H₁ H₂ (w := w) k cost sampling
    (forkPackage randomBound cert.code g qH cert.data) (pk, ()) (cert.targetBudget sampling qH)
    (by omega) hfit hsampling (fun out hout => by
      have hb := forkPackage_bound cost sampling randomBound cert.code pk g qH cert.data
        localTime queries (cert.budget pk) out hout
      dsimp only [SourceCertificate.targetBudget, Env.load, Ty.load, point₁] at hb ⊢
      omega)
  have hreduce : Run.value <$> (forkPackage randomBound cert.code g qH cert.data).run cost sampling (pk, ()) =
      _root_.Schnorr.dlogReduction (ZMod r) H₁ g M adv qH g pk := by
    rw [Machine.Package.run_eq, Functor.map_map]
    exact cert.reduction sampling g pk qH
  have hideal := congrArg (simulateQ MachineSampling.uniformNaturals) hreduce
  simp only [simulateQ_map, PMF.monad_map_eq_map] at hideal
  change MarkedProbability.GoodLe _ _ ∧ MarkedProbability.bad _ ≤ _
  have he : HeapMachine.scalarLaw r w (cert.bitCode H₁ H₂ encodeK encodeM k g qH) (pk : W₁.Point) = _ := he
  constructor
  · simpa only [he, hideal] using hp.1.map Run.value
  · simpa only [he, MarkedProbability.bad_map] using hp.2

end Signatures.Runtime.Schnorr
