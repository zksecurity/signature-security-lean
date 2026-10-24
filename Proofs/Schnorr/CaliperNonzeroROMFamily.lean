import Signatures.Schnorr.CaliperROMFamilyResources
import Proofs.Schnorr.GeneralNonzeroROMSecurity
import Proofs.Model.ForkingNegligible
import Proofs.Model.NonzeroFieldGrowth

/-! Negligible nonzero-nonce Schnorr forgery from the constructed polynomial
Caliper reduction family. The components and their polynomial resources are
the full-field route's; only the signing branch's source law differs. -/
namespace Schnorr.CaliperROM.Family
open OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend
variable {F G M : Nat → Type} [∀ n, Field (F n)] [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
    [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)]
    {queries : Nat → QueryAllowance} {generator : ∀ n, G n}
    (parameters : ∀ n, Parameters (F n) (G n) (M n) (queries n) (generator n))
    [inst : ∀ n, SampleableType (F n)] [∀ n, SampleableType (F n)ˣ] [∀ n, SampleableType (G n)]

include inst in
theorem nonzero_reduction_nonuniform (resources : PolynomialResources parameters)
    (adversary : ∀ n, NonzeroAdversary (parameters n))
    (sampled : ∀ n, inst n = SchnorrROMTape.PrivateSampler.Enumerated.sampleable (parameters n).config.sampler)
    (nonzero : ∀ n, (parameters n).Nonzero) :
    cyclicDLogNonuniformWithin (fun n => SchnorrROMTape.Fresh.port (parameters n).config.handler.sampler.tape)
      (fun n => SchnorrROM.Pass.Initialization.points (parameters n).config)
      (fun n => (parameters n).config.handler.sampler.tape.scalar) generator
      (fun n => Schnorr.NonzeroListROM.NativeSolver.reduction (G₂ := G n) (K := M n) (adversary n).source.main (queries n).hash) :=
  cyclicDLogNonuniformWithin.of_pointwise _ _ _ _ _
    (fun n => (parameters n).solverCode) (fun n => (parameters n).solverMemory) (fun n => (parameters n).solverTime)
    resources.wordBits resources.solverCode resources.solverMemory resources.solverTime
    (fun n => nonzero_reduction_within (parameters n) (adversary n) (sampled n) (nonzero n))

end Schnorr.CaliperROM.Family

namespace Schnorr.CaliperROM.Family.Proofs
open OracleComp OracleSpec Signatures.Runtime

theorem nonzero_security
    (curve : Model.CyclicCurve) [model : NonzeroNonce.ROMSecurityModel curve]
    (queries : Nat → QueryAllowance)
    (adversary : ∀ n, Schnorr.NonzeroNonce.UnrestrictedAdversary curve n (queries n))
    (resources : PolynomialResources (fun n => model.parameters n (queries n)))
    (hardness : dlogHardness (fun n => model.parameters n (queries n)))
    (fieldGrowth : negligible (fun n => (curve.order n : ENNReal)⁻¹)) :
    negligible (fun n => 𝒟[Schnorr.NonzeroNonce.romEufCmaGame curve n (adversary n)] {true}) := by
  have fits := nonzero_reduction_nonuniform (fun n => model.parameters n (queries n)) resources adversary
    (fun n => model.sampling n (queries n)) (fun n => model.nonzero n (queries n))
  have solverSmall := hardness _ fits
  have signingLossSmall : negligible (fun n =>
      ((queries n).sign : ENNReal) * ((queries n).sign + (queries n).hash) * ((curve.order n - 1 : Nat) : ENNReal)⁻¹) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Model.CyclicCurve.order] using
      (resources.signingQueries.mul (resources.signingQueries.add resources.hashQueries)).negligible_mul
        (Model.negligible_inv_card_sub_one (F := fun n => curve.Scalar n) fieldGrowth)
  apply Model.negligible_of_forking_bound
    (fun n => MeasureTheory.measure_ne_top _ _)
    (fun n => ENNReal.inv_ne_top.mpr (by unfold Model.CyclicCurve.order; positivity)) resources.hashQueries
    signingLossSmall fieldGrowth solverSmall
  intro n
  rw [Schnorr.NonzeroNonce.romEufCmaGame_eq, Schnorr.NonzeroListROM.NativeSolver.reduction_experiment (G₂ := curve.Group n)
    (K := model.Message n) (curve.generator n) (adversary n).source (queries n).hash]
  exact Schnorr.NonzeroNonce.LazyROM.security (curve.generator n) (curve.generates n) (adversary n).source (queries n).sign (queries n).hash
    (fun pk => ⟨(adversary n).signingQueries pk, (adversary n).hashQueries pk⟩)

end Schnorr.CaliperROM.Family.Proofs
