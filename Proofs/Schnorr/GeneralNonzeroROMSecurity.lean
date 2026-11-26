import Signatures.Schnorr.GeneralNonzeroROMSecurityModel
import Proofs.Schnorr.Game

/-! Proofs for the short nonzero-nonce Schnorr ROM statement. The displayed game
is the original source game; the forking bound is in the success of the named
replaying solver, and a separate theorem places that solver in the fixed Caliper
budget. -/

open OracleComp OracleSpec

namespace Schnorr.NonzeroNonce

variable (curve : Model.CyclicCurve) [model : ROMSecurityModel curve]

theorem UnrestrictedAdversary.query_allowances (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    (∀ pk, IsQueryBoundP (adversary.source.main pk) (· matches .inl (.inl _)) queries.random) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main pk) (· matches .inr _) queries.sign) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main pk) (· matches .inl (.inr _)) queries.hash) := by
  refine ⟨fun pk => ?_, fun pk => ?_, fun pk => ?_⟩
  · refine IsQueryBoundP.of_imp ?_ (adversary.randomQueries pk)
    rintro (randomOrHash | message) h
    · cases randomOrHash <;> exact h
    · exact h
  · refine IsQueryBoundP.of_imp ?_ (adversary.signingQueries pk)
    rintro (randomOrHash | message) h <;> exact h
  · refine IsQueryBoundP.of_imp ?_ (adversary.hashQueries pk)
    rintro (randomOrHash | message) h
    · cases randomOrHash <;> exact h
    · exact h

theorem romEufCmaGame_eq (securityParameter : Nat) {queries : QueryAllowance}
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    romEufCmaGame curve securityParameter adversary =
      NonzeroNonce.game (curve.generator securityParameter) adversary.source :=
  Schnorr.Game.nonzeroRom_eq_source curve securityParameter adversary.source

theorem Proofs.rom_security
    (curve : Model.CyclicCurve) [model : ROMSecurityModel curve]
    (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    𝒟[romEufCmaGame curve securityParameter adversary] {true} ≤
      (queries.sign : ENNReal) * (queries.sign + queries.hash) * ((curve.order securityParameter - 1 : Nat) : ENNReal)⁻¹ +
      (queries.hash + 1 : ENNReal) * (curve.order securityParameter : ENNReal)⁻¹ +
      ((queries.hash + 1 : ENNReal) *
        𝒟[DiffieHellman.dlogExperiment (curve.generator securityParameter) (romReduction curve adversary)] {true}) ^
        (1 / 2 : ℝ) := by
  have fork := Schnorr.NonzeroNonce.LazyROM.security (curve.generator securityParameter) (curve.generates securityParameter)
    adversary.source queries.sign queries.hash (fun pk => ⟨adversary.signingQueries pk, adversary.hashQueries pk⟩)
  rw [← Signatures.Runtime.Schnorr.NonzeroListROM.NativeSolver.reduction_experiment (G₂ := curve.Group securityParameter)
    (K := model.Message securityParameter)] at fork
  rw [romEufCmaGame_eq]
  exact Model.forking_inverse queries.hash (MeasureTheory.measure_ne_top _ _)
    (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)) fork

theorem Proofs.rom_reduction_within
    (curve : Model.CyclicCurve) [model : ROMSecurityModel curve]
    (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    ROMDLogSolverWithin curve securityParameter queries (romReductionTime curve securityParameter queries)
      (romReduction curve adversary) :=
  CaliperROM.nonzero_reduction_within (model.parameters securityParameter queries) adversary
    (model.sampling securityParameter queries) (model.nonzero securityParameter queries)

end Schnorr.NonzeroNonce
