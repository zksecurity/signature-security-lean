import Signatures.Schnorr.GeneralNonzeroROMSecurityModel
import Signatures.Schnorr.Proofs.GeneralNonzeroROM
import Signatures.Schnorr.Proofs.Game

/-! Proofs for the short general nonzero-nonce Schnorr ROM statement. The displayed game is
the original source game, and its DLog term ranges over the same fixed backend
that contains the derived complete replaying solver. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr.ListROM

namespace Schnorr.NonzeroNonce

universe v w x

variable (curve : Model.CyclicCurve) [model : ROMSecurityModel.{v, w, x} curve]

theorem UnrestrictedAdversary.query_allowances (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    (∀ pk, IsQueryBoundP (adversary.source.main pk) (· matches .inl (.inl _)) queries.random) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main pk) (· matches .inr _) queries.sign) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main pk) (· matches .inl (.inr _)) queries.hash) := by
  refine ⟨fun pk => ?_, fun pk => ?_, fun pk => ?_⟩
  · refine IsQueryBoundP.of_imp ?_ ((adversary.randomQueries pk).mono
      (le_of_eq (congrArg QueryAllowance.random (model.queries_eq securityParameter queries))))
    rintro (randomOrHash | message) h
    · cases randomOrHash <;> exact h
    · exact h
  · refine IsQueryBoundP.of_imp ?_ ((adversary.signingQueries pk).mono
      (le_of_eq (congrArg QueryAllowance.sign (model.queries_eq securityParameter queries))))
    rintro (randomOrHash | message) h <;> exact h
  · refine IsQueryBoundP.of_imp ?_ ((adversary.hashQueries pk).mono
      (le_of_eq (congrArg QueryAllowance.hash (model.queries_eq securityParameter queries))))
    rintro (randomOrHash | message) h
    · cases randomOrHash <;> exact h
    · exact h

theorem romEufCmaGame_eq (securityParameter : Nat) {queries : QueryAllowance}
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    romEufCmaGame curve securityParameter adversary =
      NonzeroNonce.game (model.parameters securityParameter queries).generator adversary.source := by
  simpa only [romEufCmaGame, NonzeroNonce.game, SignatureAlg.unforgeableExperiment,
    ROMSecurityModel.generator_eq] using
    (Schnorr.Game.nonzeroRom_eq_source curve securityParameter ⟨adversary.source.main⟩)

theorem romDLogSuccessBound_eq (securityParameter : Nat) (queries : QueryAllowance) (time : Nat) :
    romDLogSuccessBound curve securityParameter queries time =
      (model.parameters securityParameter queries).dlogBound time := rfl

theorem Proofs.rom_security
    (curve : Model.CyclicCurve) [model : ROMSecurityModel curve]
    (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    𝒟[romEufCmaGame curve securityParameter adversary] {true} ≤
      (queries.sign : ENNReal) * (queries.sign + queries.hash) * ((curve.order securityParameter - 1 : Nat) : ENNReal)⁻¹ +
      (queries.hash + 1 : ENNReal) * (curve.order securityParameter : ENNReal)⁻¹ +
      ((queries.hash + 1 : ENNReal) *
        romDLogSuccessBound curve securityParameter queries (romReductionTime curve securityParameter queries)) ^ (1 / 2 : ℝ) := by
  rw [romEufCmaGame_eq, romDLogSuccessBound_eq]
  have h := GeneralROM.security (model.parameters securityParameter queries) adversary
  have hs := congrArg QueryAllowance.sign (model.queries_eq securityParameter queries)
  have hh := congrArg QueryAllowance.hash (model.queries_eq securityParameter queries)
  rw [hs, hh] at h
  exact h

theorem romDLogSuccessBound_mono (securityParameter : Nat) (queries : QueryAllowance) :
    Monotone (romDLogSuccessBound curve securityParameter queries) := by
  intro time largerTime ht
  let resources := model.parameters securityParameter queries
  refine iSup_le fun solver => iSup_le fun fits => ?_
  have largerFits : NativeSolver.dlogWithin
      resources.rep resources.backend resources.descriptionSizes resources.factor resources.description
      resources.generator resources.inputWidth resources.solverCode largerTime solver :=
    ⟨fits.1, Within.mono resources.backend resources.descriptionSizes resources.factor resources.description fits.2 le_rfl ht⟩
  exact le_iSup_of_le solver (le_iSup_of_le largerFits le_rfl)

end Schnorr.NonzeroNonce
