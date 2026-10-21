import Signatures.Schnorr.GeneralNonzeroROMSecurityModel
import Signatures.Schnorr.Proofs.Game

/-! Proofs for the short nonzero-nonce Schnorr ROM statement. The displayed game
is the original source game, and its DLog term ranges over the fixed Caliper
class that contains the constructed complete replaying solver. -/

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
  exact CaliperROM.nonzero_security (model.parameters securityParameter queries) adversary
    (model.sampling securityParameter queries) (model.nonzero securityParameter queries) (curve.generates securityParameter)

theorem romDLogSuccessBound_mono (securityParameter : Nat) (queries : QueryAllowance) :
    Monotone (romDLogSuccessBound curve securityParameter queries) :=
  fun _ _ elapsed => Signatures.Runtime.CaliperBackend.cyclicDLogSuccessBound_mono
    (Signatures.Runtime.CaliperBackend.SchnorrROMTape.Fresh.port (model.parameters securityParameter queries).config.handler.sampler.tape)
    (Signatures.Runtime.CaliperBackend.SchnorrROM.Pass.Initialization.points (model.parameters securityParameter queries).config)
    (model.parameters securityParameter queries).config.handler.sampler.tape.scalar
    (curve.generator securityParameter) le_rfl le_rfl elapsed

end Schnorr.NonzeroNonce
