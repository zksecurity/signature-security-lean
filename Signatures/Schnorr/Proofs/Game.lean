import Signatures.Schnorr.Game
import Signatures.Schnorr.Proofs.Oracle
import Signatures.Model.EufCma

open OracleComp OracleSpec

namespace Schnorr.Game

theorem agm_eq_source (curve : Model.CyclicCurve) (securityParameter : Nat)
    {Message : Type} [DecidableEq Message]
    (adversary : AlgebraicAdversary curve securityParameter (Message := Message)) :
    agm curve securityParameter adversary = AGM.game (curve.generator securityParameter) adversary := by
  simp only [agm, Model.RandomOracle.run, AGM.run, AGM.oracle_eq_handler, AGM.game, AGM.experiment,
    bind_assoc, AGM.State.empty, AGM.State.signedMessages]
  congr! 8
  rename_i secret result
  rcases result with ⟨⟨output, basis⟩, state⟩
  cases h : output.value.groups () with
  | nil => simp
  | cons commitment rest =>
      cases rest <;> simp [Model.RandomOracle.hash, Model.RandomOracle.Request.hash]

theorem rom_eq_source (curve : Model.CyclicCurve) (securityParameter : Nat)
    {Message : Type} [DecidableEq Message]
    (adversary : ROM.Adversary (F := curve.Scalar securityParameter) (M := Message)
      (curve.generator securityParameter)) :
    rom curve securityParameter adversary.main = ROM.game (curve.generator securityParameter) adversary := by
  classical
  simp only [rom, ROM.game, Model.RandomOracle.run, ROM.run_eq,
    SignatureAlg.unforgeableExperiment, bind_map_left, ROM.verify_eq, bind_assoc, pure_bind]
  congr!

theorem nonzeroRom_eq_source (curve : Model.CyclicCurve) (securityParameter : Nat)
    {Message : Type} [DecidableEq Message]
    (adversary : NonzeroNonce.Adversary (F := curve.Scalar securityParameter) (M := Message)
      (curve.generator securityParameter)) :
    nonzeroRom curve securityParameter adversary.main =
      NonzeroNonce.game (curve.generator securityParameter) adversary := by
  classical
  simp only [nonzeroRom, NonzeroNonce.game, Model.RandomOracle.run, ROM.run_eq,
    SignatureAlg.unforgeableExperiment, bind_map_left, ROM.nonzero_verify_eq, bind_assoc, pure_bind]
  congr!

/-- The readable full-field game is the shared EUF-CMA experiment at `Schnorr.signature`. -/
theorem rom_eq_eufCma (curve : Model.CyclicCurve) (securityParameter : Nat)
    {Message : Type} [DecidableEq Message]
    (adversary : ROM.Adversary (F := curve.Scalar securityParameter) (M := Message)
      (curve.generator securityParameter)) :
    rom curve securityParameter adversary.main = Model.EufCma.game adversary := by
  classical
  rw [rom_eq_source]
  simp only [ROM.game, Model.EufCma.game, Model.RandomOracle.run]
  congr!

/-- The readable nonzero-nonce game is the shared EUF-CMA experiment at `NonzeroNonce.signature`. -/
theorem nonzeroRom_eq_eufCma (curve : Model.CyclicCurve) (securityParameter : Nat)
    {Message : Type} [DecidableEq Message]
    (adversary : NonzeroNonce.Adversary (F := curve.Scalar securityParameter) (M := Message)
      (curve.generator securityParameter)) :
    nonzeroRom curve securityParameter adversary.main = Model.EufCma.game adversary := by
  classical
  rw [nonzeroRom_eq_source]
  simp only [NonzeroNonce.game, Model.EufCma.game, Model.RandomOracle.run]
  congr!

end Schnorr.Game
