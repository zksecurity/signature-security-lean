import Signatures.Schnorr.Game
import Proofs.Schnorr.Oracle
import Signatures.Model.EufCma

open OracleComp OracleSpec

namespace Schnorr.Game

theorem keygen_eq (curve : Model.CyclicCurve) (securityParameter : Nat) {Message : Type} [DecidableEq Message] :
    (signature (curve.Scalar securityParameter) (curve.Group securityParameter) (curve.generator securityParameter)
      Message).keygen = (do
        let secret ← Model.RandomOracle.sample (curve.Scalar securityParameter)
        return (secret • curve.generator securityParameter, secret)) := by
  simp [signature, FiatShamir, DiffieHellman.dlogGenerable, Model.RandomOracle.sample, monad_norm,
    OracleComp.liftM_eq_liftM_liftM]

/-- The algebraic experiment, written out. -/
theorem agm_eq (curve : Model.CyclicCurve) (securityParameter : Nat)
    {Message : Type} [DecidableEq Message]
    (adversary : AlgebraicAdversary curve securityParameter (Message := Message)) :
    agm curve securityParameter adversary = Model.RandomOracle.run (do
      let secret ← Model.RandomOracle.sample (curve.Scalar securityParameter)
      match ← AGM.run (curve.generator securityParameter) secret adversary with
      | some forgery =>
          let challenge ← Model.RandomOracle.hash (forgery.message, forgery.commitment)
          return !forgery.state.malformed && decide (
            forgery.message ∉ forgery.state.signedMessages ∧
            forgery.response • curve.generator securityParameter =
              forgery.commitment + challenge • (secret • curve.generator securityParameter))
      | none => return false) := by
  classical
  simp only [agm, Model.EufCma.game, Model.EufCma.Attacker.run, keygen_eq, map_eq_bind_pure_comp,
    bind_assoc, pure_bind, Function.comp_apply, AGM.runWith_sign]
  congr 1
  refine bind_congr fun secret => bind_congr fun result => ?_
  cases result with
  | none => rfl
  | some forgery =>
    simp only [Option.map_some, ROM.verify_eq, bind_assoc, pure_bind]
    refine bind_congr fun challenge => ?_
    simp [Bool.and_assoc]

theorem agm_eq_source (curve : Model.CyclicCurve) (securityParameter : Nat)
    {Message : Type} [DecidableEq Message]
    (adversary : AlgebraicAdversary curve securityParameter (Message := Message)) :
    agm curve securityParameter adversary = AGM.game (curve.generator securityParameter) adversary := by
  rw [agm_eq]
  simp only [Model.RandomOracle.run, AGM.run, ← AGM.oracle_eq_oracleWith, AGM.oracle_eq_handler, AGM.game,
    AGM.experiment, bind_assoc, AGM.State.empty, AGM.State.signedMessages, AGM.runWith]
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
  rw [rom, Model.EufCma.game_eq_unforgeableExperiment]
  simp only [ROM.game, Model.RandomOracle.run]
  congr!

theorem nonzeroRom_eq_source (curve : Model.CyclicCurve) (securityParameter : Nat)
    {Message : Type} [DecidableEq Message]
    (adversary : NonzeroNonce.Adversary (F := curve.Scalar securityParameter) (M := Message)
      (curve.generator securityParameter)) :
    nonzeroRom curve securityParameter adversary.main =
      NonzeroNonce.game (curve.generator securityParameter) adversary := by
  classical
  rw [nonzeroRom, Model.EufCma.game_eq_unforgeableExperiment]
  simp only [NonzeroNonce.game, Model.RandomOracle.run]
  congr!

/-- The readable full-field game is the shared EUF-CMA experiment at `Schnorr.signature`. -/
theorem rom_eq_eufCma (curve : Model.CyclicCurve) (securityParameter : Nat)
    {Message : Type} [DecidableEq Message]
    (adversary : ROM.Adversary (F := curve.Scalar securityParameter) (M := Message)
      (curve.generator securityParameter)) :
    rom curve securityParameter adversary.main =
      Model.EufCma.game (Schnorr.signature (curve.Scalar securityParameter) (curve.Group securityParameter)
        (curve.generator securityParameter) Message) adversary := by
  rfl

/-- The readable nonzero-nonce game is the shared EUF-CMA experiment at `NonzeroNonce.signature`. -/
theorem nonzeroRom_eq_eufCma (curve : Model.CyclicCurve) (securityParameter : Nat)
    {Message : Type} [DecidableEq Message]
    (adversary : NonzeroNonce.Adversary (F := curve.Scalar securityParameter) (M := Message)
      (curve.generator securityParameter)) :
    nonzeroRom curve securityParameter adversary.main =
      Model.EufCma.game (NonzeroNonce.signature (F := curve.Scalar securityParameter) (M := Message)
        (curve.generator securityParameter)) adversary := by
  rfl

end Schnorr.Game
