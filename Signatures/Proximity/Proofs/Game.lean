import Signatures.Proximity.Game
import Signatures.Model.Proofs.AlgebraicOracle

open OracleComp OracleSpec

namespace Proximity.Game

theorem agm_eq_source (curve : Model.PairingCurve) (securityParameter dimension : Nat)
    {Slot : Type} [DecidableEq Slot]
    (adversary : AlgebraicAdversary curve securityParameter dimension (Slot := Slot)) :
    agm curve securityParameter dimension adversary =
      LazyAGM.game (Gₜ := curve.TargetGroup securityParameter)
        (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary := by
  classical
  simpa only [agm, LazyAGM.game, true_and] using
    Model.AlgebraicOracle.game_eq (Gₜ := curve.TargetGroup securityParameter)
      LazyAGM.terms (fun _ _ => True)
      (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary

theorem collision_eq_source (curve : Model.PairingCurve) (securityParameter dimension : Nat)
    {Slot : Type} [DecidableEq Slot]
    (adversary : AlgebraicAdversary curve securityParameter dimension (Slot := Slot)) :
    collision curve securityParameter dimension adversary =
      LazyAGM.collisionGame (curve.keyGenerator securityParameter) adversary := by
  classical
  simp only [collision, Model.AlgebraicOracle.run_eq, bind_map_left,
    Model.RandomOracle.run, LazyAGM.collisionGame, LazyAGM.collisionExperiment, LazyAGM.Collision]
  congr! 8
  exact decide_eq_decide.mpr Iff.rfl

end Proximity.Game
