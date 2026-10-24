import Signatures.Proximity.Game
import Proofs.Proximity.DirectAGM

open OracleComp OracleSpec

namespace Proximity.Game

theorem agm_eq_source (curve : Model.PairingCurve) (securityParameter dimension : Nat)
    {Slot : Type} [DecidableEq Slot]
    (adversary : AlgebraicAdversary curve securityParameter dimension (Slot := Slot)) :
    agm curve securityParameter dimension adversary =
      Model.DirectAGM.game (Gₜ := curve.TargetGroup securityParameter)
        LazyAGM.terms (fun _ _ => True)
        (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary :=
  Model.DirectAGM.eufCma_game_eq LazyAGM.terms (fun _ _ => True) _ _ adversary

theorem collision_eq_source (curve : Model.PairingCurve) (securityParameter dimension : Nat)
    {Slot : Type} [DecidableEq Slot]
    (adversary : AlgebraicAdversary curve securityParameter dimension (Slot := Slot)) :
    collision curve securityParameter dimension adversary =
      LazyAGM.collisionGame (curve.keyGenerator securityParameter)
        (Model.DirectAGM.ProofView.adversary (curve.generator securityParameter) adversary) := by
  classical
  rw [← DirectAGM.collisionGame_eq]
  simp only [collision, DirectAGM.collisionGame, DirectAGM.Collision]
  congr! 8
  exact decide_eq_decide.mpr Iff.rfl

end Proximity.Game
