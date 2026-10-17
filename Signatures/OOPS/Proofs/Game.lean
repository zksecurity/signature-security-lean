import Signatures.OOPS.Game
import Signatures.Model.Proofs.AlgebraicOracle

namespace OOPS.Game

theorem agm_eq_source (curve : Model.PairingCurve) (securityParameter degree : Nat)
    {Topic : Type} [DecidableEq Topic]
    (adversary : AlgebraicAdversary curve securityParameter degree (Topic := Topic)) :
    agm curve securityParameter degree adversary =
      LazyAGM.game (Gₜ := curve.TargetGroup securityParameter)
        (curve.generator securityParameter) (curve.keyGenerator securityParameter) degree adversary := by
  classical
  rw [LazyAGM.game_eq_of_decidableEq]
  convert Model.AlgebraicOracle.game_eq (Gₜ := curve.TargetGroup securityParameter)
    (LazyAGM.terms degree) (LazyAGM.admissible degree)
    (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary using 1
  simp only [agm, LazyAGM.admissible]
  congr!
  simp

end OOPS.Game
