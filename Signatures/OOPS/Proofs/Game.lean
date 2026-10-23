import Signatures.OOPS.Game
import Signatures.Model.Proofs.DirectAGM

namespace OOPS.Game

theorem agm_eq_source (curve : Model.PairingCurve) (securityParameter degree : Nat)
    {Topic : Type} [DecidableEq Topic]
    (adversary : AlgebraicAdversary curve securityParameter degree (Topic := Topic)) :
    agm curve securityParameter degree adversary =
      Model.DirectAGM.game (Gₜ := curve.TargetGroup securityParameter)
        (LazyAGM.terms degree) (LazyAGM.admissible degree)
        (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary :=
  Model.DirectAGM.eufCma_game_eq (LazyAGM.terms degree) (LazyAGM.admissible degree) _ _ adversary

end OOPS.Game
