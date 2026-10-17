import Signatures.BLS.Game
import Signatures.Model.Proofs.AlgebraicOracle

namespace BLS.Game

theorem agm_eq_source (curve : Model.PairingCurve) (securityParameter : Nat)
    {Message : Type} [DecidableEq Message]
    (adversary : AlgebraicAdversary curve securityParameter (Message := Message)) :
    agm curve securityParameter adversary =
      LazyAGM.game (Gₜ := curve.TargetGroup securityParameter)
        (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary := by
  classical
  simpa [agm, LazyAGM.game, Model.AlgebraicOracle.hashMessage,
    LazyAGM.terms, Model.LazyAGM.evalTerms, Model.RandomOracle.hash] using
    Model.AlgebraicOracle.game_eq (Gₜ := curve.TargetGroup securityParameter)
      LazyAGM.terms (fun _ _ => True)
      (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary

end BLS.Game
