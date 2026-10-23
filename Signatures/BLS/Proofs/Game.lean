import Signatures.BLS.Game
import Signatures.Model.Proofs.DirectAGM

namespace BLS.Game

theorem agm_eq_source (curve : Model.PairingCurve) (securityParameter : Nat)
    {Message : Type} [DecidableEq Message]
    (adversary : AlgebraicAdversary curve securityParameter (Message := Message)) :
    agm curve securityParameter adversary =
      Model.DirectAGM.game (Gₜ := curve.TargetGroup securityParameter)
        LazyAGM.terms (fun _ _ => True)
        (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary := by
  rw [agm, signature_eq_scheme]
  exact Model.DirectAGM.eufCma_game_eq LazyAGM.terms (fun _ _ => True) _ _ adversary

end BLS.Game
