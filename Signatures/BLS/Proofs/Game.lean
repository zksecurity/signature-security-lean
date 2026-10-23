import Signatures.BLS.Game
import Signatures.Model.Proofs.DirectAGM

namespace BLS.Game

/-- BLS is the pairing-family scheme with one hash term per message. -/
theorem signature_eq_scheme (curve : Model.PairingCurve) (securityParameter : Nat)
    {Message : Type} [DecidableEq Message] :
    signature curve securityParameter (Message := Message) =
      Model.DirectAGM.scheme (G₁ := curve.SignatureGroup securityParameter) (Gₜ := curve.TargetGroup securityParameter)
        LazyAGM.terms (curve.keyGenerator securityParameter) := by
  unfold signature Model.DirectAGM.scheme
  congr 1
  · funext _ secret message
    simp [Model.AlgebraicOracle.sign, Model.AlgebraicOracle.hashMessage, LazyAGM.terms, Model.LazyAGM.evalTerms,
      Model.RandomOracle.hash]
  · funext publicKey message point
    simp [Model.AlgebraicOracle.hashMessage, LazyAGM.terms, Model.LazyAGM.evalTerms, Model.RandomOracle.hash]


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
