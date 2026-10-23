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
  classical
  have sign : ∀ (secret : curve.Scalar securityParameter) (message : Message),
      Model.AlgebraicOracle.sign (G₁ := curve.SignatureGroup securityParameter) LazyAGM.terms secret message =
        (signature curve securityParameter (Message := Message)).sign (secret • curve.keyGenerator securityParameter) secret message := by
    intro secret message
    simp [Model.AlgebraicOracle.sign, Model.AlgebraicOracle.hashMessage, LazyAGM.terms, Model.LazyAGM.evalTerms,
      signature, Model.RandomOracle.hash]
  simp only [agm, Model.EufCma.game, Model.EufCma.Attacker.run, Model.DirectAGM.attacker, Model.DirectAGM.game,
    Model.DirectAGM.run, sign, signature, Model.AlgebraicOracle.hashMessage, LazyAGM.terms, Model.LazyAGM.evalTerms,
    Model.RandomOracle.hash, map_eq_bind_pure_comp, bind_assoc, pure_bind, one_smul, add_zero]
  congr! 7
  · simp [sign, signature, Model.RandomOracle.hash]
  · simp only [Function.comp_apply, pure_bind]
    refine bind_congr fun hash => ?_
    congr 1
    simp [Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]

end BLS.Game
