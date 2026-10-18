import Signatures.Proximity.Spec.LazyAGM
import Signatures.Model.DirectAGM

open OracleComp OracleSpec

namespace Proximity.DirectAGM

variable {F G₁ G₂ Slot : Type} {dimension : Nat}
  [Field F] [SampleableType F] [DecidableEq Slot]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
  [AddCommGroup G₂] [Module F G₂]

/-- The same fresh-collision event, using the actual shared-library explanation. -/
def Collision (forgery : Model.AlgebraicOracle.Result F ((Fin dimension → F) × Slot) G₁) : Prop :=
  forgery.message ∉ forgery.signedMessages ∧
    forgery.message.1 = fun k => (forgery.signedMessages.mapIdx fun n (vector, _) =>
      Model.LazyAGM.tokenCoeff forgery.signingCoefficients n * vector k).sum

noncomputable def collisionGame (generator : G₁) (keyGenerator : G₂)
    (attack : Model.DirectAGM.Adversary F (Option (Fin dimension) × Slot)
      ((Fin dimension → F) × Slot) G₁ G₂) : ProbComp Bool := by
  classical
  exact Model.RandomOracle.run do
    let secret ← Model.RandomOracle.sample F
    let forgery ← Model.DirectAGM.run LazyAGM.terms secret attack generator (secret • keyGenerator)
    return decide (Collision forgery.toResult)

end Proximity.DirectAGM
