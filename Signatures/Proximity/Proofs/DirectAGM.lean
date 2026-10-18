import Signatures.Proximity.Spec.DirectAGM
import Signatures.Model.Proofs.DirectAGM

open OracleComp OracleSpec

namespace Proximity.DirectAGM

variable {F G₁ G₂ Slot : Type} {dimension : Nat}
  [Field F] [SampleableType F] [DecidableEq Slot]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
  [AddCommGroup G₂] [Module F G₂]

/-- Collision probability is preserved exactly, including malformed and repeated outputs. -/
theorem collisionGame_eq (generator : G₁) (keyGenerator : G₂)
    (attack : Model.DirectAGM.Adversary F (Option (Fin dimension) × Slot)
      ((Fin dimension → F) × Slot) G₁ G₂) :
    collisionGame generator keyGenerator attack =
      LazyAGM.collisionGame keyGenerator (Model.DirectAGM.ProofView.adversary generator attack) := by
  classical
  simp only [collisionGame]
  conv_lhs =>
    arg 1
    arg 2
    intro secret
    rw [Model.DirectAGM.run_bind_eq LazyAGM.terms secret attack generator (secret • keyGenerator)
      (fun forgery => pure (decide (Collision forgery)))]
  simp only [Model.AlgebraicOracle.run_eq,
    bind_map_left, Model.RandomOracle.run, LazyAGM.collisionGame,
    LazyAGM.collisionExperiment, LazyAGM.Collision, Collision]
  congr! 8

end Proximity.DirectAGM
