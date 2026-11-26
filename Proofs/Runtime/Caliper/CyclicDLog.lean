import Proofs.Runtime.Caliper.Within
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-! Ordinary cyclic-group DLog hardness in a fixed Caliper model. Word width,
layouts, sampling protocol and all resource limits are fixed before choosing
the solver. Every challenge in the experiment must fit the input layout. -/
namespace Signatures.Runtime.CaliperBackend
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F G : Type} [SMul F G]
    (port : Interactive.Port w unifSpec) (input : Layout w (G × G))
    (output : Layout w F) (generator : G)

def cyclicDLogWithin (words memory time : Nat) (solver : DiffieHellman.DLogAdversary F G) : Prop :=
  (∀ scalar : F, input.valid (generator, scalar • generator)) ∧
    Interactive.Within port input output words memory time (fun value => solver value.val.1 value.val.2)

variable {port input output generator} {words memory time words' memory' time' : Nat}
    {solver : DiffieHellman.DLogAdversary F G}
theorem cyclicDLogWithin.mono
    (bounded : cyclicDLogWithin port input output generator words memory time solver)
    (stored : words ≤ words') (space : memory ≤ memory') (elapsed : time ≤ time') :
    cyclicDLogWithin port input output generator words' memory' time' solver :=
  ⟨bounded.1, bounded.2.mono stored space elapsed⟩

end Signatures.Runtime.CaliperBackend
