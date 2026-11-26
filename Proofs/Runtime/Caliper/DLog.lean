import Proofs.Runtime.Caliper.Within
import Signatures.Model.CoCDH

/-! The `(1,1)`-DLog solver class in a fixed Caliper word model: actual code on
a port and layouts fixed before the solver is chosen, within code, time and
total-memory limits, with every sampled challenge representable. -/
namespace Signatures.Runtime.CaliperBackend
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F G K : Type} [SMul F G] [SMul F K]
    (port : Interactive.Port w unifSpec) (input : Layout w ((G × G) × (K × K)))
    (output : Layout w F) (generator : G) (keyGenerator : K)

def dlogWithin (words memory time : Nat) (solver : AlgebraicGroupModel.DLog11Adversary F G K) : Prop :=
  (∀ scalar : F, input.valid ((generator, scalar • generator), (keyGenerator, scalar • keyGenerator))) ∧
  Interactive.Within port input output words memory time
    (fun value => solver value.val.1.1 value.val.1.2 value.val.2.1 value.val.2.2)

variable {port input output generator keyGenerator} {words memory time words' memory' time' : Nat}
    {solver : AlgebraicGroupModel.DLog11Adversary F G K}
theorem dlogWithin.mono (bounded : dlogWithin port input output generator keyGenerator words memory time solver)
    (stored : words ≤ words') (space : memory ≤ memory') (elapsed : time ≤ time') :
    dlogWithin port input output generator keyGenerator words' memory' time' solver :=
  ⟨bounded.1, bounded.2.mono stored space elapsed⟩

end Signatures.Runtime.CaliperBackend
