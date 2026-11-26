import Proofs.Runtime.Caliper.Within
import Signatures.Model.CoCDH

/-! The co-CDH solver class in a fixed Caliper model. The input stores the public key
and the three signature-group challenge points. The key-group generator is a
fixed parameter of the experiment. Every sampled scalar and challenge point
must fit; layouts, sampling port and resource limits are fixed before the solver. -/
namespace Signatures.Runtime.CaliperBackend
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F G K : Type} [SMul F G] [SMul F K]
    (port : Interactive.Port w unifSpec) (input : Layout w (K × (G × (G × G))))
    (output : Layout w G) (generator : G) (keyGenerator : K)

def coCDHWithin (words memory time : Nat) (solver : BLS.CoCDH.CoCDHAdversary F G K) : Prop :=
  (∀ (scalar : F) (point : G), input.valid (scalar • keyGenerator, generator, scalar • generator, point)) ∧
  Interactive.Within port input output words memory time
    (fun value => solver value.val.2.1 keyGenerator value.val.2.2.1 value.val.1 value.val.2.2.2)

variable {port input output generator keyGenerator} {words memory time words' memory' time' : Nat}
    {solver : BLS.CoCDH.CoCDHAdversary F G K}
theorem coCDHWithin.mono (bounded : coCDHWithin port input output generator keyGenerator words memory time solver)
    (stored : words ≤ words') (space : memory ≤ memory') (elapsed : time ≤ time') :
    coCDHWithin port input output generator keyGenerator words' memory' time' solver :=
  ⟨bounded.1, bounded.2.mono stored space elapsed⟩

end Signatures.Runtime.CaliperBackend
