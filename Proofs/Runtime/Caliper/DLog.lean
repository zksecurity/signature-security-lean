import Proofs.Runtime.Caliper.Within
import Signatures.Model.CoCDH
import Proofs.Model.AdvantageBound

/-! DLog hardness in a fixed Caliper word model. All sampled challenges must
be representable. The same layouts, port and code/time/total-memory limits are
fixed before the solver is chosen. No completed reduction certificate is an
assumption of this definition. -/
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

section Advantage
variable {w : Nat} {F G K : Type} [Field F] [SampleableType F]
    [AddCommGroup G] [Module F G] [AddCommGroup K] [Module F K]
    (port : Interactive.Port w unifSpec) (input : Layout w ((G × G) × (K × K)))
    (output : Layout w F) (generator : G) (keyGenerator : K)

noncomputable def dlogSuccessBound (words memory time : Nat) : ENNReal :=
  Model.advantageBound (Model.dlog11Advantage generator keyGenerator)
    (dlogWithin port input output generator keyGenerator words memory time)

theorem dlogSuccessBound_mono {words memory time words' memory' time' : Nat}
    (stored : words ≤ words') (space : memory ≤ memory') (elapsed : time ≤ time') :
    dlogSuccessBound port input output generator keyGenerator words memory time ≤
      dlogSuccessBound port input output generator keyGenerator words' memory' time' := by
  apply iSup_le
  intro solver
  apply iSup_le
  intro bounded
  exact Model.le_advantageBound _ _ solver (bounded.mono stored space elapsed)
end Advantage
end Signatures.Runtime.CaliperBackend
