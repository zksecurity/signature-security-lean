import Proofs.Runtime.Caliper.Within
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import Proofs.Model.AdvantageBound

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

section Advantage
variable {w : Nat} {F G : Type} [Field F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq F]
    (port : Interactive.Port w unifSpec) (input : Layout w (G × G))
    (output : Layout w F) (generator : G)

noncomputable def cyclicDLogSuccessBound (words memory time : Nat) : ENNReal :=
  Model.advantageBound (fun solver => 𝒟[DiffieHellman.dlogExperiment generator solver] {true})
    (cyclicDLogWithin port input output generator words memory time)

theorem cyclicDLogSuccessBound_mono {words memory time words' memory' time' : Nat}
    (stored : words ≤ words') (space : memory ≤ memory') (elapsed : time ≤ time') :
    cyclicDLogSuccessBound port input output generator words memory time ≤
      cyclicDLogSuccessBound port input output generator words' memory' time' := by
  apply iSup_le
  intro solver
  apply iSup_le
  intro bounded
  exact Model.le_advantageBound (fun candidate => 𝒟[DiffieHellman.dlogExperiment generator candidate] {true})
    _ solver (bounded.mono stored space elapsed)
end Advantage
end Signatures.Runtime.CaliperBackend
