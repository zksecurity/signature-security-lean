import Signatures.Runtime.Caliper.SchnorrROMReplayForkResultBounds

/-! The rejection guard's Boolean is an actual sum tag: fresh requests select
the second-pass branch; repeated challenges select failure. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

def guardChoice := (ReplaySecond.rawInput config).sum (ReplaySecond.rawInput config) (width_pos config.sampler.wordFits)
  (ReplaySecond.combinedFits config (by change 1 + max ((1 + 1) + _) ((1 + 1) + _) ≤ _; omega))
def chooseGuard (value : config.handler.sampler.tape.boolean.Value × ReplaySecond.Request config) :
    ReplaySecond.Request config ⊕ ReplaySecond.Request config :=
  if value.1.val = true then .inr value.2 else .inl value.2
theorem chooseGuard_bytes (value : config.handler.sampler.tape.boolean.Value × ReplaySecond.Request config) :
    (guardChoice config).encoding.encode (chooseGuard config value) = (ReplayChallenge.Guard.output config).encoding.encode value := by
  rcases value with ⟨⟨flag, valid⟩, request⟩
  cases flag
  all_goals
    simp only [chooseGuard, Bool.false_eq_true, ↓reduceIte]
    change _ :: (_ ++ List.replicate (_ - _) 0) = _
    rw [Nat.max_self, Nat.sub_self, List.replicate_zero, List.append_nil]
    rfl

def savedReady (fuel : Nat) (value : ReplayChallenge.Input config) : Prop :=
  fuel + 1 ≤ config.capacityPred + 1 ∧ value.2.2.val.2.1.length + (2 * fuel + 2) ≤ config.sampler.capacity

variable [DecidableEq F]
def guardChoiceSource (value : ReplayChallenge.Input config) : ProbComp (ReplaySecond.Request config ⊕ ReplaySecond.Request config) :=
  chooseGuard config <$> ReplayChallenge.Checked.source config value

theorem guardChoice_refines : Interactive.Refines (Fresh.port config.handler.sampler.tape) .unit
    (ReplayChallenge.input config) (guardChoice config) (guardChoiceSource config) (ReplayChallenge.Checked.program config) := by
  unfold guardChoiceSource
  exact (ReplayChallenge.Checked.refines config).viewOutput (guardChoice config) (chooseGuard config) (chooseGuard_bytes config)

theorem guardChoice_ready (fuel : Nat) (value : ReplayChallenge.Input config) (room : savedReady config fuel value)
    (answer) (reached : answer ∈ support (guardChoiceSource config value)) :
    Sum.elim (ReplaySecond.ready config fuel) (ReplaySecond.ready config fuel) answer := by
  simp only [guardChoiceSource, support_map, Set.mem_image] at reached
  obtain ⟨tested, reached, rfl⟩ := reached
  have kept := ReplayChallenge.Checked.retains_first config value tested reached
  have ready : ReplaySecond.ready config fuel tested.2 := by
    unfold ReplaySecond.ready
    rw [kept.1]
    exact room
  unfold chooseGuard
  split <;> exact ready

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
