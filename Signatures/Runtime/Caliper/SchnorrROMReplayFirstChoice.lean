import Signatures.Runtime.Caliper.SchnorrROMReplayChallengeBounds

/-! The first selector's Boolean tag is already the stored tag for a sum of
retained slot/result frames. This identical-byte view lets the controller
branch before sampling, so a rejected first pass need not draw a challenge. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFirst
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} (config : Signing.Enumerated.Configuration w M F G)

def choice := (ReplayChallenge.input config).sum (ReplayChallenge.input config) (width_pos config.sampler.wordFits)
  (ReplaySecond.combinedFits config (by change 1 + max (1 + _) (1 + _) ≤ _; omega))
def slot (value : (Selection.result config).Value) : config.handler.sampler.tape.counter.Value :=
  ⟨value.val.2, by
    have bounded := value.property.2
    have room := config.countFits
    change value.val.2 < config.capacityPred + 2 at bounded
    change value.val.2 < 2 ^ w
    omega⟩

def choose (value : (Selection.result config).Value × Terminal.Output config) : ReplayChallenge.Input config ⊕ ReplayChallenge.Input config :=
  if value.1.val.1 = true then .inr (slot config value.1, value.2) else .inl (slot config value.1, value.2)

theorem choose_bytes (value : (Selection.result config).Value × Terminal.Output config) :
    (choice config).encoding.encode (choose config value) = (output config).encoding.encode value := by
  rcases value with ⟨⟨⟨flag, index⟩, valid⟩, first⟩
  cases flag
  all_goals
    simp only [choose, Bool.false_eq_true, ↓reduceIte]
    change _ :: (_ ++ List.replicate (_ - _) 0) = _
    rw [Nat.max_self, Nat.sub_self, List.replicate_zero, List.append_nil]
    rfl

theorem choose_first (value : (Selection.result config).Value × Terminal.Output config) :
    (Sum.elim id id (choose config value)).2 = value.2 := by
  unfold choose
  split <;> rfl

variable [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (caller : Pass.Caller config A) (ops : Handler.Operations config) (qH : Nat) (indexFits : qH + 1 < 2 ^ w)

def choiceSource (fuel : Nat) (value : {value : Pass.Initialization.Input config // Pass.Replay.ready config fuel value}) :=
  choose config <$> source config caller ops qH indexFits fuel value

theorem choice_refines (fuel : Nat) : Interactive.Refines (Fresh.port config.handler.sampler.tape) .unit
    (input config fuel) (choice config) (choiceSource config caller ops qH indexFits fuel) (program config caller ops qH indexFits fuel) := by
  unfold choiceSource
  exact (refines config caller ops qH indexFits fuel).viewOutput (choice config) (choose config) (choose_bytes config)

theorem choice_ready (fuel : Nat) (value : {value : Pass.Initialization.Input config // Pass.Replay.ready config fuel value})
    (answer) (reached : answer ∈ support (choiceSource config caller ops qH indexFits fuel value))
    (replacement : config.handler.sampler.tape.scalar.Value) :
    ReplaySecond.ready config fuel (((Sum.elim id id answer).1, replacement), (Sum.elim id id answer).2) := by
  simp only [choiceSource, support_map, Set.mem_image] at reached
  obtain ⟨selected, reached, rfl⟩ := reached
  rw [choose_first]
  exact next_ready config caller ops qH indexFits fuel value selected reached _ replacement

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFirst
