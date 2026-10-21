import Signatures.Runtime.Caliper.SchnorrROMPassGrowth
import Signatures.Runtime.Caliper.SchnorrROMReplayRestart

/-! Derive second-pass admission from the first pass, without assuming a bound
on a completed controller. Restart preserves the private suffix in both tapes;
its retained prefix is included in the second pass's saved-cell reservation. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Pass.Replay
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G A : Type} (config : Signing.Enumerated.Configuration w M F G)

def ready (fuel : Nat) (value : Initialization.Input config) : Prop :=
  fuel + 1 ≤ config.capacityPred + 1 ∧ value.1.val.1.length + (4 * fuel + 3) ≤ config.sampler.capacity
theorem first_ready (fuel : Nat) (value : Initialization.Input config) (room : ready config fuel value) :
    Initialization.admitted config fuel value := ⟨room.1, by have := room.2; omega⟩
theorem ready_empty (fuel : Nat) (value : Initialization.Input config) (empty : value.1.val.1 = [])
    (tables : fuel + 1 ≤ config.capacityPred + 1) (tapes : 4 * fuel + 3 ≤ config.sampler.capacity) :
    ready config fuel value := by
  refine ⟨tables, ?_⟩
  simpa only [empty, List.length_nil, Nat.zero_add] using tapes

def request (first : Terminal.Output config) (slot : config.handler.sampler.tape.counter.Value)
    (replacement : config.handler.sampler.tape.scalar.Value) (room : first.2.val.2.1.length < config.sampler.capacity) :
    (ReplayRestart.input config.handler.sampler.tape).Value :=
  ⟨(slot.val, replacement.val, first.2.val.2), ⟨slot.property, replacement.property, first.2.property.2⟩, room⟩
def nextInput (first : Terminal.Output config) (slot : config.handler.sampler.tape.counter.Value)
    (replacement : config.handler.sampler.tape.scalar.Value) (room : first.2.val.2.1.length < config.sampler.capacity) :
    Initialization.Input config :=
  (⟨ReplayRestart.source (request config first slot replacement room).val,
      (ReplayRestart.implementation config.handler.sampler.tape).preserves _ (request config first slot replacement room).property⟩,
    ⟨first.2.val.1.1, first.2.property.1.1⟩)
theorem next_tapes (first : Terminal.Output config) (slot : config.handler.sampler.tape.counter.Value)
    (replacement : config.handler.sampler.tape.scalar.Value) (room : first.2.val.2.1.length < config.sampler.capacity) :
    (nextInput config first slot replacement room).1.val =
      ReplayRestart.tapes (Schnorr.RawTape.restart slot.val replacement.val ⟨first.2.val.2.1, first.2.val.2.2⟩) := rfl
theorem restart_lengths (first : Terminal.Output config) (slot : config.handler.sampler.tape.counter.Value)
    (replacement : config.handler.sampler.tape.scalar.Value) (room : first.2.val.2.1.length < config.sampler.capacity) :
    (nextInput config first slot replacement room).1.val.1.length ≤ first.2.val.2.1.length + 1 ∧
      (nextInput config first slot replacement room).1.val.2 = (nextInput config first slot replacement room).1.val.1 :=
  Schnorr.RawTape.restart_length slot.val replacement.val ⟨first.2.val.2.1, first.2.val.2.2⟩

variable [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (ops : Handler.Operations config) (caller : Pass.Caller config A)

theorem restart_room (fuel : Nat) (value : Initialization.Input config) (room : ready config fuel value)
    (first : Terminal.Output config) (reached : first ∈ support (Pass.source config caller ops fuel value)) :
    first.2.val.2.1.length < config.sampler.capacity := by
  have growth := Pass.tape_lengths config ops caller fuel value (first_ready config fuel value room) first reached
  have reserved := room.2
  omega

theorem second_ready (fuel : Nat) (value : Initialization.Input config) (room : ready config fuel value)
    (first : Terminal.Output config) (reached : first ∈ support (Pass.source config caller ops fuel value))
    (slot : config.handler.sampler.tape.counter.Value) (replacement : config.handler.sampler.tape.scalar.Value) :
    Initialization.admitted config fuel
      (nextInput config first slot replacement (restart_room config ops caller fuel value room first reached)) := by
  have growth := Pass.tape_lengths config ops caller fuel value (first_ready config fuel value room) first reached
  have reset := restart_lengths config first slot replacement (restart_room config ops caller fuel value room first reached)
  exact ⟨room.1, by have := room.2; omega⟩

theorem second_lengths (fuel : Nat) (value : Initialization.Input config) (room : ready config fuel value)
    (first : Terminal.Output config) (reached : first ∈ support (Pass.source config caller ops fuel value))
    (slot : config.handler.sampler.tape.counter.Value) (replacement : config.handler.sampler.tape.scalar.Value)
    (second : Terminal.Output config)
    (finished : second ∈ support (Pass.source config caller ops fuel
      (nextInput config first slot replacement (restart_room config ops caller fuel value room first reached)))) :
    second.2.val.2.1.length ≤ value.1.val.1.length + (4 * fuel + 3) ∧
      second.2.val.2.2.length ≤ value.1.val.1.length + (2 * fuel + 2) := by
  have firstGrowth := Pass.tape_lengths config ops caller fuel value (first_ready config fuel value room) first reached
  have reset := restart_lengths config first slot replacement (restart_room config ops caller fuel value room first reached)
  have secondGrowth := Pass.tape_lengths config ops caller fuel _
    (second_ready config ops caller fuel value room first reached slot replacement) second finished
  rw [reset.2] at secondGrowth
  exact ⟨by omega, by omega⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.Pass.Replay
