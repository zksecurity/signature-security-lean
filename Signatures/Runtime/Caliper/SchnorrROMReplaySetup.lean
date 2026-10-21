import Signatures.Runtime.Caliper.SchnorrROMReplayForkSource

/-! Construct the fork's empty tapes from runtime generator/public-key inputs.
Both empty encodings, including their reserved padding, are written by code. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Setup
open Caliper BoundedSource SchnorrROMTape ByteRoute
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

def input := (Pass.Initialization.points config).representation
def emptyTapes : (Pass.Initialization.tapes config).Value :=
  ⟨([], []), ⟨Nat.zero_le _, by simp⟩, ⟨Nat.zero_le _, by simp⟩⟩
def initialValue (value : (Pass.Initialization.points config).Value) : Pass.Initialization.Input config :=
  (emptyTapes config, value)
def parts : List (Part w) :=
  [.literal ((Pass.Initialization.tapes config).representation.encoding.encode (emptyTapes config)),
   .slice 0 (input config).encoding.words]
theorem parts_valid : Valid (input config).encoding.words (parts config) :=
  ⟨by omega, trivial⟩
theorem parts_size : ByteRoute.words (parts config) = (Pass.Initialization.input config).encoding.words := by
  simp only [parts, ByteRoute.words, Encoding.encode_length, Nat.add_zero]
  rfl
theorem parts_bytes (value : (Pass.Initialization.points config).Value) :
    bytes ((input config).encoding.encode value) (parts config) =
      (Pass.Initialization.input config).encoding.encode (initialValue config value) := by
  have copied := slice_block [] ((input config).encoding.encode value) []
  simp only [List.length_nil, List.nil_append, List.append_nil, Encoding.encode_length] at copied
  simp only [parts, bytes, List.append_nil, copied]
  rfl
def realizer : Realizer .unit (input config) (Pass.Initialization.input config) (initialValue config) :=
  ByteRoute.realizer _ _ _ (parts config) config.sampler.wordFits
    (parts_valid config) (parts_size config) (parts_bytes config)
theorem time (value) : (realizer config).time value ≤ 8 * (Pass.Initialization.input config).encoding.words :=
  ByteRoute.time _ _ _ _ _ _ _ _ value
theorem words : descriptionWords (realizer config).code ≤ 26 * (Pass.Initialization.input config).encoding.words + 14 :=
  ByteRoute.codeWords _ _ _ _ _ _ _ _
theorem names (slots : Nat) : NamesAccounted (realizer config).code slots :=
  ByteRoute.names _ _ _ _ _ _ _ _ slots
theorem buffers : (realizer config).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _

theorem ready (fuel : Nat) (tables : fuel + 1 ≤ config.capacityPred + 1)
    (tapes : 6 * fuel + 3 ≤ config.sampler.capacity) (value : (Pass.Initialization.points config).Value) :
    Pass.Replay.ready config fuel (initialValue config value) :=
  Pass.Replay.ready_empty config fuel (initialValue config value) rfl tables tapes
def start (fuel : Nat) (tables : fuel + 1 ≤ config.capacityPred + 1)
    (tapes : 6 * fuel + 3 ≤ config.sampler.capacity) (value : (Pass.Initialization.points config).Value) :
    {value : Pass.Initialization.Input config // Pass.Replay.ready config fuel value} :=
  ⟨initialValue config value, ready config fuel tables tapes value⟩
def prepared (fuel : Nat) (tables : fuel + 1 ≤ config.capacityPred + 1)
    (tapes : 6 * fuel + 3 ≤ config.sampler.capacity) :
    Realizer .unit (input config) (ReplayFirst.input config fuel) (start config fuel tables tapes) :=
  (realizer config).viewOutput (ReplayFirst.input config fuel) (start config fuel tables tapes) (fun _ => rfl)

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Setup
