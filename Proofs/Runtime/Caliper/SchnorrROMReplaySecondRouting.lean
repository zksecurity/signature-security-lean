import Proofs.Runtime.Caliper.SchnorrROMReplaySecondLayout

/-! Execute the replay reset with the original request retained, then copy the
runtime public points into the second pass's initialization frame. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplaySecond
open Caliper BoundedSource SchnorrROMTape ByteRoute
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

def resetValue (value : (ReplayRestart.input config.handler.sampler.tape).Value × Request config) :
    (Pass.Initialization.tapes config).Value × Request config :=
  (⟨ReplayRestart.source value.1.val,
    (ReplayRestart.implementation config.handler.sampler.tape).preserves value.1.val value.1.property⟩, value.2)
theorem resetNameFits : (ReplayRestart.implementation config.handler.sampler.tape).program.savedBuffer < 2 ^ w := by
  have bounded := ReplayRestart.buffers config.handler.sampler.tape
  have room := config.sampler.wordFits
  unfold Realizer.savedBuffer
  omega
def reset : Realizer .unit (prepared config) (restarted config) (resetValue config) :=
  (ReplayRestart.implementation config.handler.sampler.tape).program.retain (by decide) (rawInput config)
    config.sampler.wordFits (resetNameFits config) (prepared config).fits (restarted config).fits
def repackValue (value : (Pass.Initialization.tapes config).Value × Request config) :
    Pass.Initialization.Input config × Request config := ((value.1, pointsValue config value.2.2), value.2)
def repackParts : List (Part w) :=
  [.slice 0 (Pass.Initialization.tapes config).representation.encoding.words,
   .slice ((Pass.Initialization.tapes config).representation.encoding.words + (arguments config).encoding.words +
     (header config).encoding.words) (Pass.Initialization.points config).representation.encoding.words,
   .slice (Pass.Initialization.tapes config).representation.encoding.words (rawInput config).encoding.words]
theorem repack_valid : Valid (restarted config).encoding.words (repackParts config) := by
  have original := first_parts config
  change (first config).encoding.words = (header config).encoding.words +
    ((Pass.Initialization.points config).representation.encoding.words + (_ + _)) + _ at original
  simp only [repackParts, Valid]
  change (0 + _ ≤ (Pass.Initialization.tapes config).representation.encoding.words +
    ((arguments config).encoding.words + (first config).encoding.words)) ∧
    (_ + _ ≤ (Pass.Initialization.tapes config).representation.encoding.words +
      ((arguments config).encoding.words + (first config).encoding.words)) ∧
    (_ + _ ≤ (Pass.Initialization.tapes config).representation.encoding.words + (rawInput config).encoding.words) ∧ True
  exact ⟨by omega, by omega, le_rfl, trivial⟩
theorem repack_size : words (repackParts config) = (secondInput config).encoding.words := by
  change (Pass.Initialization.tapes config).representation.encoding.words +
    ((Pass.Initialization.points config).representation.encoding.words + ((rawInput config).encoding.words + 0)) =
      ((Pass.Initialization.tapes config).representation.encoding.words + (Pass.Initialization.points config).representation.encoding.words) +
        (rawInput config).encoding.words
  omega
def afterPointsBytes (value : Terminal.Output config) :=
  (Selection.tables config).representation.encoding.encode ⟨value.2.val.1.2, value.2.property.1.2⟩ ++
    (Pass.Initialization.tapes config).representation.encoding.encode (tapeValue config value)
theorem first_points (value : Terminal.Output config) : (first config).encoding.encode value =
    (header config).encoding.encode value.1 ++ (Pass.Initialization.points config).representation.encoding.encode (pointsValue config value) ++
      afterPointsBytes config value := by
  change _ ++ ((_ ++ _) ++ _) = (_ ++ _) ++ (_ ++ _)
  simp only [List.append_assoc]
  rfl
theorem repack_bytes (value : (Pass.Initialization.tapes config).Value × Request config) :
    bytes ((restarted config).encoding.encode value) (repackParts config) =
      (secondInput config).encoding.encode (repackValue config value) := by
  let tapes := (Pass.Initialization.tapes config).representation.encoding.encode value.1
  let args := (arguments config).encoding.encode value.2.1
  let tag := (header config).encoding.encode value.2.2.1
  let points := (Pass.Initialization.points config).representation.encoding.encode (pointsValue config value.2.2)
  let rest := afterPointsBytes config value.2.2
  let original := (rawInput config).encoding.encode value.2
  have tapesLength : tapes.length = (Pass.Initialization.tapes config).representation.encoding.words := Encoding.encode_length _ _
  have argsLength : args.length = (arguments config).encoding.words := Encoding.encode_length _ _
  have tagLength : tag.length = (header config).encoding.words := Encoding.encode_length _ _
  have pointsLength : points.length = (Pass.Initialization.points config).representation.encoding.words := Encoding.encode_length _ _
  have originalLength : original.length = (rawInput config).encoding.words := Encoding.encode_length _ _
  have split : original = args ++ (tag ++ points ++ rest) := congrArg (fun bytes => args ++ bytes) (first_points config value.2.2)
  have one := slice_block [] tapes original
  have two := slice_block (tapes ++ args ++ tag) points rest
  have three := slice_block tapes original []
  simp only [List.length_nil, List.nil_append, List.append_nil, List.length_append,
    tapesLength, argsLength, tagLength, pointsLength, originalLength] at one two three
  have allBytes : tapes ++ original = (tapes ++ args ++ tag) ++ points ++ rest := by rw [split]; simp only [List.append_assoc]
  rw [← allBytes] at two
  change bytes (tapes ++ original) (repackParts config) = (tapes ++ points) ++ original
  simp only [repackParts, bytes, List.append_nil]
  rw [one, two, three, List.append_assoc]
def repack : Realizer .unit (restarted config) (secondInput config) (repackValue config) :=
  ByteRoute.realizer _ _ _ (repackParts config) config.sampler.wordFits
    (repack_valid config) (repack_size config) (repack_bytes config)

def nextInput (fuel : Nat) (value : {value : Request config // ready config fuel value}) :=
  Pass.Replay.nextInput config value.val.2 value.val.1.1 value.val.1.2 (by have := value.property.2; omega)
def initializeReplay (fuel : Nat) : Realizer .unit (input config fuel) (secondInput config)
    (fun value => (nextInput config fuel value, value.val)) :=
  (((prepare config fuel).then (reset config)).then (repack config)).viewOutput (secondInput config)
    (fun value => (nextInput config fuel value, value.val)) (fun _ => rfl)
theorem next_ready (fuel : Nat) (value : {value : Request config // ready config fuel value}) :
    Pass.Initialization.admitted config fuel (nextInput config fuel value) := by
  have lengths := Pass.Replay.restart_lengths config value.val.2 value.val.1.1 value.val.1.2
    (by have := value.property.2; omega)
  exact ⟨value.property.1, by
    change (nextInput config fuel value).1.val.1.length ≤ value.val.2.2.val.2.1.length + 1 ∧ _ at lengths
    have := value.property.2
    omega⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplaySecond
