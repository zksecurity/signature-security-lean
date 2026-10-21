import Signatures.Runtime.Caliper.SchnorrROMReplaySecondSource

/-! Frames for selecting the second forgery without losing either pass. The
target ordinal is the runtime slot retained by the restart request. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayMatch
open Caliper BoundedSource SchnorrROMTape ByteRoute
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

abbrev Frame := Terminal.Output config × ReplaySecond.Request config
def frame := ReplaySecond.output config
theorem frame_words : (frame config).encoding.words =
    (ReplaySecond.first config).encoding.words + ((1 + 1) + (ReplaySecond.first config).encoding.words) := rfl
theorem fits {words : Nat} (small : words ≤ 8 * (ReplaySecond.first config).encoding.words + 16) : words < 2 ^ w :=
  ReplaySecond.combinedFits config small
def prepared := (ReplaySecond.first config).prod (frame config)
  (fits config (by rw [frame_words]; omega))
def selected := (Selection.result config).representation.prod (frame config)
  (fits config (by change (1 + 1) + _ ≤ _; rw [frame_words]; omega))
def argument := (Selection.result config).prod config.handler.sampler.tape.counter
  (by change (1 + 1) + 1 < _; have := config.sampler.wordFits; omega)
def checking := (argument config).representation.prod (frame config)
  (fits config (by change ((1 + 1) + 1) + _ ≤ _; rw [frame_words]; omega))
def output := (Selection.boolean config).representation.prod (frame config)
  (fits config (by change 1 + _ ≤ _; rw [frame_words]; omega))

def prepareParts : List (Part w) :=
  [.slice 0 (ReplaySecond.first config).encoding.words, .slice 0 (frame config).encoding.words]
theorem prepare_valid : Valid (frame config).encoding.words (prepareParts config) := by
  have := frame_words config
  exact ⟨by omega, by omega, trivial⟩
theorem prepare_size : words (prepareParts config) = (prepared config).encoding.words := by
  change _ + (_ + 0) = _ + _
  omega
theorem prepare_bytes (value : Frame config) : bytes ((frame config).encoding.encode value) (prepareParts config) =
    (prepared config).encoding.encode (value.1, value) := by
  have first := slice_block [] ((ReplaySecond.first config).encoding.encode value.1)
    ((ReplaySecond.rawInput config).encoding.encode value.2)
  have full := slice_block [] ((frame config).encoding.encode value) []
  simp only [List.length_nil, List.nil_append, List.append_nil, Encoding.encode_length] at first full
  change bytes ((frame config).encoding.encode value) (prepareParts config) =
    (ReplaySecond.first config).encoding.encode value.1 ++ (frame config).encoding.encode value
  simp only [prepareParts, bytes, List.append_nil]
  rw [full]
  exact congrArg (fun head => head ++ (frame config).encoding.encode value) first
def prepare : Realizer .unit (frame config) (prepared config) (fun value => (value.1, value)) :=
  ByteRoute.realizer _ _ _ (prepareParts config) config.sampler.wordFits
    (prepare_valid config) (prepare_size config) (prepare_bytes config)

def argumentValue (value : (Selection.result config).Value × Frame config) :
    (argument config).Value × Frame config :=
  (⟨(value.1.val, value.2.2.1.1.val), value.1.property, value.2.2.1.1.property⟩, value.2)
def argumentParts : List (Part w) :=
  [.slice 0 (Selection.result config).representation.encoding.words,
   .slice ((Selection.result config).representation.encoding.words + (ReplaySecond.first config).encoding.words) 1,
   .slice (Selection.result config).representation.encoding.words (frame config).encoding.words]
theorem argument_valid : Valid (selected config).encoding.words (argumentParts config) := by
  have width := frame_words config
  change (0 + 2 ≤ 2 + (frame config).encoding.words) ∧
    (2 + (ReplaySecond.first config).encoding.words + 1 ≤ 2 + (frame config).encoding.words) ∧
    (2 + (frame config).encoding.words ≤ 2 + (frame config).encoding.words) ∧ True
  exact ⟨by omega, by omega, le_rfl, trivial⟩
theorem argument_size : words (argumentParts config) = (checking config).encoding.words := by
  change 2 + (1 + ((frame config).encoding.words + 0)) = (2 + 1) + (frame config).encoding.words
  omega
theorem argument_bytes (value : (Selection.result config).Value × Frame config) :
    bytes ((selected config).encoding.encode value) (argumentParts config) =
      (checking config).encoding.encode (argumentValue config value) := by
  let selection := (Selection.result config).representation.encoding.encode value.1
  let second := (ReplaySecond.first config).encoding.encode value.2.1
  let target := config.handler.sampler.tape.counter.representation.encoding.encode value.2.2.1.1
  let rest := config.handler.sampler.tape.scalar.representation.encoding.encode value.2.2.1.2 ++
    (ReplaySecond.first config).encoding.encode value.2.2.2
  let original := (frame config).encoding.encode value.2
  have selectionLength : selection.length = (Selection.result config).representation.encoding.words := Encoding.encode_length _ _
  have secondLength : second.length = (ReplaySecond.first config).encoding.words := Encoding.encode_length _ _
  have targetLength : target.length = 1 := Encoding.encode_length _ _
  have originalLength : original.length = (frame config).encoding.words := Encoding.encode_length _ _
  have split : original = second ++ (target ++ rest) := by
    change _ ++ ((_ ++ _) ++ _) = _ ++ (_ ++ (_ ++ _))
    simp only [List.append_assoc]
    rfl
  have one := slice_block [] selection original
  have two := slice_block (selection ++ second) target rest
  have three := slice_block selection original []
  simp only [List.length_nil, List.nil_append, List.append_nil, List.length_append,
    selectionLength, secondLength, targetLength, originalLength] at one two three
  have full : selection ++ original = (selection ++ second) ++ target ++ rest := by
    rw [split]
    simp only [List.append_assoc]
  rw [← full] at two
  change bytes (selection ++ original) (argumentParts config) = (selection ++ target) ++ original
  simp only [argumentParts, bytes, List.append_nil]
  rw [one, two, three, List.append_assoc]
def arguments : Realizer .unit (selected config) (checking config) (argumentValue config) :=
  ByteRoute.realizer _ _ _ (argumentParts config) config.sampler.wordFits
    (argument_valid config) (argument_size config) (argument_bytes config)

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayMatch
