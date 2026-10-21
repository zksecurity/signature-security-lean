import Signatures.Runtime.Caliper.SchnorrROMPassBuffers
import Signatures.Runtime.Caliper.SchnorrROMPassSelectionBounds
import Signatures.Runtime.Caliper.SchnorrROMReplayAdmission

/-! Frames for replaying the second pass while retaining the first result.
The admission predicate reserves the second pass's tape growth; it follows
from the first pass and is not an additional completed-controller assumption. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplaySecond
open Caliper BoundedSource SchnorrROMTape ByteRoute
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

abbrev Request := (config.handler.sampler.tape.counter.Value × config.handler.sampler.tape.scalar.Value) × Terminal.Output config
def arguments := config.handler.sampler.tape.counter.representation.prod config.handler.sampler.tape.scalar.representation
  (by change 1 + 1 < _; have := config.sampler.wordFits; omega)
def header := (Pairing.unitRepresentation w).sum (ForgeryHash.result config) (width_pos config.sampler.wordFits)
  (by have := PassSelection.inputFits config; omega)
def first := PassSelection.input config
def prefixWords := (header config).encoding.words + config.handler.caches.representation.encoding.words
theorem first_parts : (first config).encoding.words = prefixWords config + (Pass.Initialization.tapes config).representation.encoding.words := by
  change (header config).encoding.words + (config.handler.caches.representation.encoding.words +
    (Pass.Initialization.tapes config).representation.encoding.words) =
      ((header config).encoding.words + config.handler.caches.representation.encoding.words) +
        (Pass.Initialization.tapes config).representation.encoding.words
  omega
theorem first_size : (first config).encoding.words ≤ 8 * config.handler.width + 1 := by
  have size := (Selection.sizes config).1
  change (ForgeryHash.result config).encoding.words + config.handler.store.representation.encoding.words ≤ _ at size
  change 1 + max 0 _ + _ ≤ _
  omega
theorem initial_size : (Pass.Initialization.input config).encoding.words ≤ (first config).encoding.words := by
  have parts := first_parts config
  change _ + (Pass.Initialization.points config).representation.encoding.words ≤ _
  change _ = ((header config).encoding.words +
    ((Pass.Initialization.points config).representation.encoding.words + (_ + _))) + _ at parts
  omega
theorem combinedFits {words : Nat} (small : words ≤ 8 * (first config).encoding.words + 16) : words < 2 ^ w :=
  config.handler.fits_of_le (by have := first_size config; have := Random.positive config; omega)

def rawInput : Representation w (Request config) := (arguments config).prod (first config)
  (combinedFits config (by change (1 + 1) + _ ≤ _; omega))
def ready (fuel : Nat) (value : Request config) : Prop :=
  fuel + 1 ≤ config.capacityPred + 1 ∧ value.2.2.val.2.1.length + (2 * fuel + 2) ≤ config.sampler.capacity
instance (fuel : Nat) : DecidablePred (ready config fuel) := fun _ => by unfold ready; infer_instance
def input (fuel : Nat) := (rawInput config).restrict (ready config fuel)
def prepared := (ReplayRestart.input config.handler.sampler.tape).representation.prod (rawInput config)
  (combinedFits config (by
    have parts := first_parts config
    change (1 + (1 + (Pass.Initialization.tapes config).representation.encoding.words)) + ((1 + 1) + _) ≤ _
    omega))
def restarted := (Pass.Initialization.tapes config).representation.prod (rawInput config)
  (combinedFits config (by have := first_parts config; change _ + ((1 + 1) + _) ≤ _; omega))
def secondInput := (Pass.Initialization.input config).prod (rawInput config)
  (combinedFits config (by have := initial_size config; change _ + ((1 + 1) + _) ≤ _; omega))
def output := (first config).prod (rawInput config)
  (combinedFits config (by change _ + ((1 + 1) + _) ≤ _; omega))

def tapeValue (value : Terminal.Output config) : (Pass.Initialization.tapes config).Value :=
  ⟨value.2.val.2, value.2.property.2⟩
def pointsValue (value : Terminal.Output config) : (Pass.Initialization.points config).Value :=
  ⟨value.2.val.1.1, value.2.property.1.1⟩
def prefixBytes (value : Terminal.Output config) := (header config).encoding.encode value.1 ++
  config.handler.caches.representation.encoding.encode ⟨value.2.val.1, value.2.property.1⟩
theorem prefix_length (value : Terminal.Output config) : (prefixBytes config value).length = prefixWords config := by
  simp only [prefixBytes, List.length_append, Encoding.encode_length, prefixWords]
theorem first_bytes (value : Terminal.Output config) : (first config).encoding.encode value =
    prefixBytes config value ++ (Pass.Initialization.tapes config).representation.encoding.encode (tapeValue config value) := by
  change _ ++ (_ ++ _) = (_ ++ _) ++ _
  rw [List.append_assoc]
  rfl

def prepareValue (fuel : Nat) (value : {value : Request config // ready config fuel value}) :=
  (Pass.Replay.request config value.val.2 value.val.1.1 value.val.1.2
    (by have := value.property.2; omega), value.val)
def prepareParts : List (Part w) :=
  [.slice 0 (arguments config).encoding.words,
   .slice ((arguments config).encoding.words + prefixWords config) (Pass.Initialization.tapes config).representation.encoding.words,
   .slice 0 (rawInput config).encoding.words]
theorem prepare_valid (fuel : Nat) : Valid (input config fuel).encoding.words (prepareParts config) := by
  simp only [prepareParts, Valid]
  change (0 + _ ≤ (arguments config).encoding.words + (first config).encoding.words) ∧
    (_ + _ ≤ (arguments config).encoding.words + (first config).encoding.words) ∧
    (0 + (rawInput config).encoding.words ≤ (rawInput config).encoding.words) ∧ True
  have := first_parts config
  exact ⟨by omega, by omega, by omega, trivial⟩
theorem prepare_size : words (prepareParts config) = (prepared config).encoding.words := by
  change (1 + 1) + ((Pass.Initialization.tapes config).representation.encoding.words +
    ((rawInput config).encoding.words + 0)) =
      (1 + (1 + (Pass.Initialization.tapes config).representation.encoding.words)) + (rawInput config).encoding.words
  omega
theorem prepare_bytes (fuel : Nat) (value : {value : Request config // ready config fuel value}) :
    bytes ((input config fuel).encoding.encode value) (prepareParts config) =
      (prepared config).encoding.encode (prepareValue config fuel value) := by
  let args := (arguments config).encoding.encode value.val.1
  let front := prefixBytes config value.val.2
  let tapes := (Pass.Initialization.tapes config).representation.encoding.encode (tapeValue config value.val.2)
  let original := (first config).encoding.encode value.val.2
  have argsLength : args.length = (arguments config).encoding.words := Encoding.encode_length _ _
  have prefixLength : front.length = prefixWords config := prefix_length config _
  have tapeLength : tapes.length = (Pass.Initialization.tapes config).representation.encoding.words := Encoding.encode_length _ _
  have originalLength : original.length = (first config).encoding.words := Encoding.encode_length _ _
  have split : original = front ++ tapes := first_bytes config _
  have one := slice_block [] args original
  have two := slice_block (args ++ front) tapes []
  have three := slice_block [] (args ++ original) []
  simp only [List.length_nil, List.nil_append, List.append_nil, List.length_append,
    argsLength, prefixLength, tapeLength, originalLength] at one two three
  change ((args ++ original).drop 0).take (rawInput config).encoding.words = args ++ original at three
  change bytes (args ++ original) (prepareParts config) = (args ++ tapes) ++ (args ++ original)
  simp only [prepareParts, bytes, List.append_nil]
  rw [List.append_assoc] at two
  rw [one, three, split, two]
  simp only [List.append_assoc]
def prepare (fuel : Nat) : Realizer .unit (input config fuel) (prepared config) (prepareValue config fuel) :=
  ByteRoute.realizer _ _ _ (prepareParts config) config.sampler.wordFits
    (prepare_valid config fuel) (prepare_size config) (prepare_bytes config fuel)

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplaySecond
