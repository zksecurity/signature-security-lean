import Proofs.Runtime.Caliper.SchnorrROMPassCallerBounds

/-! Initialize a pass from its runtime tapes, generator and public key. The
public key is copied for the caller; both caches are written empty. Replay and
saved tapes are copied intact, so the same initializer can serve both passes. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Pass.Initialization
open Caliper BoundedSource SchnorrROMTape ByteRoute
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

def tapes := Read.tapes config.handler.sampler.tape
def points := config.handler.core.arithmetic.points
abbrev Input := (tapes config).Value × (points config).Value
def input : Representation w (Input config) := (tapes config).representation.prod (points config).representation (by
  have room := config.handler.store.representation.fits
  change ((points config).representation.encoding.words + (_ + _)) + (tapes config).representation.encoding.words < _ at room
  omega)
def output := config.point.representation.prod config.handler.store.representation (Pass.inputFits config)
def empty : config.handler.core.table.Value := ⟨[], Nat.zero_le _, by simp⟩
def store (value : Input config) : config.handler.store.Value :=
  ⟨((value.2.val, [], []), value.1.val), ⟨value.2.property, (empty config).property, (empty config).property⟩, value.1.property⟩
def start (value : Input config) : config.point.Value × config.handler.store.Value :=
  (⟨value.2.val.2, value.2.property.2⟩, store config value)
def cacheBytes := config.handler.core.table.representation.encoding.encode (empty config) ++
  config.handler.core.table.representation.encoding.encode (empty config)
def parts : List (Part w) :=
  [.slice ((tapes config).representation.encoding.words + config.point.representation.encoding.words) config.point.representation.encoding.words,
   .slice (tapes config).representation.encoding.words (points config).representation.encoding.words,
   .literal (cacheBytes config), .slice 0 (tapes config).representation.encoding.words]
theorem parts_valid : Valid (input config).encoding.words (parts config) := by
  simp only [parts, Valid]
  change ((tapes config).representation.encoding.words + config.point.representation.encoding.words) +
    config.point.representation.encoding.words ≤ (tapes config).representation.encoding.words +
      (config.point.representation.encoding.words + config.point.representation.encoding.words) ∧
    (tapes config).representation.encoding.words + (points config).representation.encoding.words ≤
      (tapes config).representation.encoding.words + (points config).representation.encoding.words ∧
    0 + (tapes config).representation.encoding.words ≤
      (tapes config).representation.encoding.words + (points config).representation.encoding.words ∧ True
  exact ⟨by omega, le_rfl, by omega, trivial⟩
theorem parts_size : words (parts config) = (output config).encoding.words := by
  simp only [parts, words, cacheBytes, List.length_append, Encoding.encode_length]
  change config.point.representation.encoding.words + ((points config).representation.encoding.words +
    ((config.handler.core.table.representation.encoding.words + config.handler.core.table.representation.encoding.words) +
      ((tapes config).representation.encoding.words + 0))) = config.point.representation.encoding.words +
    (((points config).representation.encoding.words +
      (config.handler.core.table.representation.encoding.words + config.handler.core.table.representation.encoding.words)) +
        (tapes config).representation.encoding.words)
  omega
theorem parts_bytes (value : Input config) : bytes ((input config).encoding.encode value) (parts config) =
    (output config).encoding.encode (start config value) := by
  let tape := (tapes config).representation.encoding.encode value.1
  let generator := config.point.representation.encoding.encode ⟨value.2.val.1, value.2.property.1⟩
  let key := config.point.representation.encoding.encode ⟨value.2.val.2, value.2.property.2⟩
  let pair := (points config).representation.encoding.encode value.2
  have split : pair = generator ++ key := rfl
  have tapeLength : tape.length = (tapes config).representation.encoding.words := Encoding.encode_length _ _
  have generatorLength : generator.length = config.point.representation.encoding.words := Encoding.encode_length _ _
  have keyLength : key.length = config.point.representation.encoding.words := Encoding.encode_length _ _
  have pairLength : pair.length = (points config).representation.encoding.words := Encoding.encode_length _ _
  have one := slice_block (tape ++ generator) key []
  have two := slice_block tape pair []
  have three := slice_block [] tape pair
  simp only [List.length_append, List.length_nil, List.nil_append, List.append_nil,
    tapeLength, generatorLength, keyLength, pairLength] at one two three
  change bytes (tape ++ pair) (parts config) = key ++ ((pair ++ cacheBytes config) ++ tape)
  simp only [parts, bytes, List.append_nil]
  rw [two, three]
  rw [List.append_assoc] at one
  rw [split, one]
  simp only [List.append_assoc]
def code : Realizer .unit (input config) (output config) (start config) :=
  ByteRoute.realizer _ _ _ (parts config) config.sampler.wordFits (parts_valid config) (parts_size config) (parts_bytes config)
theorem time (value) : (code config).time value ≤ 8 * (output config).encoding.words := ByteRoute.time _ _ _ _ _ _ _ _ value
theorem words : descriptionWords (code config).code ≤ 26 * (output config).encoding.words + 14 := ByteRoute.codeWords _ _ _ _ _ _ _ _
theorem names (slots : Nat) : NamesAccounted (code config).code slots := ByteRoute.names _ _ _ _ _ _ _ _ slots
theorem buffers : (code config).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _

def admitted (fuel : Nat) (value : Input config) : Prop :=
  fuel + 1 ≤ config.capacityPred + 1 ∧ value.1.val.1.length + (3 * fuel + 1) ≤ config.sampler.capacity
theorem reserved (fuel : Nat) (value : Input config) (room : admitted config fuel value) :
    Handler.Reserved config fuel (store config value).val := by
  change 0 + fuel ≤ _ ∧ 0 + (fuel + 1) ≤ _ ∧ _ ≤ _
  exact ⟨by have := room.1; omega, by simpa only [Nat.zero_add] using room.1, room.2⟩

end Signatures.Runtime.CaliperBackend.SchnorrROM.Pass.Initialization
