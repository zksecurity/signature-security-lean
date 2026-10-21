import Signatures.Runtime.Caliper.SchnorrROMFreshGuardStep
import Signatures.Runtime.Caliper.ByteRoute

/-! Charge the routing of a runtime slot, replacement and saved tape into the
scan frame. The two initial false flags are literal machine words. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.FreshGuard
open Caliper BoundedSource SchnorrROMTape ByteRoute
variable {w : Nat} {F : Type} (layout : Layouts w F)

def prepareValue (value : (input layout).Value) : (frame layout).Value :=
  ⟨(value.val.2.2, (value.val.1, false, false), value.val.2.1),
    value.property.2.2, ⟨value.property.1, trivial, trivial⟩, value.property.2.1⟩
def prepareParts : List (Part w) :=
  [.slice (1 + layout.scalar.representation.encoding.words) (layout.list layout.capacity (by omega)).representation.encoding.words,
   .slice 0 1, .literal [0, 0], .slice 1 layout.scalar.representation.encoding.words]
theorem prepare_valid : Valid (input layout).representation.encoding.words (prepareParts layout) := by
  change (1 + _ + _ ≤ 1 + (_ + _)) ∧ (0 + 1 ≤ 1 + (_ + _)) ∧ (1 + _ ≤ 1 + (_ + _)) ∧ True
  exact ⟨by omega, by omega, by omega, trivial⟩
theorem prepare_size : words (prepareParts layout) = (frame layout).representation.encoding.words := by
  change (1 + layout.capacity * layout.entry.representation.encoding.words) +
    (1 + (2 + (layout.scalar.representation.encoding.words + 0))) =
      (1 + layout.capacity * layout.entry.representation.encoding.words) + (3 + layout.scalar.representation.encoding.words)
  omega
theorem prepare_bytes (value : (input layout).Value) :
    bytes ((input layout).representation.encoding.encode value) (prepareParts layout) =
      (frame layout).representation.encoding.encode (prepareValue layout value) := by
  let slot := layout.counter.representation.encoding.encode ⟨value.val.1, value.property.1⟩
  let replacement := layout.scalar.representation.encoding.encode ⟨value.val.2.1, value.property.2.1⟩
  let cells := (layout.list layout.capacity (by omega)).representation.encoding.encode ⟨value.val.2.2, value.property.2.2⟩
  have slotLength : slot.length = 1 := Encoding.encode_length _ _
  have replacementLength : replacement.length = layout.scalar.representation.encoding.words := Encoding.encode_length _ _
  have cellsLength : cells.length = (layout.list layout.capacity (by omega)).representation.encoding.words := Encoding.encode_length _ _
  have first := slice_block (slot ++ replacement) cells []
  have second := slice_block [] slot (replacement ++ cells)
  have third := slice_block slot replacement cells
  simp only [List.length_append, slotLength, replacementLength, cellsLength, List.append_nil,
    List.length_nil, List.nil_append, List.append_assoc] at first second third
  change bytes (slot ++ (replacement ++ cells)) (prepareParts layout) = cells ++ ((slot ++ [0, 0]) ++ replacement)
  simp only [prepareParts, bytes, List.append_nil]
  rw [first, second, third]
  simp only [List.append_assoc]
def prepare : Constructed (input layout) (frame layout) (fun value => (value.2.2, (value.1, false, false), value.2.1)) where
  implementation :=
    { preserves := fun _ valid => ⟨valid.2.2, ⟨valid.1, trivial, trivial⟩, valid.2.1⟩
      program := ByteRoute.realizer _ _ (prepareValue layout) (prepareParts layout) layout.wordFits
        (prepare_valid layout) (prepare_size layout) (prepare_bytes layout) }
  budget := ⟨8 * (frame layout).representation.encoding.words, 26 * (frame layout).representation.encoding.words + 14⟩
  bounded := ⟨ByteRoute.time _ _ (prepareValue layout) (prepareParts layout) layout.wordFits
    (prepare_valid layout) (prepare_size layout) (prepare_bytes layout), ByteRoute.codeWords _ _ (prepareValue layout) (prepareParts layout) layout.wordFits
    (prepare_valid layout) (prepare_size layout) (prepare_bytes layout)⟩
  buffers := 2
  buffers_le := ByteRoute.buffers _ _ (prepareValue layout) (prepareParts layout) layout.wordFits
    (prepare_valid layout) (prepare_size layout) (prepare_bytes layout)
  names := ByteRoute.names _ _ (prepareValue layout) (prepareParts layout) layout.wordFits
    (prepare_valid layout) (prepare_size layout) (prepare_bytes layout)

end Signatures.Runtime.CaliperBackend.SchnorrROM.FreshGuard
