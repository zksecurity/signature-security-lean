import Signatures.Runtime.Caliper.SchnorrAGMLayout
import Signatures.Runtime.Caliper.ImplementationMemory

/-! Executed Schnorr AGM initialization. Both copies of the challenge are read
from runtime input. The empty cache, initial affine basis, signed-message list
and flags are written as charged literal instructions, including all padding. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Setup
open Caliper BoundedSource Assembly
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS : Nat} {M F G : Type} [Zero F] [One F]
    (layout : Layouts w M F G qH qS)
    (zeroValid : layout.scalar.valid 0) (oneValid : layout.scalar.valid 1)

def initial : layout.state.Value := ⟨([], [(1, 0), (0, 1)], [], false, false), by
  refine ⟨⟨by simp, by simp⟩, ⟨by change 2 ≤ qS + 2; omega, ?_⟩,
    ⟨by simp, by simp⟩, trivial, trivial⟩
  intro pair member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨oneValid, zeroValid⟩
  · rcases List.mem_cons.mp member with rfl | member
    · exact ⟨zeroValid, oneValid⟩
    · cases member⟩

def initialized (value : layout.config.Value) : layout.initialized.Value :=
  ⟨(value.val, value.val, (initial layout zeroValid oneValid).val),
    value.property, value.property, (initial layout zeroValid oneValid).property⟩

def operands : List (Operand w) :=
  reads 0 0 layout.config.representation.encoding.words ++
    reads 0 0 layout.config.representation.encoding.words ++
    (layout.state.representation.encoding.encode (initial layout zeroValid oneValid)).map Operand.literal

theorem operands_length : (operands layout zeroValid oneValid).length = layout.initialized.representation.encoding.words := by
  simp only [operands, List.length_append, reads_length, List.length_map, Encoding.encode_length]
  change _ + _ + _ = _ + (_ + _)
  omega

theorem output_bytes (value : layout.config.Value) :
    layout.initialized.representation.encoding.encode (initialized layout zeroValid oneValid value) =
      layout.config.representation.encoding.encode value ++ layout.config.representation.encoding.encode value ++
        layout.state.representation.encoding.encode (initial layout zeroValid oneValid) := by
  change (_ ++ _) ++ ((_ ++ _) ++ _) = ((_ ++ _) ++ (_ ++ _)) ++ _
  exact (List.append_assoc _ _ _).symm

def code : Realizer .unit layout.config.representation layout.initialized.representation
    (initialized layout zeroValid oneValid) :=
  Assembly.realizer .unit (by decide) _ _ _ (operands layout zeroValid oneValid) layout.wordFits
    (operands_length layout zeroValid oneValid)
    (by
      intro operand member
      rcases List.mem_append.mp member with copied | literal
      · rcases List.mem_append.mp copied with copied | copied <;>
          exact reads_namesFit _ _ _ (by have := layout.wordFits; omega) operand copied
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp literal
        trivial)
    (by
      intro value before represented operand member
      rcases List.mem_append.mp member with copied | literal
      · rcases List.mem_append.mp copied with copied | copied <;>
          exact reads_valid 1 0 0 _ before (by decide)
            (by rw [represented_size _ represented]; omega)
            (by rw [represented_size _ represented]; exact layout.config.representation.fits) operand copied
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp literal
        trivial)
    (by
      intro value before represented
      have copied := reads_values 0 0 layout.config.representation.encoding.words before
        (by rw [represented_size _ represented]; omega)
      rw [represented.2.1] at copied
      rw [List.drop_zero, List.take_of_length_le (layout.config.representation.encoding.encode_length value).le] at copied
      rw [output_bytes]
      simp only [operands, values, List.map_append, List.map_map]
      exact congrArg₂ List.append (congrArg₂ List.append copied copied) (List.map_id _))

def implementation : Implementation .unit layout.config layout.initialized
    (fun value => (value, value, ([], [(1, 0), (0, 1)], [], false, false))) where
  preserves _ valid := ⟨valid, valid, (initial layout zeroValid oneValid).property⟩
  program := code layout zeroValid oneValid

theorem bounded : (implementation layout zeroValid oneValid).BoundedBy
    (8 * layout.initialized.representation.encoding.words)
    (26 * layout.initialized.representation.encoding.words + 14) := by
  constructor
  · intro value
    change (Assembly.code (operands layout zeroValid oneValid)).staticTime .unit ≤ _
    simpa only [operands_length] using code_time_unit_le (operands layout zeroValid oneValid)
  · change descriptionWords (Assembly.code (operands layout zeroValid oneValid)) ≤ _
    simpa only [operands_length] using code_descriptionWords_le (operands layout zeroValid oneValid)

theorem sources : SourcesBound (operands layout zeroValid oneValid) 1 := by
  apply (sourcesBound_append _ _ _).mpr
  refine ⟨(sourcesBound_append _ _ _).mpr ⟨sourcesBound_reads _ _ _ _ (by decide),
    sourcesBound_reads _ _ _ _ (by decide)⟩, ?_⟩
  intro operand member
  obtain ⟨word, _, rfl⟩ := List.mem_map.mp member
  trivial

theorem names : NamesBound (implementation layout zeroValid oneValid).program.code 3 := by
  have bounds := code_names (operands layout zeroValid oneValid) 1 (sources layout zeroValid oneValid)
  exact ⟨bounds.1, bounds.2.trans (by decide)⟩

theorem buffers : (implementation layout zeroValid oneValid).program.code.memBound ≤ 2 :=
  (code_names (operands layout zeroValid oneValid) 1 (sources layout zeroValid oneValid)).2

section Source
variable {w qH qS : Nat} {M F G : Type} [Field F]
    (layout : Layouts w M F G qH qS)
    (zeroValid : layout.scalar.valid 0) (oneValid : layout.scalar.valid 1)

/-- Exact initial state of the existing finite-store reduction, including the
public-generator/public-key affine basis. The code does not sample randomness. -/
theorem initial_source : (initial layout zeroValid oneValid).val =
    encodeState ({} : Signatures.Runtime.SchnorrAGM.State F G M) := rfl

end Source
end Signatures.Runtime.CaliperBackend.SchnorrAGM.Setup
