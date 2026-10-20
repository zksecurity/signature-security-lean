import Signatures.Runtime.Caliper.SchnorrAGMRandomLayout
import Signatures.Runtime.Caliper.SourceListBytes
import Signatures.Runtime.Caliper.EncodedEquality

/-! The executed random-request test reads the group-list header and compares
it with zero. Bounded lengths make the test agree with source emptiness. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Random
open Caliper BoundedSource Assembly
variable {w qH qS randomBound : Nat} {M F G : Type} (layout : Layouts w M F G qH qS randomBound)

def inputPoints (args : layout.input.Value) : layout.points.Value := ⟨args.val.1, args.property.1⟩
def inputRows (args : layout.input.Value) : layout.coefficientRows.Value := ⟨args.val.2.1, args.property.2.1⟩
def inputBase (args : layout.input.Value) : layout.base.Value := ⟨args.val.2.2, args.property.2.2⟩
def inputState (args : layout.input.Value) : layout.scheme.state.Value :=
  ⟨(inputBase layout args).val.2, (inputBase layout args).property.2⟩
theorem input_bytes (args : layout.input.Value) : layout.input.representation.encoding.encode args =
    layout.points.representation.encoding.encode (inputPoints layout args) ++
      (layout.coefficientRows.representation.encoding.encode (inputRows layout args) ++
        layout.base.representation.encoding.encode (inputBase layout args)) := rfl

def header := wordRepresentation w (width_pos layout.scheme.wordFits)
def compared : Representation w (Word w × Word w) := (header layout).prod (header layout)
  (by change 1 + 1 < 2 ^ w; have := layout.scheme.wordFits; omega)
def testOperands : List (Operand w) := reads 0 0 1 ++ [.literal 0]
theorem testOperands_length : (testOperands (w := w)).length = 2 := by simp only [testOperands, List.length_append, reads_length]; rfl
theorem testOperands_sources : SourcesBound (testOperands (w := w)) 1 := by
  simp only [testOperands, sourcesBound_append]
  refine ⟨sourcesBound_reads _ _ _ _ (by decide), ?_⟩
  intro operand member
  simp only [List.mem_singleton] at member
  subst operand
  trivial

def prepareTest : Realizer .unit layout.input.representation (compared layout)
    (fun args => (BitVec.ofNat w args.val.1.length, 0)) :=
  Assembly.realizer .unit (by decide) _ _ _ testOperands layout.scheme.wordFits testOperands_length
    (by
      intro operand member
      rcases List.mem_append.mp member with copied | literal
      · exact reads_namesFit 0 _ _ (by positivity) operand copied
      · simp only [List.mem_singleton] at literal; subst operand; trivial)
    (by
      intro args before represented operand member
      have size := represented_size _ represented
      rw [layout.input_words] at size
      have headerExists : 1 ≤ layout.points.representation.encoding.words := by change 1 ≤ 1 + _; omega
      have fits : (before.bufs 0).size < 2 ^ w := by rw [represented_size _ represented]; exact layout.input.representation.fits
      rcases List.mem_append.mp member with copied | literal
      · exact reads_valid 1 0 0 1 before (by decide) (by omega) fits operand copied
      · simp only [List.mem_singleton] at literal; subst operand; trivial)
    (by
      intro args before represented
      have contents := represented.2.1
      rw [input_bytes] at contents
      have read := ListBytes.read_header layout.scheme.point layout.groups layout.groupCountFits layout.points.representation.fits
        (inputPoints layout args) [] (layout.coefficientRows.representation.encoding.encode (inputRows layout args) ++
          layout.base.representation.encoding.encode (inputBase layout args)) before contents
      simp only [List.length_nil] at read
      simp only [testOperands, values, List.map_append]
      change values (reads 0 0 1) before ++ [0] = _
      rw [read]
      rfl)

theorem header_equal (args : layout.input.Value) : decide (BitVec.ofNat w args.val.1.length = (0 : Word w)) = shape args.val := by
  have fits : args.val.1.length < 2 ^ w := args.property.1.1.trans_lt layout.groupCountFits
  have zero : BitVec.ofNat w args.val.1.length = (0 : Word w) ↔ args.val.1.length = 0 := by
    constructor
    · intro equal
      have numbers := congrArg BitVec.toNat equal
      change args.val.1.length % 2 ^ w = 0 % 2 ^ w at numbers
      simpa only [Nat.mod_eq_of_lt fits, Nat.zero_mod] using numbers
    · intro equal; rw [equal]; rfl
  simp only [zero, shape]
  cases args.val.1 <;> rfl

def test : Implementation .unit layout.input (DataImplementation.boolLayout w (width_pos layout.scheme.wordFits)) shape where
  preserves _ _ := trivial
  program := ((prepareTest layout).then
    (EncodedEquality.realizer .unit (header layout) layout.scheme.wordFits (compared layout).fits)).viewOutput
      (DataImplementation.boolLayout w (width_pos layout.scheme.wordFits)).representation (fun args => ⟨shape args.val, trivial⟩) (by
        intro args
        change [if shape args.val then 1 else 0] = [if decide (BitVec.ofNat w args.val.1.length = (0 : Word w)) then 1 else 0]
        rw [header_equal])

theorem test_bounded : (test layout).BoundedBy 32 128 := by
  have packed := code_time_unit_le (testOperands (w := w))
  have stored := code_descriptionWords_le (testOperands (w := w))
  rw [testOperands_length] at packed stored
  constructor
  · intro args
    change (Assembly.code testOperands).staticTime .unit + EncodedEquality.time .unit 1 ≤ _
    rw [EncodedEquality.time_unit]
    omega
  · change descriptionWords (Assembly.code testOperands ;; EncodedEquality.code 1) ≤ _
    rw [descriptionWords_seq, EncodedEquality.code_descriptionWords]
    omega
theorem test_names : NamesBound (test layout).program.code 5 := by
  have packed := code_names (testOperands (w := w)) 1 testOperands_sources
  have equality := EncodedEquality.code_names (w := w) 1
  exact ⟨max_le (packed.1.trans (by decide)) equality.registers, max_le (packed.2.trans (by decide)) equality.buffers⟩
theorem test_nameFits : (test layout).program.savedBuffer < 2 ^ w := by
  have := (test_names layout).buffers
  have := layout.scheme.wordFits
  change max 2 (test layout).program.code.memBound < _
  omega
end Signatures.Runtime.CaliperBackend.SchnorrAGM.Random
