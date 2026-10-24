import Proofs.Runtime.Caliper.SchnorrAGMHashDispatchLayout
import Proofs.Runtime.Caliper.SourceListBytes

/-! The hash request selector executes reads of both list headers and compares
the resulting two-word value with a stored pair of ones. It then retains the
input and emits the actual branch tag, with bounded copies and code. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.HashDispatch
open Caliper BoundedSource Assembly
variable {w qH qS : Nat} {M F G : Type} [DecidableEq M] [DecidableEq G]
    (layout : Layouts w M F G qH qS)

def inputMessage (value : layout.input.Value) : layout.hash.scheme.message.Value := ⟨value.val.1, value.property.1.1⟩
def inputPoints (value : layout.input.Value) : layout.points.Value := ⟨value.val.2.1, value.property.1.2.1⟩
def inputRows (value : layout.input.Value) : layout.coefficients.Value := ⟨value.val.2.2.1, value.property.1.2.2.1⟩
def inputState (value : layout.input.Value) : layout.hash.scheme.state.Value := ⟨value.val.2.2.2, value.property.1.2.2.2⟩

theorem input_bytes (value : layout.input.Value) : layout.input.representation.encoding.encode value =
    layout.hash.scheme.message.representation.encoding.encode (inputMessage layout value) ++
      (layout.points.representation.encoding.encode (inputPoints layout value) ++
        (layout.coefficients.representation.encoding.encode (inputRows layout value) ++
          layout.hash.scheme.state.representation.encoding.encode (inputState layout value))) := rfl

def headerPair := WordBinary.pair w layout.hash.scheme.wordFits
def compared : Representation w ((Word w × Word w) × (Word w × Word w)) :=
  (headerPair layout).prod (headerPair layout) (by change 2 + 2 < 2 ^ w; have := layout.hash.scheme.wordFits; omega)
def headers (value : layout.input.Value) : Word w × Word w :=
  (BitVec.ofNat w value.val.2.1.length, BitVec.ofNat w value.val.2.2.1.length)

def testOperands : List (Operand w) :=
  reads 0 layout.hash.scheme.message.representation.encoding.words 1 ++
    reads 0 (layout.hash.scheme.message.representation.encoding.words + layout.points.representation.encoding.words) 1 ++
      [.literal 1, .literal 1]
omit [DecidableEq M] [DecidableEq G] in
theorem testOperands_length : (testOperands layout).length = 4 := by
  simp only [testOperands, List.length_append, reads_length, List.length_cons, List.length_nil]
omit [DecidableEq M] [DecidableEq G] in
theorem testOperands_sources : SourcesBound (testOperands layout) 1 := by
  simp only [testOperands, sourcesBound_append]
  refine ⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩, ?_⟩
  intro operand member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> trivial

def prepareTest : Realizer .unit layout.input.representation (compared layout)
    (fun value => (headers layout value, (1, 1))) :=
  Assembly.realizer .unit (by decide) _ _ _ (testOperands layout) layout.hash.scheme.wordFits (testOperands_length layout)
    (by
      intro operand member
      simp only [testOperands, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with (member | member) | (rfl | rfl)
      · exact reads_namesFit 0 _ _ (by positivity) operand member
      · exact reads_namesFit 0 _ _ (by positivity) operand member
      · trivial
      · trivial)
    (by
      intro value before represented operand member
      have size := represented_size _ represented
      rw [layout.input_words] at size
      have points : 1 ≤ layout.points.representation.encoding.words := by change 1 ≤ 1 + _; omega
      have rows : 1 ≤ layout.coefficients.representation.encoding.words := by change 1 ≤ 1 + _; omega
      have fits : (before.bufs 0).size < 2 ^ w := by rw [represented_size _ represented]; exact layout.input.representation.fits
      simp only [testOperands, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with (member | member) | (rfl | rfl)
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member
      · trivial
      · trivial)
    (by
      intro value before represented
      have contents := represented.2.1
      rw [input_bytes] at contents
      have groups := ListBytes.read_header layout.hash.scheme.point layout.groups layout.groupCountFits
        layout.points.representation.fits (inputPoints layout value)
        (layout.hash.scheme.message.representation.encoding.encode (inputMessage layout value))
        (layout.coefficients.representation.encoding.encode (inputRows layout value) ++
          layout.hash.scheme.state.representation.encoding.encode (inputState layout value)) before contents
      have rows := ListBytes.read_header layout.hash.flat.attach.values layout.rows layout.rowCountFits
        layout.coefficients.representation.fits (inputRows layout value)
        (layout.hash.scheme.message.representation.encoding.encode (inputMessage layout value) ++
          layout.points.representation.encoding.encode (inputPoints layout value))
        (layout.hash.scheme.state.representation.encoding.encode (inputState layout value)) before
        (by
          change (before.bufs 0).toList = (_ ++ _) ++
            (layout.coefficients.representation.encoding.encode (inputRows layout value) ++ _)
          simpa only [List.append_assoc] using contents)
      simp only [Encoding.encode_length, List.length_append] at groups rows
      simp only [testOperands, values, List.map_append]
      change values (reads 0 _ _) before ++ values (reads 0 _ _) before ++ [1, 1] = _
      rw [groups, rows]
      rfl)

private theorem word_one_iff {value : Nat} (hw : 16 < 2 ^ w) (fits : value < 2 ^ w) :
    BitVec.ofNat w value = (1 : Word w) ↔ value = 1 := by
  constructor
  · intro same
    have numbers := congrArg BitVec.toNat same
    change value % 2 ^ w = 1 % 2 ^ w at numbers
    simpa only [Nat.mod_eq_of_lt fits, Nat.mod_eq_of_lt (show 1 < 2 ^ w by omega)] using numbers
  · rintro rfl; rfl

theorem headers_equal (value : layout.input.Value) : decide (headers layout value = (1, 1)) = shape value.val := by
  have groups : value.val.2.1.length < 2 ^ w := value.property.1.2.1.1.trans_lt layout.groupCountFits
  have rows : value.val.2.2.1.length < 2 ^ w := value.property.1.2.2.1.1.trans_lt layout.rowCountFits
  simp only [headers, Prod.mk.injEq, word_one_iff layout.hash.scheme.wordFits groups,
    word_one_iff layout.hash.scheme.wordFits rows, shape]

def test : Implementation .unit layout.input (DataImplementation.boolLayout w (width_pos layout.hash.scheme.wordFits)) shape where
  preserves _ _ := trivial
  program := ((prepareTest layout).then
    (EncodedEquality.realizer .unit (headerPair layout) layout.hash.scheme.wordFits (compared layout).fits)).viewOutput
      (DataImplementation.boolLayout w (width_pos layout.hash.scheme.wordFits)).representation
      (fun value => ⟨shape value.val, trivial⟩) (by
        intro value
        change [if shape value.val then 1 else 0] = [if decide (headers layout value = (1, 1)) then 1 else 0]
        rw [headers_equal])

theorem test_bounded : (test layout).BoundedBy 47 192 := by
  have packed := code_time_unit_le (testOperands layout)
  have stored := code_descriptionWords_le (testOperands layout)
  rw [testOperands_length] at packed stored
  constructor
  · intro value
    change (Assembly.code (testOperands layout)).staticTime .unit + EncodedEquality.time .unit 2 ≤ _
    rw [EncodedEquality.time_unit]
    omega
  · change descriptionWords (Assembly.code (testOperands layout) ;; EncodedEquality.code 2) ≤ _
    rw [descriptionWords_seq, EncodedEquality.code_descriptionWords]
    omega

theorem test_names : NamesBound (test layout).program.code 5 := by
  have packed := code_names (testOperands layout) 1 (testOperands_sources layout)
  have equality := EncodedEquality.code_names (w := w) 2
  exact ⟨max_le (packed.1.trans (by decide)) equality.registers, max_le (packed.2.trans (by decide)) equality.buffers⟩

theorem test_nameFits : (test layout).program.savedBuffer < 2 ^ w := by
  have := (test_names layout).buffers
  have := layout.hash.scheme.wordFits
  change max 2 (test layout).program.code.memBound < _
  omega

def selector : Implementation .unit layout.input layout.selected (GuardedBranch.select shape) :=
  GuardedBranch.selector (hw := layout.hash.scheme.wordFits) (test layout) (by decide)
    (test_nameFits layout) layout.duplicateFits layout.tagFits

theorem selector_bounded : (selector layout).BoundedBy
    (68 * layout.input.representation.encoding.words + 88) (221 * layout.input.representation.encoding.words + 458) := by
  apply (GuardedBranch.selector_boundedBy (test layout) (test_nameFits layout) layout.duplicateFits layout.tagFits (test_bounded layout)).mono <;> omega
theorem selector_buffers : (selector layout).program.code.memBound ≤ 6 :=
  GuardedBranch.selector_buffers (test layout) (test_nameFits layout) layout.duplicateFits layout.tagFits (test_names layout).buffers
theorem selector_names : NamesAccounted (selector layout).program.code 5 :=
  GuardedBranch.selector_names (test layout) (test_nameFits layout) layout.duplicateFits layout.tagFits (test_names layout).accounted

end Signatures.Runtime.CaliperBackend.SchnorrAGM.HashDispatch
