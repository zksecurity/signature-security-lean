import Proofs.Runtime.Caliper.SchnorrAGMSigningArithmeticBounds
import Proofs.Runtime.Caliper.EncodedConstant
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrAGMSigningArithmetic

-- Modular words test the executed routing and resource contracts. The generic
-- field/group theorem separately identifies the original signing arithmetic.
private instance : SMul (Word 16) (Word 16) := ⟨fun scalar point => scalar * point⟩
private def scheme : CaliperBackend.SchnorrAGM.Layouts 16 Nat (Word 16) (Word 16) 1 1 where
  scalar := Layout.all (wordRepresentation 16 (by decide))
  point := Layout.all (wordRepresentation 16 (by decide))
  message := Layout.counter 16 256 (by decide) (by decide)
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def layout : CaliperBackend.SchnorrAGM.Signing.Layouts 16 Nat (Word 16) (Word 16) 1 1 where
  scheme := scheme
  storageFits := by decide

private def scale : Implementation .unit layout.arithmetic.scaleArgs scheme.point (fun input => input.1 • input.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .mul (by decide)).viewInput layout.arithmetic.scaleArgs.representation
    (fun input => input.val) (fun _ => rfl)).viewOutput scheme.point.representation
      (fun input => ⟨input.val.1 * input.val.2, trivial⟩) (fun _ => rfl)
private def sub : Implementation .unit layout.arithmetic.points scheme.point (fun input => input.1 - input.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .sub (by decide)).viewInput layout.arithmetic.points.representation
    (fun input => input.val) (fun _ => rfl)).viewOutput scheme.point.representation
      (fun input => ⟨input.val.1 - input.val.2, trivial⟩) (fun _ => rfl)
private def zero : Implementation .unit scheme.scalar scheme.scalar (fun _ => 0) :=
  Implementation.constant scheme.scalar scheme.scalar ⟨0, trivial⟩ scheme.wordFits
private def negArgs : Implementation .unit scheme.scalar scheme.affine (fun input => (0, input)) :=
  zero.pair (Implementation.identity scheme.scalar (by decide)) (by decide) scheme.wordFits
    (by decide) (by decide) (by decide) (by decide) scheme.affine.representation.fits
private def negate : Implementation .unit scheme.scalar scheme.scalar Neg.neg :=
  (negArgs.then sub).castFunction (by funext input; exact BitVec.zero_sub input)
private theorem scaleBound : scale.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private theorem subBound : sub.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private theorem negateBound : negate.BoundedBy 118 631 := by
  have zeroBound := Implementation.constant_bounded scheme.scalar scheme.scalar ⟨0, trivial⟩ scheme.wordFits
  have paired : negArgs.BoundedBy 112 603 := by
    apply (Implementation.pair_boundedBy zero (Implementation.identity scheme.scalar (by decide))
      scheme.wordFits (by decide) (by decide) (by decide) (by decide) scheme.affine.representation.fits
      zeroBound (Implementation.identity_boundedBy scheme.scalar (by decide))).mono <;> decide
  apply ((paired.then subBound).castFunction _).mono <;> decide
private theorem scaleNames : NamesBound scale.program.code 3 := ⟨by decide, by decide⟩
private theorem subNames : NamesBound sub.program.code 3 := ⟨by decide, by decide⟩
private theorem negateNames : NamesBound negate.program.code 3 := ⟨by decide, by decide⟩

open CaliperBackend.SchnorrAGM.Signing.Arithmetic
private def program := implementation layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide)
private theorem bounded : program.BoundedBy (timeBudget layout 6 6 118) (codeBudget layout 27 27 631) :=
  CaliperBackend.SchnorrAGM.Signing.Arithmetic.bounded layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers
    (by decide) scaleBound subBound negateBound
private theorem named : NamesAccounted program.program.code 3 :=
  names layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide) 3
    scaleNames.accounted subNames.accounted negateNames.accounted
private theorem bufferBound : program.program.code.memBound ≤ 6 :=
  buffers layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide)
private theorem accepted : DescriptionFits program.program.code := program.program.description_fits

private theorem valid_iff (c z g pk : Word 16) (message : Nat)
    (entries : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16)))
    (basis : List (Word 16 × Word 16)) (signed : List Nat) (malformed bad : Bool) :
    layout.input.valid ((c, z), g, pk, message, entries, basis, signed, malformed, bad) ↔
      message < 256 ∧ (entries.length ≤ 3 ∧ ∀ entry ∈ entries, entry.1.1 < 256) ∧
        basis.length ≤ 3 ∧ (signed.length ≤ 1 ∧ ∀ message ∈ signed, message < 256) := by
  change ((True ∧ True) ∧ True ∧ True ∧ message < 256 ∧
    (entries.length ≤ 3 ∧ ∀ entry ∈ entries, (entry.1.1 < 256 ∧ True) ∧ (True ∧ True ∧ True ∧ True)) ∧
    (basis.length ≤ 3 ∧ ∀ pair ∈ basis, True ∧ True) ∧ (signed.length ≤ 1 ∧ ∀ message ∈ signed, message < 256) ∧ True ∧ True) ↔ _
  simp only [true_and, and_true, implies_true]

private def initial : layout.input.Value :=
  ⟨((2, 11), 3, 5, 7, [((5, 6), (1, true, 13, 14))], [(1, 0), (0, 1)], [], false, false), by rw [valid_iff]; decide⟩
private def changed : layout.input.Value :=
  ⟨((3, 19), 2, 7, 8, [], [], [], false, true), by rw [valid_iff]; decide⟩
private def full : layout.input.Value :=
  ⟨((65535, 2), 5, 3, 255,
    [((3, 4), (2, true, 9, 10)), ((3, 4), (8, true, 11, 12)), ((5, 6), (1, false, 13, 14))],
    [(1, 0), (0, 1), (5, 7)], [9], true, true), by rw [valid_iff]; decide⟩
private def zeroChallenge : layout.input.Value :=
  ⟨((0, 0), 5, 3, 0, [], [], [], true, false), by rw [valid_iff]; decide⟩

example : ¬ layout.input.valid ((0, 0), 1, 1, 256, [], [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ((0, 0), 1, 1, 0, [], List.replicate 4 (0, 0), [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ((0, 0), 1, 1, 0, [], [], [1, 2], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ((0, 0), 1, 1, 0, List.replicate 4 ((0, 0), (0, false, 0, 0)), [], [], false, false) := by rw [valid_iff]; decide

private theorem memory (tape : RandomTape 16) (input : layout.input.Value) (before : State 16)
    (holds : layout.input.representation.Holds input before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape program.program.code before after (program.program.time input) net peak ∧
      layout.work.representation.Holds ⟨value input.val, program.preserves input.val input.property⟩ after ∧
      program.program.time input ≤ timeBudget layout 6 6 118 ∧
      ∀ between, (Caliper.Reaches .unit tape program.program.code before between ∨ between = after) →
        (staticWords program.program.code registers buffers : Int) + between.liveMem (max buffers program.program.code.memBound) ≤
          5 * codeBudget layout 27 27 631 + 12 + registers + 3 * buffers + before.liveMem buffers + timeBudget layout 6 6 118 :=
  resources layout trivial scale sub negate scaleNames.buffers subNames.buffers negateNames.buffers (by decide)
    scaleBound subBound negateBound scaleNames.accounted subNames.accounted negateNames.accounted tape input before holds
    registers buffers initialRegisters initialBuffers

private def execute (input : layout.input.Value) :=
  let initial := layout.input.representation.initial input
  let before := { initial with
    bufs := fun b => if b = 200 then #[77] else initial.bufs b
    caps := fun b => if b = 200 then 4 else initial.caps b
    regs := fun r => if r = 99 then 91 else initial.regs r
    tapePos := 9 }
  (Caliper.run .unit RandomTape.zero 1000000 program.program.code before).map fun result =>
    (result.1.bufs 0, result.1.bufs 200, result.1.caps 200, result.1.regs 99, result.1.tapePos,
      (List.range 30).all (fun i => result.1.caps (i + 1) == 0), decide (result.2.1 ≤ timeBudget layout 6 6 118))

open Lean in
run_cmd do
  let oneTable : Array (Word 16) := #[1, 5, 6, 1, 1, 13, 14] ++ Array.replicate 12 0
  let emptyTable : Array (Word 16) := Array.replicate 19 0
  unless execute initial == some
      (#[7, 23, 2, 0, 0, 0] ++ oneTable ++ #[23, 11, 11, 65534, 7, 2, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
        #[77], 4, 91, 9, true, true) do
    throwError "signing arithmetic lost commitment, response, affine coefficient, state, framing, scratch release or time bound"
  unless execute changed == some
      (#[8, 17, 3, 0, 0, 0] ++ emptyTable ++ #[17, 19, 19, 65533, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        #[77], 4, 91, 9, true, true) do
    throwError "signing arithmetic ignored changed runtime scalars, points, message or bad flag"
  unless execute full == some
      (#[255, 13, 65535, 0, 0, 0, 3, 3, 4, 2, 1, 9, 10, 3, 4, 8, 1, 11, 12, 5, 6, 1, 0, 13, 14,
          13, 2, 2, 1, 255, 3, 1, 0, 0, 1, 5, 7, 1, 9, 1, 1], #[77], 4, 91, 9, true, true) do
    throwError "signing arithmetic lost wraparound, full histories, duplicate cache entries or flags"
  unless execute zeroChallenge == some
      (#[0, 0, 0, 0, 0, 0] ++ emptyTable ++ #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
        #[77], 4, 91, 9, true, true) do
    throwError "signing arithmetic failed on zero scalars or changed malformed state"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``arguments, ``computed, ``finish, ``implementation, ``source_original,
      ``CaliperBackend.SchnorrAGM.Signing.Arithmetic.bounded, ``resources, ``names, ``buffers,
      ``bounded, ``named, ``bufferBound, ``accepted, ``memory] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrAGMSigningArithmetic
