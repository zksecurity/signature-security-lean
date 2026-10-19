import Signatures.Runtime.Caliper.ListIndexBounds
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource

namespace SignaturesTest.CaliperListIndex

private def numbers : ListIndex.Layouts 8 Nat where
  value := Layout.counter 8 256 (by decide) (by decide)
  capacity := 3
  indexBound := 256
  indexPositive := by decide
  indexFits := by decide
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def zeroCapacity : ListIndex.Layouts 8 Nat :=
  { numbers with capacity := 0, countFits := by decide, storageFits := by decide }
private def firstOnly : ListIndex.Layouts 8 Nat :=
  { numbers with indexBound := 1, indexPositive := by decide, indexFits := by decide }
private def tokens : ListIndex.Layouts 8 Unit where
  value := DataImplementation.unitLayout 8
  capacity := 3
  indexBound := 256
  indexPositive := by decide
  indexFits := by decide
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def pairs : ListIndex.Layouts 10 (Nat × Nat) where
  value := (Layout.counter 10 1024 (by decide) (by decide)).prod
    (Layout.counter 10 1024 (by decide) (by decide)) (by decide)
  capacity := 3
  indexBound := 1024
  indexPositive := by decide
  indexFits := by decide
  wordFits := by decide
  countFits := by decide
  storageFits := by decide

private def first : numbers.input.Value := ⟨(0, 99, [2, 5, 7]), by
  change 0 < 256 ∧ 99 < 256 ∧ 3 ≤ 3 ∧ ∀ value ∈ [2, 5, 7], value < 256
  simp⟩
private def middle : numbers.input.Value := ⟨(1, 99, [2, 5, 7]), by
  change 1 < 256 ∧ 99 < 256 ∧ 3 ≤ 3 ∧ ∀ value ∈ [2, 5, 7], value < 256
  simp⟩
private def last : numbers.input.Value := ⟨(2, 99, [2, 5, 7]), by
  change 2 < 256 ∧ 99 < 256 ∧ 3 ≤ 3 ∧ ∀ value ∈ [2, 5, 7], value < 256
  simp⟩
private def missing : numbers.input.Value := ⟨(3, 99, [2, 5, 7]), by
  change 3 < 256 ∧ 99 < 256 ∧ 3 ≤ 3 ∧ ∀ value ∈ [2, 5, 7], value < 256
  simp⟩
private def maxIndex : numbers.input.Value := ⟨(255, 99, [2, 5, 7]), by
  change 255 < 256 ∧ 99 < 256 ∧ 3 ≤ 3 ∧ ∀ value ∈ [2, 5, 7], value < 256
  simp⟩
private def empty : numbers.input.Value := ⟨(0, 99, []), by
  change 0 < 256 ∧ 99 < 256 ∧ 0 ≤ 3 ∧ ∀ value ∈ ([] : List Nat), value < 256
  simp⟩
private def short : numbers.input.Value := ⟨(0, 99, [2]), by
  change 0 < 256 ∧ 99 < 256 ∧ 1 ≤ 3 ∧ ∀ value ∈ [2], value < 256
  simp⟩
private def zeroDefault : numbers.input.Value := ⟨(1, 0, [2]), by
  change 1 < 256 ∧ 0 < 256 ∧ 1 ≤ 3 ∧ ∀ value ∈ [2], value < 256
  simp⟩
private def noSlots : zeroCapacity.input.Value := ⟨(255, 99, []), by
  change 255 < 256 ∧ 99 < 256 ∧ 0 ≤ 0 ∧ ∀ value ∈ ([] : List Nat), value < 256
  simp⟩
private def indexBoundOne : firstOnly.input.Value := ⟨(0, 99, [2, 5, 7]), by
  change 0 < 1 ∧ 99 < 256 ∧ 3 ≤ 3 ∧ ∀ value ∈ [2, 5, 7], value < 256
  simp⟩
private def zeroWidth : tokens.input.Value := ⟨(2, (), [(), (), ()]), by
  exact ⟨by change 2 < 256; decide, trivial, by change 3 ≤ 3; decide, fun _ _ => trivial⟩⟩
private def pairInput : pairs.input.Value := ⟨(1, (99, 98), [(2, 3), (5, 6), (7, 8)]), by
  change 1 < 1024 ∧ (99 < 1024 ∧ 98 < 1024) ∧ 3 ≤ 3 ∧
    ∀ value ∈ [(2, 3), (5, 6), (7, 8)], value.1 < 1024 ∧ value.2 < 1024
  simp⟩

example : ¬ numbers.input.valid (256, 0, []) := by
  intro valid
  have impossible : 256 < 256 := valid.1
  omega
example : ¬ numbers.input.valid (0, 256, []) := by
  intro valid
  have impossible : 256 < 256 := valid.2.1
  omega
example : ¬ numbers.input.valid (0, 0, [1, 2, 3, 4]) := by
  intro valid
  have impossible : 4 ≤ 3 := valid.2.2.1
  omega
example : ¬ numbers.input.valid (0, 0, [256]) := by
  intro valid
  have impossible : 256 < 256 := valid.2.2.2 256 (by simp)
  omega
example : (ListIndex.implementation numbers).program.code.memBound ≤ 6 := ListIndex.buffers numbers
example : NamesAccounted (ListIndex.implementation numbers).program.code 0 := ListIndex.names numbers 0
example : DescriptionFits (ListIndex.implementation numbers).program.code :=
  (ListIndex.implementation numbers).program.description_fits
private theorem bound : (ListIndex.implementation numbers).BoundedBy
    (ListIndex.timeBudget numbers) (ListIndex.codeBudget numbers) := ListIndex.bounded numbers

-- The original arithmetic-language indexing and the Caliper implementation
-- have the same mathematical result, for every primitive interpretation with
-- the stated equality/subtraction semantics, not only the examples below.
example {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type} {cell : Ty Atom}
    (P : Primitives base Op) (eq : Op (.pair .nat .nat) .bool) (sub : Op (.pair .nat .nat) .nat)
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (hsub : ∀ x y, P.execute sub (x, y) = x - y)
    (n : Nat) (default : cell.Value base) (xs : List (cell.Value base)) :
    (index eq sub).denote P (n, default, xs, ()) = (xs[n]?).getD default :=
  index_denote P eq sub heq hsub n default xs

private def run {w : Nat} {V : Type} (layout : ListIndex.Layouts w V) (value : layout.input.Value) :=
  let initial := layout.input.representation.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  (Caliper.run .unit RandomTape.zero 10000 (ListIndex.implementation layout).program.code before).map fun result =>
    (result.1.bufs 0, result.1.bufs 200, result.1.caps 200, result.1.regs 99, result.1.tapePos,
      (List.range 10).all (fun i => result.1.caps (i + 1) == 0))

open Lean in
run_cmd do
  for (value, expected) in [(first, 2), (middle, 5), (last, 7), (missing, 99), (maxIndex, 99),
      (empty, 99), (short, 2), (zeroDefault, 0)] do
    unless run numbers value == some (#[expected], #[77], 4, 91, 9, true) do
      throwError "index lookup failed for {value.val}, expected {expected}"
  unless run zeroCapacity noSlots == some (#[99], #[77], 4, 91, 9, true) do
    throwError "zero-capacity lookup did not retain its runtime default"
  unless run firstOnly indexBoundOne == some (#[2], #[77], 4, 91, 9, true) do
    throwError "lookup incorrectly coupled index and list capacities"
  unless run tokens zeroWidth == some (#[], #[77], 4, 91, 9, true) do
    throwError "zero-word entry lookup failed"
  unless run pairs pairInput == some (#[5, 6], #[77], 4, 91, 9, true) do
    throwError "multiword lookup crossed entry boundaries"
  unless (ListIndex.implementation numbers).program.time short < (ListIndex.implementation numbers).program.time first do
    throwError "the suffix after the first hit must still be scanned and charged"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``ListIndex.body, ``ListIndex.body_accepted, ``ListIndex.body_bounded, ``ListIndex.body_names,
      ``ListIndex.implementation, ``ListIndex.buffers, ``ListIndex.bounded, ``ListIndex.names,
      ``ListIndex.static_bound, ``ListIndex.resources, ``indexStep_value, ``index_denote, ``bound] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperListIndex
