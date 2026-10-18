import Signatures.Runtime.Caliper
import Lean

open Caliper Signatures.Runtime.CaliperBackend

namespace SignaturesTest.CaliperLists

private def word := wordRepresentation 8 (by decide)
private def unit : Representation 8 Unit := ⟨Encoding.unit 8, by decide⟩
private def two := word.boundedList 2 (by decide) (by decide)
private def three := word.boundedList 3 (by decide) (by decide)
private def consInput := word.prod two (by decide)
private def empty := ListConstruct.emptyRealizer .unit (by decide) unit word 2 (by decide) (by decide) (by decide)
private def prepend := ListConstruct.realizer .unit (by decide) word 2 (by decide) (by decide) (by decide)
private def split := ListDestruct.realizer .unit (by decide) word 2 (by decide) (by decide) (by decide)
private def grow := ListCapacity.realizer .unit (by decide) word 2 5 (by decide) (by decide) (by decide) (by decide)

-- Empty construction charges the full reserved capacity and releases scratch.
example : (Caliper.run .unit RandomTape.zero 300 empty.code (unit.initial ())).map
    (fun (state, time, net, peak) => (state.bufs 0, state.caps 1, time, net, peak)) =
    some (#[0, 0, 0], 0, 21, 3, 6) := by decide

-- The same code prepends to partial and full input lists; the stored length
-- changes at execution time, and unused output slots retain canonical zeros.
example : (Caliper.run .unit RandomTape.zero 300 prepend.code
    (consInput.initial (42, ⟨[7], by decide⟩))).map
    (fun (state, time, net, peak) => (state.bufs 0, time, net, peak)) =
    some (#[2, 42, 7, 0], 37, 0, 4) := by decide
example : (Caliper.run .unit RandomTape.zero 300 prepend.code
    (consInput.initial (42, ⟨[7, 11], by decide⟩))).map
    (fun (state, time, _, _) => (state.bufs 0, time)) =
    some (#[3, 42, 7, 11], 37) := by decide

-- List case analysis reads the length, not a host-language list selector.
example : (Caliper.run .unit RandomTape.zero 400 split.code
    (three.initial ⟨[], by decide⟩)).map
    (fun (state, time, net, peak) => (state.bufs 0, state.caps 1, time, net, peak)) =
    some (#[0, 0, 0, 0, 0], 0, 37, 1, 6) := by decide
example : (Caliper.run .unit RandomTape.zero 400 split.code
    (three.initial ⟨[42, 7, 11], by decide⟩)).map
    (fun (state, time, net, peak) => (state.bufs 0, time, net, peak)) =
    some (#[1, 42, 2, 7, 11], 46, 1, 6) := by decide
example : (Caliper.run .unit RandomTape.zero 400 split.code
    (three.initial ⟨[42], by decide⟩)).map
    (fun (state, time, _, _) => (state.bufs 0, time)) =
    some (#[1, 42, 0, 0, 0], 46) := by decide

private def pair := word.prod word (by decide)
private def pairList := pair.boundedList 2 (by decide) (by decide)
private def splitPairs := ListDestruct.realizer .unit (by decide) pair 1 (by decide) (by decide) (by decide)
example : (Caliper.run .unit RandomTape.zero 500 splitPairs.code
    (pairList.initial ⟨[(7, 11)], by decide⟩)).map
    (fun (state, time, _, _) => (state.bufs 0, time)) =
    some (#[1, 7, 11, 0, 0, 0], 54) := by decide

-- Zero-word elements still carry a meaningful, bounded length header.
private def unitList := unit.boundedList 2 (by decide) (by decide)
private def splitUnits := ListDestruct.realizer .unit (by decide) unit 1 (by decide) (by decide) (by decide)
example : (Caliper.run .unit RandomTape.zero 200 splitUnits.code
    (unitList.initial ⟨[(), ()], by decide⟩)).map
    (fun (state, time, _, _) => (state.bufs 0, time)) = some (#[1, 1], 22) := by decide

-- Widening pays for all new padding; it preserves the mathematical list.
example : (Caliper.run .unit RandomTape.zero 500 grow.code
    (two.initial ⟨[42], by decide⟩)).map
    (fun (state, time, net, peak) => (state.bufs 0, time, net, peak)) =
    some (#[1, 42, 0, 0, 0, 0], 45, 3, 9) := by decide
example : three.encoding.decode [4, 42, 7, 11] = none := by decide

-- These are uniform symbolic bounds, including arbitrary element encodings;
-- generated code grows with capacity, not with the number of possible values.
example (entryWords capacity : Nat) :
    (ListConstruct.consCode (w := 8) entryWords capacity).staticTime .unit ≤
      8 * (1 + (capacity + 1) * entryWords) + 5 := ListConstruct.consCode_time_unit_le _ _
example (entryWords capacity : Nat) (values : List (Word 8)) :
    ListDestruct.time (w := 8) .unit entryWords capacity values ≤
      8 * ListDestruct.outputWords entryWords capacity + 7 := ListDestruct.time_unit_le _ _ _
example : descriptionWords prepend.code ≤ 142 := ListConstruct.consCode_descriptionWords_le 1 2
example : descriptionWords split.code ≤ 319 := ListDestruct.code_descriptionWords_le 1 2

-- Original source lists remain unbounded mathematical types. The implementation
-- proves preservation of the represented capacity, rather than assuming it.
private def sourceCons := BoundedSource.ListImplementation.cons .unit (by decide) word 2 (by decide) (by decide) (by decide)
example : sourceCons.program.code = prepend.code := rfl
example (head : Word 8) (tail : List (Word 8)) (valid : tail.length ≤ 2) :
    (head :: tail).length ≤ 3 := sourceCons.preserves (head, tail) ⟨trivial, valid⟩
private def sourceCases := BoundedSource.ListImplementation.cases .unit (by decide) word 2 (by decide) (by decide) (by decide)
example : sourceCases.program.code = split.code := rfl
example (values : List (Word 8)) (valid : values.length ≤ 3) :
    BoundedSource.ListImplementation.caseValid 2 (BoundedSource.ListImplementation.caseList values) :=
  sourceCases.preserves values valid

open Lean in
run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``CellArithmetic.exec, ``CellArithmetic.exec_at,
      ``ListConstruct.emptyRealizer, ``ListConstruct.realizer, ``ListConstruct.consCode_time_unit_le,
      ``ListConstruct.consCode_descriptionWords_le, ``ListDestruct.realizer, ``ListDestruct.time_unit_le,
      ``ListDestruct.code_descriptionWords_le, ``ListCapacity.realizer, ``ListCapacity.time_unit_le,
      ``ListCapacity.descriptionWords_le, ``Realizer.viewInput, ``BoundedSource.ListImplementation.empty,
      ``BoundedSource.ListImplementation.cons, ``BoundedSource.ListImplementation.cases,
      ``BoundedSource.ListImplementation.widen] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperLists
