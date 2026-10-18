import Signatures.Runtime.Caliper
import Lean

open Caliper Signatures.Runtime.CaliperBackend

namespace SignaturesTest.CaliperFold

private def word := wordRepresentation 8 (by decide)
private def triple := word.prod (word.prod word (by decide)) (by decide)
private def argument := ListFold.argument word triple word (by decide)
private def step (value : Word 8 × ((Word 8 × (Word 8 × Word 8)) × Word 8)) :=
  (value.2.1.2.1, (value.1, value.2.2))

-- The body uses the incoming accumulator, current entry and saved environment.
-- Every output word comes from an executed indexed read/copy.
private def body : Realizer .unit argument triple step :=
  Assembly.realizer .unit (by decide) argument triple step
    [.read 0 2, .read 0 0, .read 0 4] (by decide) (by rfl)
    (by intro operand member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> simp [Assembly.Operand.NamesFit])
    (by
      intro value state represented operand member
      have size := Assembly.represented_size argument represented
      change (state.bufs 0).size = 5 at size
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> simp [Assembly.Operand.Valid, size])
    (by
      intro value state represented
      have bytes : state.bufs 0 = #[value.1, value.2.1.1, value.2.1.2.1, value.2.1.2.2, value.2.2] := by
        have array := congrArg List.toArray represented.2.1
        simpa [argument, ListFold.argument, triple, word, wordRepresentation, wordEncoding,
          Representation.prod, Encoding.prod, Encoding.checked] using array
      simp [Assembly.values, Assembly.Operand.value, bytes, triple, word, wordRepresentation,
        wordEncoding, Representation.prod, Encoding.prod, Encoding.checked, step])

private def input (capacity : Nat) (countFits : capacity < 256) (storageFits : 1 + capacity + 3 + 2 < 256) :=
  ListFold.frame word triple word capacity countFits (by
    change 1 + capacity * 1 + 3 + 2 * 1 < 256
    omega)
private def fold := ListFold.realizer .unit (by decide) word triple word (by decide) (by decide) body
  (by decide) 3 (by decide) (by decide)

example : body.time (7, ((1, (2, 3)), 99)) = 24 := by decide
example : body.savedBuffer = 2 := by decide

example : (Caliper.run .unit RandomTape.zero 3000 fold.code
    ((input 3 (by decide) (by decide)).initial (⟨[], by decide⟩, ((1, (2, 3)), 99)))).map
    (fun (state, time, net, peak) => (state.bufs 0, time, net, peak)) =
    some (#[1, 2, 3], 26, -5, 3) := by decide
example : (Caliper.run .unit RandomTape.zero 3000 fold.code
    ((input 3 (by decide) (by decide)).initial (⟨[7], by decide⟩, ((1, (2, 3)), 99)))).map
    (fun (state, time, net, peak) => (state.bufs 0, time, net, peak)) =
    some (#[2, 7, 99], 297, -5, 10) := by decide
example : (Caliper.run .unit RandomTape.zero 3000 fold.code
    ((input 3 (by decide) (by decide)).initial (⟨[7, 11], by decide⟩, ((1, (2, 3)), 99)))).map
    (fun (state, time, _, _) => (state.bufs 0, time)) = some (#[7, 11, 99], 540) := by decide

private def fullInput : State 8 :=
  let initial := (input 3 (by decide) (by decide)).initial (⟨[7, 11, 13], by decide⟩, ((1, (2, 3)), 99))
  { initial with
    bufs := fun buffer => if buffer = 7 then #[77] else initial.bufs buffer
    caps := fun buffer => if buffer = 7 then 1 else initial.caps buffer }

-- Maximum-length traversal reaches the capacity-zero projection. Unrelated
-- storage survives; both scratch and the saved tail/environment are released.
example : (Caliper.run .unit RandomTape.zero 3000 fold.code fullInput).map
    (fun (state, time, net, peak) => ((state.bufs 0, state.bufs 7),
      (state.caps 1, state.caps 2), (time, net, peak))) =
    some ((#[11, 13, 99], #[77]), (0, 0), (753, -5, 10)) := by decide +kernel

private def emptyFold := ListFold.realizer .unit (by decide) word triple word (by decide) (by decide) body
  (by decide) 0 (by decide) (by decide)
example : (Caliper.run .unit RandomTape.zero 300 emptyFold.code
    ((input 0 (by decide) (by decide)).initial (⟨[], by decide⟩, ((1, (2, 3)), 99)))).map
    (fun (state, time, _, _) => (state.bufs 0, time)) = some (#[1, 2, 3], 24) := by decide

example (value : BoundedList (Word 8) 3 × ((Word 8 × (Word 8 × Word 8)) × Word 8)) :
    fold.time value ≤ 1437 :=
  ListFold.time_unit_le step body.time 24 (fun _ => by change 24 ≤ 24; decide) 2 1 3 1 3 value.1.val value.2.1 value.2.2
example : descriptionWords fold.code ≤ 5783 := by
  have bound := ListFold.code_descriptionWords_le body.code 2 1 3 1 3
  exact bound

-- Entries may themselves be restricted mathematical source values. Decoding
-- rejects an out-of-domain entry even if the list's own length fits.
private def boundedEntry := BoundedSource.Layout.counter 8 10 (by decide) (by decide)
private def boundedList := boundedEntry.boundedList 2 (by decide) (by decide)
example : (boundedList.representation.encoding.decode [1, 7, 0]).map Subtype.val = some [7] := by decide
example : boundedList.representation.encoding.decode [1, 11, 0] = none := by decide

private def wordLayout := BoundedSource.Layout.all word
private def stateLayout := BoundedSource.Layout.all triple
private def sourceBody : BoundedSource.Implementation .unit
    (BoundedSource.FoldImplementation.bodyInput wordLayout stateLayout wordLayout (by decide)) stateLayout step where
  preserves _ _ := trivial
  program := (body.viewInput _
    (fun value : {_value : Word 8 × ((Word 8 × (Word 8 × Word 8)) × Word 8) // True ∧ True ∧ True} => value.val)
    (fun _ => rfl)).viewOutput _ _ (fun _ => rfl)
private def sourceFold := BoundedSource.FoldImplementation.compile wordLayout stateLayout wordLayout (by decide)
  sourceBody (by decide) (by decide) (by decide) 3 (by decide) (by decide)

-- Connecting the unbounded mathematical source types introduces no new
-- executable callback or alternative implementation of the finished fold.
example : sourceFold.program.code = fold.code := rfl
example : BoundedSource.FoldImplementation.sourceFold step ([7, 11, 13], ((1, (2, 3)), 99)) =
    (11, (13, 99)) := rfl

open Lean in
run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``body, ``sourceBody, ``sourceFold, ``ListFold.prepare_exec, ``Reorder.realizer, ``ListFold.exec, ``ListFold.realizer,
      ``ListFold.code_descriptionFits, ``ListFold.time_unit_le, ``ListFold.code_descriptionWords_le,
      ``BoundedSource.listView, ``BoundedSource.FoldImplementation.source_result,
      ``BoundedSource.FoldImplementation.preserves, ``BoundedSource.FoldImplementation.compile] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperFold
