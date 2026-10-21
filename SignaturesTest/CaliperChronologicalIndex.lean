import Signatures.Runtime.Caliper.ChronologicalIndex
import Lean

open Caliper Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperChronologicalIndex

private def layout (capacity : Fin 4) : ChronologicalIndex.Layouts 12 (Nat × Nat) Nat where
  key := (Layout.counter 12 256 (by decide) (by decide)).prod
    (Layout.counter 12 256 (by decide) (by decide)) (by decide)
  value := Layout.counter 12 256 (by decide) (by decide)
  capacity := capacity.val
  wordFits := by decide
  countFits := by have := capacity.isLt; omega
  storageFits := by change 16 * (4 + (capacity.val + 2) * (2 + 1) + 2) < 4096; have := capacity.isLt; omega
private instance (capacity : Fin 4) (value : (Nat × Nat) × List ((Nat × Nat) × Nat)) :
    Decidable ((layout capacity).input.valid value) := by
  change Decidable ((value.1.1 < 256 ∧ value.1.2 < 256) ∧ value.2.length ≤ capacity.val ∧
    ∀ entry ∈ value.2, (entry.1.1 < 256 ∧ entry.1.2 < 256) ∧ entry.2 < 256)
  infer_instance
private def run (capacity : Fin 4) (key : Nat × Nat) (entries : List ((Nat × Nat) × Nat)) := do
  let value : (layout capacity).input.Value ← if valid : (layout capacity).input.valid (key, entries)
    then some ⟨(key, entries), valid⟩ else none
  let initial := (layout capacity).input.representation.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  let result ← Caliper.run .unit RandomTape.zero 100000 (ChronologicalIndex.implementation (layout capacity)).program.code before
  pure (((layout capacity).result.representation.encoding.decode (result.1.bufs 0).toList).map Subtype.val,
    result.1.bufs 200, result.1.caps 200, result.1.regs 99, result.1.tapePos,
    (List.range 20).all (fun i => result.1.caps (i + 1) == 0),
    decide ((ChronologicalIndex.implementation (layout capacity)).program.time value ≤ ChronologicalIndex.timeBudget (layout capacity)))

open Lean in
run_cmd do
  let target := ((2, 3), 10)
  let other := ((2, 4), 20)
  for (entries, expected) in [([], (false, 0)), ([target], (true, 0)), ([other], (false, 1)),
      ([target, other], (true, 1)), ([other, target], (true, 0)),
      ([target, other, target], (true, 0)), ([other, target, other], (true, 1)),
      ([other, other, other], (false, 3))] do
    unless run 3 (2, 3) entries == some (some expected, #[77], 4, 91, 9, true, true) do
      throwError "chronological scan lost its oldest match, missing index or caller state"
  unless run 0 (2, 3) [] == some (some (false, 0), #[77], 4, 91, 9, true, true) do
    throwError "zero-capacity scan did not terminate with index zero"
  unless run 3 (256, 3) [] == none && run 3 (2, 3) (List.replicate 4 target) == none &&
      run 3 (2, 3) [((2, 3), 256)] == none do
    throwError "scan accepted an invalid encoding or excess entries"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``ChronologicalIndex.fold_value, ``ChronologicalIndex.body, ``ChronologicalIndex.body_budget,
      ``ChronologicalIndex.accepted, ``ChronologicalIndex.bounded, ``ChronologicalIndex.buffers,
      ``ChronologicalIndex.names] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperChronologicalIndex
