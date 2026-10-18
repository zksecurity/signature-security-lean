import Signatures.Runtime.Caliper.EncodedEquality
import Lean

open Caliper Signatures.Runtime.CaliperBackend

namespace SignaturesTest.CaliperEquality

private def word := wordRepresentation 8 (by decide)
private def pair := word.prod word (by decide)
private def empty : Representation 8 Unit := ⟨Encoding.unit 8, by decide⟩

private def observe {A : Type} [DecidableEq A] (representation : Representation 8 A)
    (fits : representation.encoding.words + representation.encoding.words < 2 ^ 8) (left right : A) := do
  let program := EncodedEquality.realizer .unit representation (by decide) fits
  let initial := (representation.prod representation fits).initial (left, right)
  let before := { initial with
    bufs := fun buffer => if buffer = 200 then #[77] else initial.bufs buffer
    caps := fun buffer => if buffer = 200 then 1 else initial.caps buffer }
  let (state, time, net, peak) ← Caliper.run .unit RandomTape.zero 128 program.code before
  pure ((state.bufs 0, state.bufs 200), (time, net, peak, state.caps 0))

example : observe word (by decide) 255 255 = some ((#[1], #[77]), (9, -1, 0, 1)) := by decide +kernel
example : observe word (by decide) 0 255 = some ((#[0], #[77]), (9, -1, 0, 1)) := by decide +kernel
-- Both positions matter; a comparison of only the first word is insufficient.
example : observe pair (by decide) (5, 7) (5, 8) = some ((#[0], #[77]), (15, -3, 0, 1)) := by decide +kernel
example : observe pair (by decide) (5, 7) (6, 7) = some ((#[0], #[77]), (15, -3, 0, 1)) := by decide +kernel
example : observe pair (by decide) (5, 7) (5, 7) = some ((#[1], #[77]), (15, -3, 0, 1)) := by decide +kernel
-- A zero-word injective encoding has only one represented value. The Boolean
-- result still acquires and initializes its own, charged output word.
example : observe empty (by decide) () () = some ((#[1], #[77]), (3, 1, 1, 1)) := by decide +kernel

example : descriptionWords (EncodedEquality.code (w := 8) 2) = 73 := EncodedEquality.code_descriptionWords 2
example : NamesBound (EncodedEquality.code (w := 8) 100) 5 := EncodedEquality.code_names 100

open Lean in
run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``WordEquality.equalSlices_eq, ``WordEquality.step_exec, ``WordEquality.scan_exec,
      ``WordEquality.scan_descriptionWords, ``WordEquality.scan_descriptionFits,
      ``EncodedEquality.finish_exec, ``EncodedEquality.code_exec, ``EncodedEquality.equalSlices_encoding,
      ``EncodedEquality.realizer, ``EncodedEquality.implementation, ``EncodedEquality.implementation_boundedBy,
      ``EncodedEquality.implementation_names] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperEquality
