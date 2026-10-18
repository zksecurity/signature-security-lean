import Signatures.Runtime.Caliper
import Lean

open Caliper Signatures.Runtime.CaliperBackend
open Signatures.Runtime.CaliperBackend.BoundedSource

namespace SignaturesTest.CaliperScalars

private def counter := Layout.counter 8 256 (by decide) (by decide)
private def naturalPair := Natural.pair 256 256 (by decide : 16 < 2 ^ 8) (by decide) (by decide)

private def observe {A B : Type} {input : Layout 8 A} {output : Layout 8 B} {f : A → B}
    (implementation : Implementation .unit input output f) (value : input.Value) :=
  (Caliper.run .unit RandomTape.zero 300 implementation.program.code
    (input.representation.initial value)).map
      (fun (state, time, net, peak) => (state.bufs 0, time, net, peak, state.caps 0, state.caps 1))

private def addition := Natural.add .unit 128 128 (by decide : 16 < 2 ^ 8) (by decide)
private def subtraction := Natural.subtract .unit 256 256 (by decide : 16 < 2 ^ 8) (by decide) (by decide)
private def equality := Natural.equal .unit 256 256 (by decide : 16 < 2 ^ 8) (by decide) (by decide)
private def less := Natural.less .unit 256 256 (by decide : 16 < 2 ^ 8) (by decide) (by decide)

-- The one-word result keeps the two-word allocation. No capacity is erased
-- from the resource account by truncating the buffer's filled length.
example : observe addition ⟨(127, 127), by change _ < _ ∧ _ < _; decide⟩ = some (#[254], 6, 0, 0, 2, 0) := by decide
example : observe subtraction ⟨(0, 255), by change _ < _ ∧ _ < _; decide⟩ = some (#[0], 8, 0, 0, 2, 0) := by decide
example : observe subtraction ⟨(255, 0), by change _ < _ ∧ _ < _; decide⟩ = some (#[255], 8, 0, 0, 2, 0) := by decide
example : observe subtraction ⟨(255, 255), by change _ < _ ∧ _ < _; decide⟩ = some (#[0], 8, 0, 0, 2, 0) := by decide
example : observe subtraction ⟨(200, 150), by change _ < _ ∧ _ < _; decide⟩ = some (#[50], 8, 0, 0, 2, 0) := by decide
example : observe equality ⟨(255, 255), by change _ < _ ∧ _ < _; decide⟩ = some (#[1], 6, 0, 0, 2, 0) := by decide
example : observe equality ⟨(255, 0), by change _ < _ ∧ _ < _; decide⟩ = some (#[0], 6, 0, 0, 2, 0) := by decide
example : observe less ⟨(0, 255), by change _ < _ ∧ _ < _; decide⟩ = some (#[1], 6, 0, 0, 2, 0) := by decide
example : observe less ⟨(255, 0), by change _ < _ ∧ _ < _; decide⟩ = some (#[0], 6, 0, 0, 2, 0) := by decide

-- These are failures of the required capacity predicates, before a natural
-- arithmetic implementation can be constructed; wrapping words are insufficient.
example : ¬ (128 + 129 ≤ 2 ^ 8) := by decide
example : ¬ counter.valid 256 := by change ¬ 256 < 256; decide
example : ¬ (Natural.pair 128 128 (by decide : 16 < 2 ^ 8) (by decide) (by decide)).valid (128, 0) := by change ¬ (128 < 128 ∧ 0 < 128); decide

private def natConstant := Natural.constant .unit (by decide) counter 256 255 (by decide) (by decide) (by decide)
private def boolConstant := DataImplementation.boolean .unit (by decide) naturalPair true (by decide)
private def unitConstant := DataImplementation.unit .unit (by decide) naturalPair (by decide)
example : observe natConstant ⟨0, by change _ < _; decide⟩ = some (#[255], 7, 0, 1, 1, 0) := by decide
example : observe boolConstant ⟨(7, 9), by change _ < _ ∧ _ < _; decide⟩ = some (#[1], 7, -1, 1, 1, 0) := by decide
example : observe unitConstant ⟨(7, 9), by change _ < _ ∧ _ < _; decide⟩ = some (#[], 0, -2, 0, 0, 0) := by decide
example : descriptionWords unitConstant.program.code = 14 := by decide

example : (Encoding.boolean 8 (by decide)).decode [0] = some false := by decide
example : (Encoding.boolean 8 (by decide)).decode [1] = some true := by decide
example : (Encoding.boolean 8 (by decide)).decode [2] = none := by decide
example : (Encoding.boolean 8 (by decide)).decode [] = none := by decide
example : (Encoding.boolean 8 (by decide)).decode [0, 1] = none := by decide

private def select := DataImplementation.select .unit counter (by decide) (by decide)
example : observe select ⟨(true, 255), by change True ∧ _ < _; decide⟩ = some (#[0, 255], 5, 0, 0, 2, 0) := by decide
example : observe select ⟨(false, 255), by change True ∧ _ < _; decide⟩ = some (#[1, 255], 5, 0, 0, 2, 0) := by decide
example : descriptionWords select.program.code = 23 := by decide

private def modulo := Finite.ofNat .unit (by decide) 256 4 (by decide : 16 < 2 ^ 8) (by decide) (by decide)
private def fullDomain := Finite.ofNat .unit (by decide) 256 255 (by decide : 16 < 2 ^ 8) (by decide) (by decide)
private def singleton := Finite.ofNat .unit (by decide) 256 0 (by decide : 16 < 2 ^ 8) (by decide) (by decide)
private def finiteValue := Finite.value .unit 255 (by decide : 16 < 2 ^ 8) (by decide)
private def finiteConstant := Finite.constant .unit (by decide) counter 255 ⟨255, by decide⟩ (by decide) (by decide)

example : observe modulo ⟨254, by change _ < _; decide⟩ = some (#[4], 21, 1, 3, 2, 0) := by decide
example : observe modulo ⟨255, by change _ < _; decide⟩ = some (#[0], 21, 1, 3, 2, 0) := by decide
example : observe modulo ⟨0, by change _ < _; decide⟩ = some (#[0], 21, 1, 3, 2, 0) := by decide
example : observe fullDomain ⟨255, by change _ < _; decide⟩ = some (#[255], 0, 0, 0, 1, 0) := by decide
example : observe singleton ⟨255, by change _ < _; decide⟩ = some (#[0], 21, 1, 3, 2, 0) := by decide
example : observe finiteValue ⟨⟨255, by decide⟩, trivial⟩ = some (#[255], 0, 0, 0, 1, 0) := by decide
example : observe finiteConstant ⟨0, by change _ < _; decide⟩ = some (#[255], 7, 0, 1, 1, 0) := by decide
example : (Finite.layout 4 (by decide : 16 < 2 ^ 8) (by decide)).representation.encoding.decode [5] = none := by decide

-- The source functions retain ordinary Nat/Fin semantics. Their symbolic
-- correctness comes from the implementations, not from the examples above.
example (value : Nat × Nat) (valid : naturalPair.valid value) :
    counter.valid (value.1 - value.2) := subtraction.preserves value valid
example (value : Nat × Nat) (valid : naturalPair.valid value) :
    subtraction.program.time ⟨value, valid⟩ = 8 := Saturating.time_unit _
example (value : Nat × Nat) (valid : naturalPair.valid value) :
    equality.program.time ⟨value, valid⟩ = 6 := rfl

-- Both callees consume the same original pair. The saved input must survive
-- the first call's writes. We then branch on the computed Boolean and carry
-- the computed difference through the selected continuation.
private def paired := equality.pair subtraction (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)
private def yes := Natural.constant .unit (by decide) counter 256 1 (by decide) (by decide) (by decide)
private def no := Implementation.identity (cost := .unit) counter (by decide)
private def choice := (paired.then select).then (yes.branch no (by decide) (by decide) (by decide))

example : observe paired ⟨(200, 150), by change _ < _ ∧ _ < _; decide⟩ =
    some (#[0, 50], 170, 0, 6, 2, 0) := by decide
example : observe choice ⟨(200, 150), by change _ < _ ∧ _ < _; decide⟩ =
    some (#[50], 185, -1, 6, 1, 0) := by decide
example : observe choice ⟨(255, 255), by change _ < _ ∧ _ < _; decide⟩ =
    some (#[1], 192, -1, 6, 1, 0) := by decide
example (value : naturalPair.Value) : paired.program.time value ≤ 170 := by
  have bound := Pairing.time_unit_le equality.program subtraction.program (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) value
  have subtractTime := Saturating.time_unit (Natural.words (w := 8) value.val)
  change subtraction.program.time value = 8 at subtractTime
  change paired.program.time value ≤ 6 + subtraction.program.time value + 52 * 2 + 36 * 1 + 16 * 1 at bound
  omega
example : descriptionWords paired.program.code ≤ 696 :=
  Pairing.descriptionWords_le equality.program subtraction.program (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

private def projection := Implementation.first (cost := .unit) (by decide) counter counter (by decide) (by decide)
example : observe projection ⟨(255, 7), by change _ < _ ∧ _ < _; decide⟩ =
    some (#[255], 8, -1, 1, 1, 0) := by decide
private def otherProjection := Implementation.second (cost := .unit) (by decide) counter counter (by decide) (by decide)
example : observe otherProjection ⟨(255, 7), by change _ < _ ∧ _ < _; decide⟩ =
    some (#[7], 8, -1, 1, 1, 0) := by decide

private def callerState : State 8 :=
  let initial := naturalPair.representation.initial ⟨(200, 150), by change _ < _ ∧ _ < _; decide⟩
  { initial with
    bufs := fun buffer => if buffer = 7 then #[99] else initial.bufs buffer
    caps := fun buffer => if buffer = 7 then 1 else initial.caps buffer }
example : (Caliper.run .unit RandomTape.zero 300 choice.program.code callerState).map
    (fun (state, _, _, _) => (state.bufs 7, state.caps 7, state.caps 1, state.caps 2)) =
    some (#[99], 1, 0, 0) := by decide

example (bound : Nat) (fits : bound + 1 ≤ 256) (value : counter.Value) :
    (Finite.ofNat .unit (by decide) 256 bound (by decide) (by decide) fits).program.time value ≤ 21 := by
  calc
    _ = if bound + 1 = 256 then 0 else 21 := Finite.ofNat_time_unit 256 bound (by decide) (by decide) fits value
    _ ≤ 21 := by split <;> decide

open Lean in
run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``WordBinary.load_exec, ``WordBinary.finish_exec, ``WordBinary.exec,
      ``WordBinary.descriptionFits, ``WordBinary.realizer, ``Saturating.exec,
      ``Saturating.descriptionFits, ``Saturating.realizer, ``Saturating.time_unit,
      ``Encoding.boolean, ``Boolean.constant, ``Boolean.select_bytes, ``Boolean.selectRealizer,
      ``Natural.constant, ``Natural.add, ``Natural.subtract_words, ``Natural.subtract,
      ``Natural.equal, ``Natural.less, ``Finite.operands, ``Finite.ofNat, ``Finite.value,
      ``Finite.constant, ``DataImplementation.unit, ``DataImplementation.boolean,
      ``DataImplementation.select, ``addition, ``subtraction, ``equality, ``less,
      ``natConstant, ``boolConstant, ``unitConstant, ``select, ``modulo, ``fullDomain,
      ``singleton, ``finiteValue, ``finiteConstant, ``WordBinary.time_unit,
      ``Boolean.constant_time_unit, ``Boolean.select_time_unit, ``Natural.add_time_unit,
      ``Natural.subtract_time_unit, ``Natural.equal_time_unit, ``Natural.less_time_unit,
      ``Finite.ofNat_time_unit, ``Finite.ofNat_descriptionWords,
      ``Pairing.swap, ``Pairing.realizer, ``Pairing.swap_time_unit_le,
      ``Pairing.swap_descriptionWords_le, ``Pairing.time_unit_le, ``Pairing.descriptionWords_le,
      ``Implementation.first, ``Implementation.second, ``Implementation.pair,
      ``Implementation.branch, ``paired, ``yes, ``no, ``choice, ``projection, ``otherProjection] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperScalars
