import Proofs.Runtime.Caliper
import Lean

open Caliper Signatures.Runtime.CaliperBackend

namespace SignaturesTest.CaliperControl

private def word := wordRepresentation 8 (by decide)
private def pair := word.prod word (by decide)
private def tagged := word.sum pair (by decide) (by decide)
private def duplicated := duplicateRealizer .unit (by decide) word (by decide) (by decide)
private def injectLeft := inlRealizer .unit (by decide) word pair (by decide) (by decide)
private def injectRight := inrRealizer .unit (by decide) word pair (by decide) (by decide)

-- New construction pays for both copied words and for tagged-union padding.
example : (Caliper.run .unit RandomTape.zero 200 duplicated.code (word.initial 42)).map
    (fun (state, time, net, peak) => (state.bufs 0, state.caps 1, time, net, peak)) =
    some (#[42, 42], 0, 16, 1, 3) := by decide
example : (Caliper.run .unit RandomTape.zero 200 injectLeft.code (word.initial 42)).map
    (fun (state, time, net, peak) => (state.bufs 0, state.caps 1, time, net, peak)) =
    some (#[0, 42, 0], 0, 22, 2, 5) := by decide
example : (Caliper.run .unit RandomTape.zero 200 injectRight.code (pair.initial (7, 11))).map
    (fun (state, time, _, _) => (state.bufs 0, time)) = some (#[1, 7, 11], 23) := by decide

-- A slice cannot read the scratch buffer while construction replaces it.
example : ¬ Assembly.Valid 1 (word.initial 42) [Assembly.Operand.read 1 0] := by
  simp [Assembly.Valid, Assembly.Operand.Valid]
example : (Caliper.run .unit RandomTape.zero 100
    (Assembly.code [Assembly.Operand.read 0 256]) (word.initial 42)).map
    (fun (state, _, _, _) => state.bufs 0) = some #[42] := by decide
-- The physical word index above wraps; the proof contract rejects it.
example : ¬ Assembly.Valid 1 (word.initial 42) [Assembly.Operand.read 0 256] := by
  simp [Assembly.Valid, Assembly.Operand.Valid]

private def projectRight := secondRealizer .unit (by decide) word word (by decide) (by decide)
private def dispatch := branchRealizer .unit (by decide) word pair word
  (complementRealizer .unit) projectRight (by decide) (by decide)

-- Unequal payload sizes exercise both tag branches and their actual copy costs.
example : (Caliper.run .unit RandomTape.zero 200 dispatch.code (tagged.initial (.inl 42))).map
    (fun (state, time, _, _) => (state.bufs 0, time)) = some (#[213], 13) := by decide
example : (Caliper.run .unit RandomTape.zero 200 dispatch.code (tagged.initial (.inr (7, 11)))).map
    (fun (state, time, _, _) => (state.bufs 0, time)) = some (#[11], 26) := by decide

private def retained := (complementRealizer .unit).retain (by decide) pair (by decide)
  (by decide) (by decide) (by decide)
private def nested := retained.retain (by decide) word (by decide) (by decide) (by decide) (by decide)
private def retainedInput := (word.prod pair (by decide)).initial (42, (11, 13))
private def nestedInput : State 8 :=
  let input := ((word.prod pair (by decide)).prod word (by decide)).initial ((42, (11, 13)), 99)
  { input with
    bufs := fun buffer => if buffer = 7 then #[77] else input.bufs buffer
    caps := fun buffer => if buffer = 7 then 1 else input.caps buffer }

-- Both wrappers release scratch and saved buffers. The nested wrapper chooses
-- buffer 3 because its callee already uses buffer 2 for retained state.
example : (complementRealizer .unit).savedBuffer = 2 := by decide
example : retained.savedBuffer = 3 := by decide
example : (Caliper.run .unit RandomTape.zero 400 retained.code retainedInput).map
    (fun (state, time, net, peak) => ((state.bufs 0, state.caps 1, state.caps 2), (time, net, peak))) =
    some ((#[213, 11, 13], 0, 0), (43, 0, 5)) := by decide
example : (Caliper.run .unit RandomTape.zero 1000 nested.code nestedInput).map
    (fun (state, time, net, peak) => ((state.bufs 0, state.bufs 7),
      (state.caps 2, state.caps 3), (time, net, peak))) =
    some ((#[213, 11, 13, 99], #[77]), (0, 0), (103, 0, 5)) := by decide
example : ¬ (max 2 (Stmt.memAllocI (w := 8) 255 0).memBound < 2 ^ 8) := by decide

private def continueBody := inrRealizer .unit (by decide) word word (by decide) (by decide)
private def returnBody := inlRealizer .unit (by decide) word word (by decide) (by decide)
private def continuing (fuel : Nat) := loopRealizer .unit (by decide) word word (by decide) (by decide)
  continueBody (complementRealizer .unit) fuel
private def returning (fuel : Nat) := loopRealizer .unit (by decide) word word (by decide) (by decide)
  returnBody (complementRealizer .unit) fuel

-- Exhaustion executes stop; early return skips it. The generated code includes
-- all copies of the body even though early exit executes just the first copy.
example : (Caliper.run .unit RandomTape.zero 1000 (continuing 2).code (word.initial 42)).map
    (fun (state, time, _, _) => (state.bufs 0, time)) = some (#[213], 53) := by decide
example : (Caliper.run .unit RandomTape.zero 1000 (returning 3).code (word.initial 42)).map
    (fun (state, time, _, _) => (state.bufs 0, time)) = some (#[42], 25) := by decide
example : (Caliper.run .unit RandomTape.zero 100 (returning 0).code (word.initial 42)).map
    (fun (state, time, _, _) => (state.bufs 0, time)) = some (#[213], 3) := by decide
example : descriptionWords (continuing 2).code = 318 := by
  exact (loopRealizer_descriptionWords .unit (by decide) word word (by decide) (by decide)
    continueBody (complementRealizer .unit) 2).trans (by decide)

open Lean in
run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Assembly.emit_exec, ``Assembly.code_exec, ``Assembly.realizer,
      ``Assembly.code_time_unit_le, ``Assembly.code_descriptionWords_le,
      ``duplicateRealizer, ``inlRealizer, ``inrRealizer, ``branchRealizer,
      ``Realizer.retain, ``Realizer.retain_time_unit_le, ``Realizer.retain_descriptionWords_le, ``loopRealizer,
      ``loopFunction_eq_source, ``loopRealizer_time_le, ``loopRealizer_descriptionWords] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperControl
