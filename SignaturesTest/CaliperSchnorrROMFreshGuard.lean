import Proofs.Runtime.Caliper.SchnorrROMFreshGuardBounds
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMFreshGuard
open SchnorrROMTape SchnorrROM

private def layout (capacity : Fin 7) : Layouts 16 (Nat × Nat) where
  scalar := (Layout.counter 16 256 (by decide) (by decide)).prod
    (Layout.counter 16 256 (by decide) (by decide)) (by decide)
  capacity := capacity.val
  wordFits := by decide
  countFits := by have := capacity.isLt; omega
  storageFits := by change 16 * (4 + (capacity.val + 2) * (2 + 2)) < 65536; have := capacity.isLt; omega
private instance (capacity : Fin 7) (value : Nat × ((Nat × Nat) × List (Schnorr.TapeCell (Nat × Nat)))) :
    Decidable ((FreshGuard.input (layout capacity)).valid value) := by
  change Decidable (value.1 < 65536 ∧ (value.2.1.1 < 256 ∧ value.2.1.2 < 256) ∧
    value.2.2.length ≤ capacity.val ∧ ∀ entry ∈ value.2.2,
      entry.1 < 65536 ∧ (entry.2.1.1 < 256 ∧ entry.2.1.2 < 256) ∧ entry.2.2 < 65536)
  infer_instance
private def run (capacity : Fin 7) (slot : Nat) (replacement : Nat × Nat) (cells : List (Schnorr.TapeCell (Nat × Nat))) := do
  let value : (FreshGuard.input (layout capacity)).Value ← if valid : (FreshGuard.input (layout capacity)).valid (slot, replacement, cells)
    then some ⟨(slot, replacement, cells), valid⟩ else none
  let initial := (FreshGuard.input (layout capacity)).representation.initial value
  let before := { initial with bufs := fun i => if i = 200 then #[77] else initial.bufs i
                               caps := fun i => if i = 200 then 4 else initial.caps i
                               regs := fun i => if i = 99 then 91 else initial.regs i
                               tapePos := 9 }
  let body := FreshGuard.implementation (layout capacity)
  let result ← Caliper.run .unit RandomTape.zero 100000 body.program.code before
  pure (((layout capacity).boolean.representation.encoding.decode (result.1.bufs 0).toList).map Subtype.val,
    result.1.bufs 200, result.1.caps 200, result.1.regs 99, result.1.tapePos,
    (List.range 20).all (fun i => result.1.caps (i + 1) == 0),
    decide (body.program.time value ≤ FreshGuard.polynomialTime (layout capacity)))

open Lean in
run_cmd do
  let privateCell : Schnorr.TapeCell (Nat × Nat) := (3, (2, 3), 7)
  let first : Schnorr.TapeCell (Nat × Nat) := (1, (2, 3), 0)
  let second : Schnorr.TapeCell (Nat × Nat) := (1, (2, 4), 0)
  let zero : Schnorr.TapeCell (Nat × Nat) := (1, (0, 0), 0)
  for (slot, replacement, cells, expected) in [
      (0, (2, 3), [], false), (0, (2, 3), [privateCell], false),
      (0, (2, 3), [first], true), (0, (2, 4), [first], false),
      (0, (3, 3), [first], false), (1, (2, 4), [first, second], true),
      (0, (2, 4), [first, second], false), (1, (2, 3), [first, second], false),
      (0, (2, 3), [privateCell, first, second], true),
      (1, (2, 4), [privateCell, first, privateCell, second], true),
      (1, (2, 3), [first, privateCell, second, first], false),
      (2, (2, 3), [first, privateCell, second, first], true),
      (2, (2, 3), [privateCell, first, second, privateCell], false),
      (65535, (2, 3), [first], false), (0, (0, 0), [zero], true),
      (0, (2, 3), [(0, (2, 3), 0), (2, (2, 3), 0)], false),
      (0, (2, 3), [(1, (2, 3), 65535)], true),
      (1, (2, 4), [privateCell, first, privateCell, second, first, second], true)] do
    unless run 6 slot replacement cells == some (some expected, #[77], 4, 91, 9, true, true) do
      throwError "guard failed public-only indexing, multiword equality, bounds, scratch or caller-state preservation"
  unless run 0 0 (2, 3) [] == some (some false, #[77], 4, 91, 9, true, true) do
    throwError "zero-capacity guard did not return unequal"
  unless run 6 65536 (2, 3) [] == none && run 6 0 (256, 3) [] == none &&
      run 6 0 (2, 3) (List.replicate 7 first) == none &&
      run 6 0 (2, 3) [(65536, (2, 3), 0)] == none &&
      run 6 0 (2, 3) [(1, (2, 256), 0)] == none &&
      run 6 0 (2, 3) [(1, (2, 3), 65536)] == none do
    throwError "guard admitted unrepresented input or excess tape cells"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``FreshGuard.publicValues_original, ``FreshGuard.fold_value, ``FreshGuard.source_original,
      ``FreshGuard.stepConstructed, ``FreshGuard.body_buffers, ``FreshGuard.body_budget,
      ``FreshGuard.prepare_bytes, ``FreshGuard.implementation, ``FreshGuard.bounded,
      ``FreshGuard.buffers, ``FreshGuard.names, ``FreshGuard.descriptionFits,
      ``FreshGuard.budget_bounds, ``FreshGuard.polynomial_bounded, ``FreshGuard.resources] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMFreshGuard
