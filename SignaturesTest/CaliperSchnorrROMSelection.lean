import Signatures.Runtime.Caliper.SchnorrROMPassSelectionBounds
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMSelection
open SchnorrROMTape SchnorrROM

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private instance : SMul (ZMod 7) (Word 16) := ⟨fun scalar point => BitVec.ofNat 16 scalar.val * point⟩
private def params : PrivateSampler.Enumerated.Parameters 16 (ZMod 7) :=
  PrivateSampler.Enumerated.Parameters.ofFinEnum 16 (ZMod 7) 6 (by decide) (by decide) (by decide)
private def config : Signing.Enumerated.Configuration 16 Nat (ZMod 7) (Word 16) where
  sampler := params
  message := Layout.counter 16 256 (by decide) (by decide)
  point := Layout.all (wordRepresentation 16 (by decide))
  capacityPred := 2
  countFits := by decide
  storageFits := by decide
private def scale : Implementation .unit config.handler.core.arithmetic.scaleArgs config.handler.core.point (fun value => value.1 • value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .mul (by decide)).viewInput config.handler.core.arithmetic.scaleArgs.representation
    (fun value => (BitVec.ofNat 16 value.val.1.val, value.val.2)) (fun _ => rfl)).viewOutput config.handler.core.point.representation
      (fun value => ⟨value.val.1 • value.val.2, trivial⟩) (fun _ => rfl)
private def sub : Implementation .unit config.handler.core.arithmetic.points config.handler.core.point (fun value => value.1 - value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .sub (by decide)).viewInput config.handler.core.arithmetic.points.representation
    (fun value => value.val) (fun _ => rfl)).viewOutput config.handler.core.point.representation
      (fun value => ⟨value.val.1 - value.val.2, trivial⟩) (fun _ => rfl)
private def operations : Handler.Operations config where
  scale := scale
  sub := sub
  slots := 3
  scaleNames := ⟨by decide, by decide⟩
  subNames := ⟨by decide, by decide⟩
  reserve := by decide
private def budget : Handler.Budget config operations where
  scaleTime := 6
  scaleWords := 27
  subTime := 6
  subWords := 27
  scale := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
  sub := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩

private abbrev Store := Schnorr.ListROM.Shared.Store (ZMod 7) (Word 16) Nat
private instance (value : Store) : Decidable (config.handler.store.valid value) := by
  change Decidable ((((True ∧ True) ∧
    (value.1.2.1.length ≤ 3 ∧ ∀ entry ∈ value.1.2.1, (entry.1.1 < 256 ∧ True) ∧ True) ∧
    (value.1.2.2.length ≤ 3 ∧ ∀ entry ∈ value.1.2.2, (entry.1.1 < 256 ∧ True) ∧ True)) ∧
    (value.2.1.length ≤ 6 ∧ ∀ cell ∈ value.2.1, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536) ∧
    (value.2.2.length ≤ 6 ∧ ∀ cell ∈ value.2.2, cell.1 < 65536 ∧ True ∧ cell.2.2 < 65536)))
  infer_instance

private instance (value : Selection.Input Nat (ZMod 7) (Word 16)) : Decidable ((Selection.input config).valid value) := by
  change Decidable (((value.1.1.1 < 256 ∧ True ∧ True) ∧ True) ∧ config.handler.store.valid value.2)
  infer_instance
private theorem allowanceFits (qH : Fin 65535) : qH.val + 1 < 2 ^ 16 := by have := qH.isLt; omega
private def run (qH : Fin 65535) (message : Nat) (commitment : Word 16) (response challenge : ZMod 7)
    (g pk : Word 16) (managed live : Signing.Table Nat (ZMod 7) (Word 16)) := do
  let raw : Selection.Input Nat (ZMod 7) (Word 16) := (((message, commitment, response), challenge),
    (((g, pk), managed, live), [(3, 0, 1)], [(1, 6, 0)]))
  let value : (Selection.input config).Value ← if valid : (Selection.input config).valid raw then some ⟨raw, valid⟩ else none
  let initial := (Selection.input config).representation.initial value
  let before := { initial with bufs := fun i => if i = 200 then #[77] else initial.bufs i
                               caps := fun i => if i = 200 then 4 else initial.caps i
                               regs := fun i => if i = 99 then 91 else initial.regs i
                               tapePos := 9 }
  let implementation := Selection.implementation config operations qH.val (allowanceFits qH)
  let result ← Caliper.run .unit RandomTape.zero 100000 implementation.program.code before
  pure (((Selection.result config).representation.encoding.decode (result.1.bufs 0).toList).map Subtype.val,
    result.1.bufs 200, result.1.caps 200, result.1.regs 99, result.1.tapePos,
    (List.range 20).all (fun i => result.1.caps (i + 1) == 0),
    decide (implementation.program.time value ≤ (Selection.selectionBudget config operations qH.val (allowanceFits qH) budget).time))

private def runPass (returned : Bool) := do
  let forge : (ForgeryHash.forgery config).Value := ⟨(2, 5, 5), by change 2 < 256; decide, trivial, trivial⟩
  let saved : config.handler.store.Value := ⟨(((3, 5), [], [((2, 5), 2)]), [], []), by decide⟩
  let value : Terminal.Output config := (if returned then .inr (forge, ⟨2, trivial⟩) else .inl (), saved)
  let initial := (PassSelection.input config).initial value
  let before := { initial with bufs := fun i => if i = 200 then #[77] else initial.bufs i
                               caps := fun i => if i = 200 then 4 else initial.caps i
                               regs := fun i => if i = 99 then 91 else initial.regs i
                               tapePos := 9 }
  let body := PassSelection.realizer config operations 0 (by decide)
  let result ← Caliper.run .unit RandomTape.zero 100000 body.code before
  pure (((Selection.result config).representation.encoding.decode (result.1.bufs 0).toList).map Subtype.val,
    result.1.bufs 200, result.1.caps 200, result.1.regs 99, result.1.tapePos,
    (List.range 20).all (fun i => result.1.caps (i + 1) == 0),
    decide (body.time value ≤ PassSelection.timeBudget config operations 0 (by decide) budget))

open Lean in
run_cmd do
  let target : (Nat × Word 16) × ZMod 7 := ((2, 5), 2)
  let different : (Nat × Word 16) × ZMod 7 := ((3, 5), 4)
  for (qH, live, expected) in [((0 : Fin 65535), [target], (true, 0)),
      (1, [target, different], (true, 1)), (0, [target, different], (false, 0)),
      (0, [different, target], (true, 0)), (2, [target, different, target], (true, 0)),
      (2, [different, target, different], (true, 1)), (2, [different], (false, 0)),
      (2, [], (false, 0)), (65534, [target, different], (true, 1))] do
    unless run qH 2 5 5 2 3 5 [] live == some (some expected, #[77], 4, 91, 9, true, true) do
      throwError "selector failed chronological lookup, missing entry or index guard"
  unless run 2 2 5 5 4 3 5 [] [target] == some (some (false, 0), #[77], 4, 91, 9, true, true) do
    throwError "selector accepted an invalid signature"
  unless run 0 2 15 5 0 3 5 [] [((2, 15), 0)] == some (some (true, 0), #[77], 4, 91, 9, true, true) do
    throwError "selector rejected a valid zero challenge"
  unless run 0 2 4 5 2 4 8 [] [((2, 4), 2)] == some (some (true, 0), #[77], 4, 91, 9, true, true) do
    throwError "selector ignored the runtime generator or public key"
  unless run 0 2 5 5 2 3 5 [((2, 5), 4)] [target] == some (some (true, 0), #[77], 4, 91, 9, true, true) &&
      run 0 2 5 5 2 3 5 [target] [] == some (some (false, 0), #[77], 4, 91, 9, true, true) do
    throwError "selector confused the managed cache with LIVE"
  unless run 2 256 5 5 2 3 5 [] [target] == none && run 2 2 5 5 2 3 5 [] (List.replicate 4 target) == none do
    throwError "selector accepted an unrepresented message or overflowing cache"
  unless runPass false == some (some (false, 0), #[77], 4, 91, 9, true, true) &&
      runPass true == some (some (true, 0), #[77], 4, 91, 9, true, true) do
    throwError "pass-output selection mishandled cutoff, union padding or the returned forgery"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Selection.point_bounded, ``Selection.verify_bounded, ``Selection.verify_buffers, ``Selection.verify_names,
      ``Selection.Guard.constructed, ``Selection.Guard.budget, ``Selection.accepted, ``Selection.buffers,
      ``Selection.names, ``Selection.bounded, ``Selection.realizer, ``Selection.resources,
      ``Selection.Guard.source_original, ``Selection.source_original, ``Selection.source_forkPoint, ``Selection.source_selectPass,
      ``PassSelection.valid, ``PassSelection.pass_bytes, ``PassSelection.buffers, ``PassSelection.names,
      ``PassSelection.time, ``PassSelection.words, ``PassSelection.bounded, ``PassSelection.resources,
      ``PassSelection.source_original] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMSelection
