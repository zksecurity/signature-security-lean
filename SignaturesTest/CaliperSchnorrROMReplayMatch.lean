import Signatures.Runtime.Caliper.SchnorrROMReplaySecondSelectionBounds
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMReplayMatch
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
private theorem scaleBound : scale.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private theorem subBound : sub.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private def operations : Handler.Operations config where
  scale := scale
  sub := sub
  slots := 3
  scaleNames := ⟨by decide, by decide⟩
  subNames := ⟨by decide, by decide⟩
  reserve := by decide
  signing := Handler.fullField config scale sub ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) scaleBound subBound
private def budget : Handler.Budget config operations where
  scaleTime := 6
  scaleWords := 27
  subTime := 6
  subWords := 27
  scale := scaleBound
  sub := subBound

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
private def run (qH : Fin 65535) (slot : Fin 65536) (returned firstReturned : Bool)
    (message : Nat) (commitment : Word 16) (response challenge : ZMod 7) (g pk : Word 16)
    (managed live : Signing.Table Nat (ZMod 7) (Word 16)) := do
  let raw : Selection.Input Nat (ZMod 7) (Word 16) := (((message, commitment, response), challenge),
    (((g, pk), managed, live), [(3, 0, 1)], [(1, 6, 0)]))
  let value : (Selection.input config).Value ← if valid : (Selection.input config).valid raw then some ⟨raw, valid⟩ else none
  let second : Terminal.Output config :=
    (if returned then .inr (⟨value.val.1.1, value.property.1.1⟩, ⟨value.val.1.2, value.property.1.2⟩) else .inl (),
      ⟨value.val.2, value.property.2⟩)
  let first : Terminal.Output config :=
    (if firstReturned then .inr (⟨(31, 21, 6), by change 31 < 256; decide, trivial, trivial⟩, ⟨4, trivial⟩) else .inl (),
      ⟨(((11, 13), [((17, 19), 3)], [((23, 29), 5)]), [(9, 0, 7)], [(1, 4, 0)]), by decide⟩)
  let frame : ReplayMatch.Frame config := (second, ((⟨slot.val, slot.isLt⟩, ⟨6, trivial⟩), first))
  let initial := (ReplayMatch.frame config).initial frame
  let before := { initial with bufs := fun i => if i = 200 then #[77] else initial.bufs i
                               caps := fun i => if i = 200 then 4 else initial.caps i
                               regs := fun i => if i = 99 then 91 else initial.regs i
                               tapePos := 9 }
  let body := ReplayMatch.realizer config operations qH.val (allowanceFits qH)
  let result ← Caliper.run .unit RandomTape.zero 100000 body.code before
  pure (((ReplayMatch.output config).encoding.decode (result.1.bufs 0).toList).map
      (fun answer : (Selection.boolean config).Value × ReplayMatch.Frame config => (answer.1.val, (ReplayMatch.frame config).encoding.encode answer.2 == (ReplayMatch.frame config).encoding.encode frame)),
    result.1.bufs 200, result.1.caps 200, result.1.regs 99, result.1.tapePos,
    (List.range 20).all (fun i => result.1.caps (i + 1) == 0),
    decide (body.time frame ≤ ReplayMatch.timeBudget config operations qH.val (allowanceFits qH) budget))

open Lean in
run_cmd do
  let target : (Nat × Word 16) × ZMod 7 := ((2, 5), 2)
  let different : (Nat × Word 16) × ZMod 7 := ((3, 5), 4)
  for (qH, slot, live, expected) in [((0 : Fin 65535), (0 : Fin 65536), [target], true),
      (1, 1, [target, different], true), (1, 0, [target, different], false),
      (0, 1, [target, different], false), (0, 0, [different, target], true),
      (2, 0, [target, different, target], true), (2, 1, [different, target, different], true),
      (2, 0, [], false), (2, 0, [different], false), (65534, 65535, [target], false)] do
    unless run qH slot true true 2 5 5 2 3 5 [] live == some (some (expected, true), #[77], 4, 91, 9, true, true) do
      throwError "matching failed chronological selection, saved slot, failed selector or full-frame preservation"
  for (returned, firstReturned, expected) in [(false, true, false), (false, false, false), (true, false, true)] do
    unless run 0 0 returned firstReturned 2 5 5 2 3 5 [] [target] == some (some (expected, true), #[77], 4, 91, 9, true, true) do
      throwError "matching mishandled cutoff or retained first-output union padding"
  unless run 0 0 true true 2 5 5 4 3 5 [] [target] == some (some (false, true), #[77], 4, 91, 9, true, true) do
    throwError "matching accepted an invalid signature"
  unless run 0 0 true true 2 15 5 0 3 5 [] [((2, 15), 0)] == some (some (true, true), #[77], 4, 91, 9, true, true) &&
      run 0 0 true true 2 4 5 2 4 8 [] [((2, 4), 2)] == some (some (true, true), #[77], 4, 91, 9, true, true) do
    throwError "matching lost zero challenge or runtime public points"
  unless run 0 0 true true 2 5 5 2 3 5 [((2, 5), 4)] [target] == some (some (true, true), #[77], 4, 91, 9, true, true) &&
      run 0 0 true true 2 5 5 2 3 5 [target] [] == some (some (false, true), #[77], 4, 91, 9, true, true) do
    throwError "matching used managed cache instead of LIVE"
  unless run 2 0 true true 256 5 5 2 3 5 [] [target] == none &&
      run 2 0 true true 2 5 5 2 3 5 [] (List.replicate 4 target) == none do
    throwError "matching admitted unrepresented data"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``ReplayMatch.prepare_bytes, ``ReplayMatch.argument_bytes, ``ReplayMatch.Check.constructed,
      ``ReplayMatch.realizer, ``ReplayMatch.preserves_frame, ``ReplayMatch.names, ``ReplayMatch.buffers,
      ``ReplayMatch.bounded, ``ReplayMatch.resources, ``ReplayMatch.check_asIndex, ``ReplayMatch.source_original,
      ``ReplaySecond.Selected.refines, ``ReplaySecond.Selected.retained_first, ``ReplaySecond.Selected.buffers,
      ``ReplaySecond.Selected.descriptionFits, ``ReplaySecond.Selected.time, ``ReplaySecond.Selected.words,
      ``ReplaySecond.Selected.names, ``ReplaySecond.Selected.resources] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMReplayMatch
