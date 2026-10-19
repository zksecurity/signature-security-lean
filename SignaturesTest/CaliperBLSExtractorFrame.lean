import Signatures.Runtime.Caliper.BLSExtractorFrameBounds
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperBLSExtractorFrame
open BLSExtractorFrame

private def accumulation : BLSPrivateAccumulate.Layouts 16 Nat (Word 16) where
  cache := {
    key := Layout.counter 16 256 (by decide) (by decide)
    value := Layout.all (wordRepresentation 16 (by decide))
    capacityPred := 4
    wordFits := by decide
    countFits := by decide
    storageFits := by decide }
  pairStorageFits := by decide
  scalarStorageFits := by decide
  goodStorageFits := by decide
  badStorageFits := by decide
private def rows : BLSRows.Layouts 16 Nat (Word 16) (Word 16) where
  accumulation := accumulation
  point := Layout.all (wordRepresentation 16 (by decide))
  goodStorageFits := by decide
  badStorageFits := by decide
private def layout : BLSTokens.Layouts 16 Nat (Word 16) (Word 16) where
  rows := rows
  capacity := 2
  coefficients := 3
  counterFits := by decide
  coefficientCountFits := by decide
  goodStorageFits := by decide
  badStorageFits := by decide

private def coeffs (values : List (Word 16)) (bounded : values.length ≤ 3) : (coefficients layout.good).Value :=
  ⟨values, bounded, fun _ _ => trivial⟩
private def log (values : List (Nat × Word 16)) (bounded : values.length ≤ 2)
    (valid : ∀ entry ∈ values, entry.1 < 256) : (tokens layout.good).Value :=
  ⟨values, bounded, fun entry member => ⟨valid entry member, trivial⟩⟩
private def goodTable : (table layout.good).Value :=
  ⟨[(9, 19)], by exact ⟨by decide, by intro entry member; simp only [List.mem_singleton] at member; subst entry; exact ⟨show (9 : Nat) < 256 by decide, trivial⟩⟩⟩
private def badTable : (table layout.bad).Value :=
  ⟨[(9, (19, 21))], by exact ⟨by decide, by intro entry member; simp only [List.mem_singleton] at member; subst entry; exact ⟨show (9 : Nat) < 256 by decide, trivial, trivial⟩⟩⟩
private def goodValue (m : Fin 256) (beta : Word 16) (gamma xi : (coefficients layout.good).Value)
    (cache : (table layout.good).Value) (hashes signatures : (tokens layout.good).Value) : (input layout.good).Value :=
  ⟨((m.val, (beta, (gamma.val, xi.val))), (cache.val, (hashes.val, signatures.val))),
    ⟨m.isLt, trivial, gamma.property, xi.property⟩, cache.property, hashes.property, signatures.property⟩
private def badValue (m : Fin 256) (beta : Word 16) (gamma xi : (coefficients layout.good).Value)
    (cache : (table layout.bad).Value) (hashes signatures : (tokens layout.good).Value) : (input layout.bad).Value :=
  ⟨((m.val, (beta, (gamma.val, xi.val))), (cache.val, (hashes.val, signatures.val))),
    ⟨m.isLt, trivial, gamma.property, xi.property⟩, cache.property, hashes.property, signatures.property⟩
private def hashes := log [(1, 71), (2, 72)] (by decide) (by decide)
private def signatures := log [(3, 73)] (by decide) (by decide)
private def gamma := coeffs [11, 12, 13] (by decide)
private def xi := coeffs [3] (by decide)
private def fullGood := goodValue 7 17 gamma xi goodTable hashes signatures
private def fullBad := badValue 7 17 gamma xi badTable hashes signatures
private def alternateBad := badValue 7 17 (coeffs [] (by decide)) xi badTable
  (log [(88, 99)] (by decide) (by decide)) signatures
private def emptyGood := goodValue 5 23 (coeffs [11] (by decide)) (coeffs [] (by decide))
  ⟨[], by exact ⟨by decide, by simp⟩⟩ (log [] (by decide) (by simp)) (log [] (by decide) (by simp))
private def hashReturned : (returned layout.good).Value :=
  ⟨((31, [(9, 19), (1, 23), (2, 29)]), ((7, 17), (signatures.val, xi.val))),
    ⟨trivial, by exact ⟨by decide, by
      intro entry member
      change entry.1 < 256 ∧ True
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> exact ⟨by decide, trivial⟩⟩⟩,
    ⟨show (7 : Nat) < 256 by decide, trivial⟩, signatures.property, xi.property⟩

example : ready layout.good fullGood := by unfold ready; decide
example : signatureReady layout.bad fullBad := by unfold signatureReady; decide
example : BLSSignatureTail.badReady layout (BLSExtractorFrame.badValue layout fullBad) :=
  BLSExtractorFrame.badReady layout fullBad (by unfold signatureReady; decide)
example : BLSSignatureTail.goodReady layout (transitionValue layout hashReturned) :=
  transitionReady layout hashReturned (by decide)
example : ¬ (coefficients layout.good).valid [1, 2, 3, 4] := by
  intro valid
  have impossible : 4 ≤ 3 := valid.1
  omega
example : ¬ (tokens layout.good).valid [(1, 1), (2, 2), (3, 3)] := by
  intro valid
  have impossible : 3 ≤ 2 := valid.1
  omega
example : DescriptionFits (prepare layout.good).code := (prepare layout.good).description_fits
example : DescriptionFits (prepareBad layout).code := (prepareBad layout).description_fits
example : DescriptionFits (transition layout).code := (transition layout).description_fits
example : (prepare layout.good).time fullGood ≤ 8 * 31 := prepare_time layout.good fullGood
example : (prepareBad layout).time fullBad ≤ 8 * 27 := signature_time layout.bad fullBad
example : (transition layout).time hashReturned ≤ 8 * 23 := transition_time layout hashReturned
example : descriptionWords (prepare layout.good).code ≤ 26 * 31 + 14 := prepare_words layout.good
example : descriptionWords (prepareBad layout).code ≤ 26 * 27 + 14 := signature_words layout.bad
example : descriptionWords (transition layout).code ≤ 26 * 23 + 14 := transition_words layout

private def run {A B : Type} {input : Representation 16 A} {output : Representation 16 B} {f : A → B}
    (body : Realizer .unit input output f) (value : A) :=
  let initial := input.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  (Caliper.run .unit RandomTape.zero 10000 body.code before).map fun result =>
    (result.1.bufs 0, result.1.bufs 200, result.1.caps 200, result.1.regs 99, result.1.tapePos,
      result.1.caps 1 == 0, decide (result.2.1 ≤ 8 * output.encoding.words))

open Lean in
run_cmd do
  unless run (prepare layout.good) fullGood == some
      (#[2, 1, 71, 2, 72, 3, 11, 12, 13, 1, 9, 19, 0, 0, 0, 0, 0, 0, 0, 0, 7, 17, 1, 3, 73, 0, 0, 1, 3, 0, 0], #[77], 4, 91, 9, true, true) do
    throwError "hash preparation confused explanation/log lengths, values, or reverse-stored order"
  let selected : Array (Word 16) := #[1, 3, 73, 0, 0, 1, 3, 0, 0, 1, 9, 19, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 17]
  for value in [fullBad, alternateBad] do
    unless run (prepareBad layout) value == some (selected, #[77], 4, 91, 9, true, true) do
      throwError "bad preparation crossed the gamma/xi or hash/signature boundary"
  unless run (prepare layout.good) emptyGood == some
      (#[0, 0, 0, 0, 0, 1, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 23, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[77], 4, 91, 9, true, true) do
    throwError "empty logs lost padding or preserved forgery data"
  unless run (transition layout) hashReturned == some
      (#[1, 3, 73, 0, 0, 1, 3, 0, 0, 3, 9, 19, 1, 23, 2, 29, 0, 0, 0, 0, 7, 17, 31], #[77], 4, 91, 9, true, true) do
    throwError "hash handoff lost updated cache entries or misplaced beta/hash sum"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``prepare, ``selectSignature, ``transition, ``prepareBad,
      ``prepare_time, ``signature_time, ``transition_time, ``prepare_words, ``signature_words, ``transition_words,
      ``prepare_names, ``signature_names, ``transition_names, ``prepare_resources, ``signature_resources, ``transition_resources,
      ``goodTailFits, ``badTailFits, ``transitionReady, ``BLSExtractorFrame.badReady] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"
end SignaturesTest.CaliperBLSExtractorFrame
