import Proofs.Runtime.Caliper.BLSExtractorAcceptance
import Proofs.Runtime.Caliper.BLSExtractorSource
import Proofs.Runtime.Caliper.BLSExtractionExitSource
import Proofs.Runtime.Caliper.BLSCallerFinishService
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperBLSExtractor

-- Word arithmetic exercises routing and composition, not a finite-field model.
-- General field-source equality is proved separately in BLSExtractorSource.
private def base (_ : Unit) : Type := Word 16
private instance (n : Nat) : OfNat (Ty.Value base (.atom ())) n := inferInstanceAs (OfNat (Word 16) n)
private instance : Zero (Ty.Value base (.atom ())) := inferInstanceAs (Zero (Word 16))
private instance : Mul (Ty.Value base (.atom ())) := inferInstanceAs (Mul (Word 16))
private instance : Add (Ty.Value base (.atom ())) := inferInstanceAs (Add (Word 16))
private instance : Sub (Ty.Value base (.atom ())) := inferInstanceAs (Sub (Word 16))
private instance : Neg (Ty.Value base (.atom ())) := inferInstanceAs (Neg (Word 16))
private instance : Div (Ty.Value base (.atom ())) := inferInstanceAs (Div (Word 16))
private inductive Op : Ty Unit → Ty Unit → Type
  | equal : Op (.pair .nat .nat) .bool
private def primitives : Primitives base Op where
  execute instruction := match instruction with | .equal => fun value => decide (value.1 = value.2)
  cost _ _ := 1
private def comparison : Expr Op [.nat, .nat] .bool := .op .equal (.pair (.var .here) (.var (.there .here)))
private theorem comparison_correct (left right : Nat) : comparison.denote primitives (left, right, ()) = decide (left = right) := rfl

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

private def binary (op : BinOp) : Implementation .unit accumulation.arithmetic.pair accumulation.cache.value
    (fun value => op.eval value.1 value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit op accumulation.cache.wordFits).viewInput accumulation.arithmetic.pair.representation
    (fun value => value.val) (fun _ => rfl)).viewOutput accumulation.cache.value.representation
      (fun value => ⟨op.eval value.val.1 value.val.2, trivial⟩) (fun _ => rfl)
private def mul : Implementation .unit accumulation.arithmetic.pair accumulation.cache.value (fun value => value.1 * value.2) := binary .mul
private def add : Implementation .unit accumulation.arithmetic.pair accumulation.cache.value (fun value => value.1 + value.2) := binary .add
private theorem mul_bound : mul.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem add_bound : add.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem mul_names : NamesBound mul.program.code 3 := by constructor <;> decide
private theorem add_names : NamesBound add.program.code 3 := by constructor <;> decide
private theorem reserve : 3 + 4 < 2 ^ 16 := by decide

private def sampleSpec : OracleSpec Unit := fun _ => accumulation.cache.value.Value
private def replyView : (Σ _ : accumulation.cache.lookup.unit.Value, accumulation.cache.value.Value) ≃ accumulation.cache.value.Value where
  toFun := Sigma.snd
  invFun value := ⟨⟨(), trivial⟩, value⟩
  left_inv value := by rcases value with ⟨⟨position, valid⟩, answer⟩; cases position; rfl
  right_inv _ := rfl
private def port : Interactive.Port 16 sampleSpec where
  Request := accumulation.cache.lookup.unit.Value
  source _ := ()
  request := accumulation.cache.lookup.unit.representation
  reply := accumulation.cache.value.representation.transport replyView
private def drawSource : OracleComp sampleSpec accumulation.cache.value.Value := queryBind () Pure.pure
private def draw : Interactive.Code 16 := .query
private theorem draw_correct : Interactive.Refines port .unit accumulation.cache.lookup.unit.representation accumulation.cache.value.representation
    (fun _ => drawSource) draw := by
  have projected := (Interactive.Refines.query port .unit).viewOutput accumulation.cache.value.representation replyView (fun _ => rfl)
  convert projected using 1 <;> rfl
private theorem draw_time : Interactive.TimeBound port .unit accumulation.cache.lookup.unit.representation draw 4 := Interactive.TimeBound.query
private theorem draw_words : (draw.lower port).descriptionWords ≤ 20 := by decide
private theorem draw_names : WordIO.NamesBound (draw.lower port) 3 := by constructor <;> decide
private theorem draw_fits : (draw.lower port).DescriptionFits := WordIO.exchange_descriptionFits 0 1 (by decide) (by decide)

private def rows : BLSRows.Layouts 16 Nat (Word 16) (Word 16) where
  accumulation := accumulation
  point := Layout.all (wordRepresentation 16 (by decide))
  goodStorageFits := by decide
  badStorageFits := by decide
private def layout : BLSTokens.Layouts 16 Nat (Word 16) (Word 16) where
  rows := rows
  capacity := 3
  coefficients := 4
  counterFits := by decide
  coefficientCountFits := by decide
  goodStorageFits := by decide
  badStorageFits := by decide
private def sub : Implementation .unit accumulation.arithmetic.pair accumulation.cache.value (fun value => value.1 - value.2) := binary .sub
private def divide : Implementation .unit accumulation.arithmetic.pair accumulation.cache.value (fun value => value.1 / value.2) := binary .udiv
private def zero : Implementation .unit accumulation.cache.value accumulation.cache.value (fun _ => 0) :=
  Implementation.constant accumulation.cache.value accumulation.cache.value ⟨0, trivial⟩ accumulation.cache.wordFits
private def negArgs : Implementation .unit accumulation.cache.value accumulation.arithmetic.pair (fun value => (0, value)) :=
  zero.pair (Implementation.identity accumulation.cache.value (by decide)) (by decide) accumulation.cache.wordFits
    (by decide) (by decide) (by decide) (by decide) accumulation.arithmetic.pair.representation.fits
private def negate : Implementation .unit accumulation.cache.value accumulation.cache.value Neg.neg :=
  (negArgs.then sub).castFunction (by funext value; exact BitVec.zero_sub value)
private theorem sub_bound : sub.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem div_bound : divide.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem neg_bound : negate.BoundedBy 118 631 := by
  have zeroBound := Implementation.constant_bounded accumulation.cache.value accumulation.cache.value ⟨0, trivial⟩ accumulation.cache.wordFits
  have paired : negArgs.BoundedBy 112 603 := by
    apply (Implementation.pair_boundedBy zero (Implementation.identity accumulation.cache.value (by decide))
      accumulation.cache.wordFits (by decide) (by decide) (by decide) (by decide) accumulation.arithmetic.pair.representation.fits
      zeroBound (Implementation.identity_boundedBy accumulation.cache.value (by decide))).mono <;> decide
  apply ((paired.then sub_bound).castFunction _).mono <;> decide
private theorem sub_names : NamesBound sub.program.code 3 := by constructor <;> decide
private theorem div_names : NamesBound divide.program.code 3 := by constructor <;> decide
private theorem neg_names : NamesBound negate.program.code 3 := by constructor <;> decide

private def good := BLSExtractor.goodCode (base := base) (key := .nat) (val := .atom ()) (slots := 3)
  layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers port draw
private def goodDenote := BLSExtractor.goodDenote (base := base) (key := .nat) (val := .atom ()) (slots := 3)
  layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers drawSource
private theorem good_correct : Interactive.RefinesOn (BLSExtractor.goodReady layout) port .unit (BLSExtractorFrame.input layout.good).representation
    (CacheScalarResult.output accumulation.good).representation goodDenote good :=
  BLSExtractor.good_refines (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource)
    layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers port draw_correct
private theorem good_time : Interactive.TimeBoundOn (BLSExtractor.goodReady layout) port .unit (BLSExtractorFrame.input layout.good).representation good
    (BLSExtractor.goodTime (base := base) (key := .nat) (val := .atom ()) layout 4 6 6 6 6) :=
  BLSExtractor.good_time (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource)
    layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers port draw_correct draw_time mul_bound add_bound sub_bound div_bound
example : (good.lower port).descriptionWords ≤ BLSExtractor.goodWords (base := base) (key := .nat) (val := .atom ()) layout 20 27 27 27 27 :=
  BLSExtractor.good_words (base := base) (key := .nat) (val := .atom ()) (slots := 3) layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers port draw draw_words mul_bound add_bound sub_bound div_bound
private theorem good_accounted : WordIO.NamesAccounted (good.lower port) 5 :=
  BLSExtractor.good_names (drawNames := 3) (names := 3) (base := base) (key := .nat) (val := .atom ()) (slots := 3) layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers port draw draw_names mul_names.accounted add_names.accounted sub_names.accounted div_names.accounted
private theorem good_fits : (good.lower port).DescriptionFits :=
  BLSExtractor.good_descriptionFits (base := base) (key := .nat) (val := .atom ()) (slots := 3) layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers port draw draw_fits draw_names (by decide)
private def bad := BLSExtractor.badCode (base := base) (key := .nat) (val := .atom ()) (slots := 3)
  layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers port draw
private def badDenote := BLSExtractor.badDenote (base := base) (key := .nat) (val := .atom ()) (slots := 3)
  layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers drawSource
private theorem bad_correct : Interactive.RefinesOn (BLSExtractor.badReady layout) port .unit (BLSExtractorFrame.input layout.bad).representation
    (CacheScalarResult.output accumulation.bad).representation badDenote bad :=
  BLSExtractor.bad_refines (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource)
    layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers port draw_correct
private theorem bad_time : Interactive.TimeBoundOn (BLSExtractor.badReady layout) port .unit (BLSExtractorFrame.input layout.bad).representation bad
    (BLSExtractor.badTime (base := base) (key := .nat) (val := .atom ()) layout 4 6 6 6 118 6) :=
  BLSExtractor.bad_time (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource)
    layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers port draw_correct draw_time mul_bound add_bound sub_bound neg_bound div_bound
example : (bad.lower port).descriptionWords ≤ BLSExtractor.badWords (base := base) (key := .nat) (val := .atom ()) layout 20 27 27 27 631 27 :=
  BLSExtractor.bad_words (base := base) (key := .nat) (val := .atom ()) (slots := 3) layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers port draw draw_words mul_bound add_bound sub_bound neg_bound div_bound
private theorem bad_accounted : WordIO.NamesAccounted (bad.lower port) 5 :=
  BLSExtractor.bad_names (drawNames := 3) (names := 3) (base := base) (key := .nat) (val := .atom ()) (slots := 3) layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers port draw draw_names mul_names.accounted add_names.accounted sub_names.accounted neg_names.accounted div_names.accounted
private theorem bad_fits : (bad.lower port).DescriptionFits :=
  BLSExtractor.bad_descriptionFits (base := base) (key := .nat) (val := .atom ()) (slots := 3) layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers port draw draw_fits draw_names (by decide)

open BLSExtractorFrame
private def coeffs (values : List (Word 16)) (bounded : values.length ≤ 4) : (coefficients layout.good).Value :=
  ⟨values, bounded, fun _ _ => trivial⟩
private def log (values : List (Nat × Word 16)) (bounded : values.length ≤ 3)
    (valid : ∀ entry ∈ values, entry.1 < 256) : (tokens layout.good).Value :=
  ⟨values, bounded, fun entry member => ⟨valid entry member, trivial⟩⟩
private def scalarCache (values : List (Nat × Word 16)) (bounded : values.length ≤ 5)
    (valid : ∀ entry ∈ values, entry.1 < 256) : (table layout.good).Value :=
  ⟨values, bounded, fun entry member => ⟨valid entry member, trivial⟩⟩
private def pairCache (values : List (Nat × (Word 16 × Word 16))) (bounded : values.length ≤ 5)
    (valid : ∀ entry ∈ values, entry.1 < 256) : (table layout.bad).Value :=
  ⟨values, bounded, fun entry member => ⟨valid entry member, trivial, trivial⟩⟩
private def goodValue (m : Fin 256) (beta : Word 16) (gamma xi : (coefficients layout.good).Value)
    (cache : (table layout.good).Value) (hashes signatures : (tokens layout.good).Value) : BLSExtractor.GoodInput layout :=
  ⟨((m.val, (beta, (gamma.val, xi.val))), (cache.val, (hashes.val, signatures.val))),
    ⟨m.isLt, trivial, gamma.property, xi.property⟩, cache.property, hashes.property, signatures.property⟩
private def badValue (m : Fin 256) (beta : Word 16) (gamma xi : (coefficients layout.good).Value)
    (cache : (table layout.bad).Value) (hashes signatures : (tokens layout.good).Value) : BLSExtractor.BadInput layout :=
  ⟨((m.val, (beta, (gamma.val, xi.val))), (cache.val, (hashes.val, signatures.val))),
    ⟨m.isLt, trivial, gamma.property, xi.property⟩, cache.property, hashes.property, signatures.property⟩
private def hashes := log [(1, 71), (2, 72)] (by decide) (by decide)
private def signatures := log [(3, 73), (4, 74)] (by decide) (by decide)
private def gamma := coeffs [2, 3] (by decide)
private def xi := coeffs [3, 4] (by decide)
private def noScalarCache := scalarCache [] (by decide) (by simp)
private def noPairCache := pairCache [] (by decide) (by simp)
private def noLog := log [] (by decide) (by simp)
private def noCoeffs := coeffs [] (by decide)
private def goodFresh := goodValue 5 20 gamma xi noScalarCache hashes signatures
private def goodOverlap := goodValue 5 20 gamma xi noScalarCache hashes hashes
private def goodMissing := goodValue 5 20 (coeffs [2] (by decide)) (coeffs [3] (by decide)) noScalarCache hashes signatures
private def goodSurplus := goodValue 5 20 (coeffs [2, 3, 99, 100] (by decide)) (coeffs [3, 4, 88, 100] (by decide)) noScalarCache hashes signatures
private def repeated := log [(2, 72), (2, 71)] (by decide) (by decide)
private def goodRepeated := goodValue 5 20 gamma xi noScalarCache repeated repeated
private def goodZero := goodValue 2 20 noCoeffs noCoeffs noScalarCache hashes hashes
private def oneLog := log [(2, 71)] (by decide) (by decide)
private def goodHit := goodValue 5 10 (coeffs [3] (by decide)) (coeffs [2] (by decide))
  (scalarCache [(2, 5)] (by decide) (by decide)) oneLog oneLog
private def goodEmpty := goodValue 2 10 (coeffs [99] (by decide)) (coeffs [100] (by decide))
  (scalarCache [(2, 2)] (by decide) (by decide)) noLog noLog
private def badFresh := badValue 5 20 gamma xi noPairCache hashes signatures
private def badIgnored := badValue 5 77 noCoeffs xi noPairCache repeated signatures
private def badRepeated := badValue 5 20 gamma xi noPairCache hashes repeated
private def badHit := badValue 5 20 gamma xi (pairCache [(4, (5, 2))] (by decide) (by decide)) hashes signatures
private def badEmpty := badValue 2 99 gamma xi (pairCache [(2, (5, 0))] (by decide) (by decide)) hashes noLog

example : BLSExtractor.goodReady layout goodFresh := by unfold BLSExtractor.goodReady BLSExtractorFrame.ready; decide
example : BLSExtractor.goodReady layout goodHit := by unfold BLSExtractor.goodReady BLSExtractorFrame.ready; decide
example : BLSExtractor.badReady layout badHit := by unfold BLSExtractor.badReady BLSExtractorFrame.signatureReady; decide
example : ¬ BLSExtractor.goodReady layout (goodValue 5 20 gamma xi (scalarCache [(2, 5)] (by decide) (by decide)) hashes signatures) := by
  unfold BLSExtractor.goodReady BLSExtractorFrame.ready
  decide

private def run {A : Type} (input : Representation 16 A) (code : Interactive.Code 16) (budget : Nat) (value : A) (replies : List (Word 16)) := do
  let initial := input.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 200000 (code.lower port) before replies
  pure (result.state.bufs 0, result.state.bufs 200, result.state.caps 200, result.state.regs 99, result.state.tapePos,
    (List.range 32).all (fun i => result.state.caps (i + 1) == 0), result.trace, result.remaining, decide (result.time ≤ budget))
private def runGood := run (input layout.good).representation good (BLSExtractor.goodTime (base := base) (key := .nat) (val := .atom ()) layout 4 6 6 6 6)
private def runBad := run (input layout.bad).representation bad (BLSExtractor.badTime (base := base) (key := .nat) (val := .atom ()) layout 4 6 6 6 118 6)
private def events (values : List (Word 16)) : List (WordIO.Event 16) := values.flatMap (fun value => [.invoke, .input value])

open Lean in
run_cmd do
  for (value, replies, expected, consumed, remaining) in [
      (goodFresh, [5, 7, 11, 13, 102, 88], #[3, 5, 5, 102, 3, 13, 4, 11, 1, 7, 2, 5], [5, 7, 11, 13, 102], [88]),
      (goodOverlap, [5, 7, 60, 88], #[3, 3, 5, 60, 1, 7, 2, 5, 0, 0, 0, 0], [5, 7, 60], [88]),
      (goodMissing, [5, 7, 11, 13, 43], #[3, 5, 5, 43, 3, 13, 4, 11, 1, 7, 2, 5], [5, 7, 11, 13, 43], []),
      (goodSurplus, [5, 7, 11, 13, 102], #[3, 5, 5, 102, 3, 13, 4, 11, 1, 7, 2, 5], [5, 7, 11, 13, 102], []),
      (goodRepeated, [5, 50], #[3, 2, 5, 50, 2, 5, 0, 0, 0, 0, 0, 0], [5, 50], []),
      (goodZero, [5, 7, 88], #[4, 2, 1, 7, 2, 5, 0, 0, 0, 0, 0, 0], [5, 7], [88]),
      (goodHit, [15, 88], #[5, 2, 5, 15, 2, 5, 0, 0, 0, 0, 0, 0], [15], [88]),
      (goodEmpty, [], #[5, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0], [], []),
      (goodFresh, [5, 7, 11, 13, 85], #[0, 5, 5, 85, 3, 13, 4, 11, 1, 7, 2, 5], [5, 7, 11, 13, 85], [])] do
    unless runGood value replies == some (expected, #[77], 4, 91, 9, true, events consumed, remaining, true) do
      throwError "complete good extractor failed for {value.val}"
  for (value, replies, expected, consumed, remaining) in [
      (badFresh, [5, 2, 7, 3, 55, 6, 88], #[1, 3, 5, 55, 6, 3, 7, 3, 4, 5, 2, 0, 0, 0, 0, 0, 0], [5, 2, 7, 3, 55, 6], [88]),
      (badIgnored, [5, 2, 7, 3, 55, 6], #[1, 3, 5, 55, 6, 3, 7, 3, 4, 5, 2, 0, 0, 0, 0, 0, 0], [5, 2, 7, 3, 55, 6], []),
      (badRepeated, [5, 2, 47, 2], #[1, 2, 5, 47, 2, 2, 5, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], [5, 2, 47, 2], []),
      (badHit, [7, 3, 55, 6], #[1, 3, 5, 55, 6, 3, 7, 3, 4, 5, 2, 0, 0, 0, 0, 0, 0], [7, 3, 55, 6], []),
      (badEmpty, [], #[0, 1, 2, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [], []),
      (badFresh, [5, 2, 7, 3, 43, 6], #[0, 3, 5, 43, 6, 3, 7, 3, 4, 5, 2, 0, 0, 0, 0, 0, 0], [5, 2, 7, 3, 43, 6], [])] do
    unless runBad value replies == some (expected, #[77], 4, 91, 9, true, events consumed, remaining, true) do
      throwError "complete bad extractor failed for {value.val}"
  unless (runGood goodZero [5]).isNone do throwError "zero-coefficient hash lookup accepted no response"
  unless (runGood goodFresh [5, 7, 11, 13]).isNone do throwError "final scalar lookup accepted no response"
  unless (runBad badFresh [5, 2, 7, 3, 55]).isNone do throwError "final pair lookup accepted a partial response"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``BLSExtractor.hash_refines, ``BLSExtractor.hash_preserves, ``BLSExtractor.good_refines, ``BLSExtractor.bad_refines,
      ``BLSExtractor.good_source, ``BLSExtractor.bad_source, ``BLSExtractor.good_original, ``BLSExtractor.bad_original,
      ``BLSExtractor.good_time, ``BLSExtractor.bad_time, ``BLSExtractor.good_words, ``BLSExtractor.bad_words,
      ``BLSExtractor.good_names, ``BLSExtractor.bad_names, ``BLSExtractor.good_resources, ``BLSExtractor.bad_resources,
      ``BLSExtractor.good_descriptionFits, ``BLSExtractor.bad_descriptionFits,
      ``Interactive.RefinesOn.viewInput, ``Interactive.RefinesOn.viewOutput, ``Interactive.TimeBoundOn.viewInput,
      ``good_correct, ``bad_correct, ``good_time, ``bad_time] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

-- Pending caller data can exceed the forgery width: union padding lies before
-- the nonzero configuration. Both must be skipped without corrupting the cache.
private def exitConfig := (wordRepresentation 16 (by decide)).prod (wordRepresentation 16 (by decide)) (by decide)
private def exitPending := (forgery layout.good).representation.prod exitConfig (by decide)
private def service := BLSCallerFinish.service layout.good (Layout.all exitConfig) (by decide) (by decide)
private def callerStore (value : BLSExtractor.GoodInput layout) : service.store.Value :=
  ⟨((99, 100), value.val.2), trivial, value.property.2⟩
private def emptyCallerStore : service.store.Value :=
  ⟨((99, 100), ([], ([], []))), trivial, ⟨by decide, by simp⟩, ⟨by decide, by simp⟩, ⟨by decide, by simp⟩⟩
private theorem caller_postcondition : BLSCaller.Postcondition service 2 emptyCallerStore (callerStore goodHit) where
  reserved := {
    config := trivial
    cached := (callerStore goodHit).property.2.1.2
    recorded := ⟨(callerStore goodHit).property.2.2.1.2, (callerStore goodHit).property.2.2.2.2⟩
    cacheRoom := by decide
    logRoom := by decide }
  config := rfl
  cache := by decide
  logs := by decide
example : BLSCallerFinish.ready layout.good (BLSExtractor.goodReady layout)
    (BLSCallerFinish.packetView layout.good (Layout.all exitConfig) (by decide) (by decide)
      ((.inl ⟨goodHit.val.1, goodHit.property.1⟩ : (forgery layout.good).Value ⊕ Unit), callerStore goodHit)) :=
  BLSCallerFinish.packet_ready layout.good (Layout.all exitConfig) (by decide) (by decide) caller_postcondition (by decide) _
example : BLSCallerFinish.ready layout.good (BLSExtractorFrame.signatureReady layout.good)
    (BLSCallerFinish.packetView layout.good (Layout.all exitConfig) (by decide) (by decide)
      ((.inl ⟨goodHit.val.1, goodHit.property.1⟩ : (forgery layout.good).Value ⊕ Unit), callerStore goodHit)) :=
  BLSCallerFinish.packet_signature_ready layout.good (Layout.all exitConfig) (by decide) (by decide) caller_postcondition (by decide) _
private def exitGood := BLSExtractionExit.goodCode (base := base) (key := .nat) (val := .atom ()) (slots := 3)
  layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers
  exitConfig exitPending (by decide) port draw
private def exitBad := BLSExtractionExit.badCode (base := base) (key := .nat) (val := .atom ()) (slots := 3)
  layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers
  exitConfig exitPending (by decide) port draw
private def exitGoodSmall := BLSExtractionExit.goodCode (base := base) (key := .nat) (val := .atom ()) (slots := 3)
  layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers
  exitConfig accumulation.cache.lookup.unit.representation (by decide) port draw

private def goodPacket (value : BLSExtractor.GoodInput layout) (configuration : Word 16 × Word 16) :
    BLSCallerFinish.Packet (P := (forgery layout.good).Value × (Word 16 × Word 16)) (C := Word 16 × Word 16) layout.good :=
  (.inl ⟨value.val.1, value.property.1⟩, configuration, ⟨value.val.2, value.property.2⟩)
private def badPacket (value : BLSExtractor.BadInput layout) (configuration : Word 16 × Word 16) :
    BLSCallerFinish.Packet (P := (forgery layout.good).Value × (Word 16 × Word 16)) (C := Word 16 × Word 16) layout.bad :=
  (.inl ⟨value.val.1, value.property.1⟩, configuration, ⟨value.val.2, value.property.2⟩)
private def goodCutoff (value : BLSExtractor.GoodInput layout) :
    BLSCallerFinish.Packet (P := (forgery layout.good).Value × (Word 16 × Word 16)) (C := Word 16 × Word 16) layout.good :=
  (.inr (⟨value.val.1, value.property.1⟩, (77, 88)), (99, 100), ⟨value.val.2, value.property.2⟩)
private def badCutoff (value : BLSExtractor.BadInput layout) :
    BLSCallerFinish.Packet (P := (forgery layout.good).Value × (Word 16 × Word 16)) (C := Word 16 × Word 16) layout.bad :=
  (.inr (⟨value.val.1, value.property.1⟩, (77, 88)), (99, 100), ⟨value.val.2, value.property.2⟩)
private def noRoom := goodValue 5 20 gamma xi (scalarCache [(2, 5)] (by decide) (by decide)) hashes signatures
example : BLSCallerFinish.ready layout.good (BLSExtractor.goodReady layout) (goodCutoff noRoom) := by trivial

private def exitGoodTime := BLSCallerFinish.timeBudget layout.good exitConfig exitPending (by decide)
  (BLSExtractor.goodTime (base := base) (key := .nat) (val := .atom ()) layout 4 6 6 6 6)
private def exitBadTime := BLSCallerFinish.timeBudget layout.bad exitConfig exitPending (by decide)
  (BLSExtractor.badTime (base := base) (key := .nat) (val := .atom ()) layout 4 6 6 6 118 6)
private theorem exit_good_time : Interactive.TimeBoundOn (BLSCallerFinish.ready layout.good (BLSExtractor.goodReady layout)) port .unit
    (BLSCallerFinish.input layout.good exitConfig exitPending (by decide)) exitGood exitGoodTime :=
  BLSExtractionExit.good_time (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource)
    layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers
    exitConfig exitPending (by decide) port draw_correct draw_time mul_bound add_bound sub_bound div_bound
private theorem exit_bad_time : Interactive.TimeBoundOn (BLSCallerFinish.ready layout.bad (BLSExtractor.badReady layout)) port .unit
    (BLSCallerFinish.input layout.bad exitConfig exitPending (by decide)) exitBad exitBadTime :=
  BLSExtractionExit.bad_time (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource)
    layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers
    exitConfig exitPending (by decide) port draw_correct draw_time mul_bound add_bound sub_bound neg_bound div_bound
example : (exitGood.lower port).DescriptionFits :=
  BLSCallerFinish.descriptionFits layout.good exitConfig exitPending (by decide) port (BLSTokens.zero layout (by trivial)) good_fits
example : (exitBad.lower port).DescriptionFits :=
  BLSCallerFinish.descriptionFits layout.bad exitConfig exitPending (by decide) port (BLSTokens.zero layout (by trivial)) bad_fits
example : WordIO.NamesAccounted (exitGood.lower port) 5 :=
  BLSCallerFinish.names layout.good exitConfig exitPending (by decide) port good_accounted (BLSTokens.zero layout (by trivial))
example : WordIO.NamesAccounted (exitBad.lower port) 5 :=
  BLSCallerFinish.names layout.bad exitConfig exitPending (by decide) port bad_accounted (BLSTokens.zero layout (by trivial))

private def runExitGood := run (BLSCallerFinish.input layout.good exitConfig exitPending (by decide)) exitGood exitGoodTime
private def runCallerExit := run
  (BLSCallerFinish.callerOutput layout.good (Layout.all exitConfig) (by decide) (by decide) exitPending (by decide)) exitGood exitGoodTime
private def runExitBad := run (BLSCallerFinish.input layout.bad exitConfig exitPending (by decide)) exitBad exitBadTime
private def runExitGoodSmall := run (BLSCallerFinish.input layout.good exitConfig accumulation.cache.lookup.unit.representation (by decide)) exitGoodSmall
  (BLSCallerFinish.timeBudget layout.good exitConfig accumulation.cache.lookup.unit.representation (by decide)
    (BLSExtractor.goodTime (base := base) (key := .nat) (val := .atom ()) layout 4 6 6 6 6))

open Lean in
run_cmd do
  for configuration in [(0, 0), (99, 100)] do
    unless runExitGood (goodPacket goodFresh configuration) [5, 7, 11, 13, 102, 88] ==
        some (#[3], #[77], 4, 91, 9, true, events [5, 7, 11, 13, 102], [88], true) do
      throwError "good return routing or scalar projection failed"
    unless runExitBad (badPacket badFresh configuration) [5, 2, 7, 3, 55, 6, 88] ==
        some (#[1], #[77], 4, 91, 9, true, events [5, 2, 7, 3, 55, 6], [88], true) do
      throwError "bad return routing or scalar projection failed"
  unless runExitGood (goodPacket goodEmpty (99, 100)) [] ==
      some (#[5], #[77], 4, 91, 9, true, [], [], true) do throwError "cached return failed"
  unless runCallerExit (.inl ⟨goodHit.val.1, goodHit.property.1⟩, callerStore goodHit) [15, 88] ==
      some (#[5], #[77], 4, 91, 9, true, events [15], [88], true) do throwError "caller service store did not reach extraction"
  unless runCallerExit (.inr (⟨goodHit.val.1, goodHit.property.1⟩, (77, 88)), callerStore goodHit) [88] ==
      some (#[0], #[77], 4, 91, 9, true, [], [88], true) do throwError "caller service cutoff failed"
  unless runExitGood (goodCutoff noRoom) [88] ==
      some (#[0], #[77], 4, 91, 9, true, [], [88], true) do throwError "cutoff required extraction room or queried"
  unless runExitBad (badCutoff badFresh) [88] ==
      some (#[0], #[77], 4, 91, 9, true, [], [88], true) do throwError "bad cutoff queried or lost its fallback"
  unless runExitGoodSmall (.inl ⟨goodFresh.val.1, goodFresh.property.1⟩, (99, 100), ⟨goodFresh.val.2, goodFresh.property.2⟩)
      [5, 7, 11, 13, 102, 88] == some (#[3], #[77], 4, 91, 9, true, events [5, 7, 11, 13, 102], [88], true) do
    throwError "return with smaller pending representation failed"
  unless runExitGoodSmall (.inr ⟨(), trivial⟩, (99, 100), ⟨noRoom.val.2, noRoom.property.2⟩) [88] ==
      some (#[0], #[77], 4, 91, 9, true, [], [88], true) do throwError "padded cutoff failed"
  unless (runExitGood (goodPacket goodFresh (99, 100)) [5, 7, 11, 13]).isNone do
    throwError "returned forgery accepted a missing final scalar"
  unless (runExitBad (badPacket badFresh (99, 100)) [5, 2, 7, 3, 55]).isNone do
    throwError "returned forgery accepted a partial pair"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``BLSCallerFinish.refines, ``BLSCallerFinish.time_bound, ``BLSCallerFinish.code_bound, ``BLSCallerFinish.resources,
      ``BLSCallerFinish.service_cacheLogs, ``BLSCallerFinish.packet_bytes, ``BLSCallerFinish.packet_ready, ``BLSCallerFinish.packet_signature_ready,
      ``BLSExtractionExit.good_refines, ``BLSExtractionExit.bad_refines, ``BLSExtractionExit.good_return_source, ``BLSExtractionExit.bad_return_source,
      ``BLSExtractionExit.good_cutoff_source, ``BLSExtractionExit.bad_cutoff_source,
      ``BLSExtractionExit.good_time, ``BLSExtractionExit.bad_time, ``BLSExtractionExit.good_words, ``BLSExtractionExit.bad_words,
      ``BLSExtractionExit.good_names, ``BLSExtractionExit.bad_names, ``BLSExtractionExit.good_descriptionFits, ``BLSExtractionExit.bad_descriptionFits,
      ``exit_good_time, ``exit_bad_time, ``caller_postcondition] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"
end SignaturesTest.CaliperBLSExtractor
