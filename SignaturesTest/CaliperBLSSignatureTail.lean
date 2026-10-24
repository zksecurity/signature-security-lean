import Proofs.Runtime.Caliper.BLSSignatureTailAcceptance
import Proofs.Runtime.Caliper.BLSSignatureTailSource
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource

namespace SignaturesTest.CaliperBLSSignatureTail

-- Word arithmetic tests the actual wiring. The field-source theorems remain
-- general; this finite executable fixture is not presented as a field model.
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
    capacityPred := 2
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
private theorem goodFits : layout.good.input.representation.encoding.words + (BLSSignatureTail.goodContext layout).representation.encoding.words < 2 ^ 16 := by decide
private theorem badFits : layout.bad.input.representation.encoding.words + (BLSSignatureTail.badContext layout).representation.encoding.words < 2 ^ 16 := by decide
private def good := BLSSignatureTail.goodCode (base := base) (key := .nat) (val := .atom ()) (slots := 3)
  layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers port draw
private def goodDenote := BLSSignatureTail.goodDenote (base := base) (key := .nat) (val := .atom ()) (slots := 3)
  layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers drawSource
private theorem good_correct : Interactive.RefinesOn (BLSSignatureTail.goodReady layout) port .unit (BLSSignatureTail.goodInput layout goodFits)
    (CacheScalarResult.output accumulation.good).representation goodDenote good :=
  BLSSignatureTail.good_refines (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource)
    layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers port draw_correct goodFits
private theorem good_time : Interactive.TimeBoundOn (BLSSignatureTail.goodReady layout) port .unit (BLSSignatureTail.goodInput layout goodFits) good
    (BLSSignatureTail.goodTime (base := base) (key := .nat) (val := .atom ()) layout 4 6 6 6 6) :=
  BLSSignatureTail.good_time (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource)
    layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers port draw_correct draw_time mul_bound add_bound sub_bound div_bound goodFits
example : (good.lower port).descriptionWords ≤ BLSSignatureTail.goodWords (base := base) (key := .nat) (val := .atom ()) layout 20 27 27 27 27 :=
  BLSSignatureTail.good_words (base := base) (key := .nat) (val := .atom ()) (slots := 3) layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers port draw draw_words mul_bound add_bound sub_bound div_bound
example : WordIO.NamesAccounted (good.lower port) 5 :=
  BLSSignatureTail.good_names (drawNames := 3) (names := 3) (base := base) (key := .nat) (val := .atom ()) (slots := 3) layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers port draw draw_names mul_names.accounted add_names.accounted sub_names.accounted div_names.accounted
example : (good.lower port).DescriptionFits :=
  BLSSignatureTail.good_descriptionFits (base := base) (key := .nat) (val := .atom ()) (slots := 3) layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers port draw draw_fits draw_names (by decide)
private def bad := BLSSignatureTail.badCode (base := base) (key := .nat) (val := .atom ()) (slots := 3)
  layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers port draw
private def badDenote := BLSSignatureTail.badDenote (base := base) (key := .nat) (val := .atom ()) (slots := 3)
  layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers drawSource
private theorem bad_correct : Interactive.RefinesOn (BLSSignatureTail.badReady layout) port .unit (BLSSignatureTail.badInput layout badFits)
    (CacheScalarResult.output accumulation.bad).representation badDenote bad :=
  BLSSignatureTail.bad_refines (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource)
    layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers port draw_correct badFits
private theorem bad_time : Interactive.TimeBoundOn (BLSSignatureTail.badReady layout) port .unit (BLSSignatureTail.badInput layout badFits) bad
    (BLSSignatureTail.badTime (base := base) (key := .nat) (val := .atom ()) layout 4 6 6 6 118 6) :=
  BLSSignatureTail.bad_time (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource)
    layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers port draw_correct draw_time mul_bound add_bound sub_bound neg_bound div_bound badFits
example : (bad.lower port).descriptionWords ≤ BLSSignatureTail.badWords (base := base) (key := .nat) (val := .atom ()) layout 20 27 27 27 631 27 :=
  BLSSignatureTail.bad_words (base := base) (key := .nat) (val := .atom ()) (slots := 3) layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers port draw draw_words mul_bound add_bound sub_bound neg_bound div_bound
example : WordIO.NamesAccounted (bad.lower port) 5 :=
  BLSSignatureTail.bad_names (drawNames := 3) (names := 3) (base := base) (key := .nat) (val := .atom ()) (slots := 3) layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers port draw draw_names mul_names.accounted add_names.accounted sub_names.accounted neg_names.accounted div_names.accounted
example : (bad.lower port).DescriptionFits :=
  BLSSignatureTail.bad_descriptionFits (base := base) (key := .nat) (val := .atom ()) (slots := 3) layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers port draw draw_fits draw_names (by decide)
private def goodValue (tokens : List (Nat × Word 16)) (coefficients : List (Word 16)) (entries : List (Nat × Word 16))
    (valid : ((tokens.length ≤ 3 ∧ ∀ token ∈ tokens, token.1 < 256) ∧ coefficients.length ≤ 4) ∧
      entries.length ≤ 3 ∧ ∀ entry ∈ entries, entry.1 < 256) : layout.good.input.Value :=
  ⟨((tokens, coefficients), entries),
    ⟨⟨valid.1.1.1, fun token member => ⟨valid.1.1.2 token member, trivial⟩⟩, valid.1.2, fun _ _ => trivial⟩,
    valid.2.1, fun entry member => ⟨valid.2.2 entry member, trivial⟩⟩
private def badValue (tokens : List (Nat × Word 16)) (coefficients : List (Word 16)) (entries : List (Nat × (Word 16 × Word 16)))
    (valid : ((tokens.length ≤ 3 ∧ ∀ token ∈ tokens, token.1 < 256) ∧ coefficients.length ≤ 4) ∧
      entries.length ≤ 3 ∧ ∀ entry ∈ entries, entry.1 < 256) : layout.bad.input.Value :=
  ⟨((tokens, coefficients), entries),
    ⟨⟨valid.1.1.1, fun token member => ⟨valid.1.1.2 token member, trivial⟩⟩, valid.1.2, fun _ _ => trivial⟩,
    valid.2.1, fun entry member => ⟨valid.2.2 entry member, trivial, trivial⟩⟩
private def goodContext (value : layout.good.input.Value) (target : Fin 256) (beta hashes : Word 16) : BLSSignatureTail.GoodInput layout :=
  (value, ⟨(target.val, beta, hashes), target.isLt, trivial, trivial⟩)
private def badContext (value : layout.bad.input.Value) (target : Fin 256) (beta : Word 16) : BLSSignatureTail.BadInput layout :=
  (value, ⟨(target.val, beta), target.isLt, trivial⟩)
private def goodTwo := goodContext (goodValue [(1, 72), (2, 71)] [3, 4] [] (by decide)) 3 20 40
private def goodMissing := goodContext (goodValue [(1, 72), (2, 71)] [3] [] (by decide)) 3 20 40
private def goodSurplus := goodContext (goodValue [(1, 72), (2, 71)] [3, 4, 99, 100] [] (by decide)) 3 20 40
private def goodRepeated := goodContext (goodValue [(2, 72), (2, 71)] [3, 4] [] (by decide)) 3 20 40
private def goodReuse := goodContext (goodValue [(1, 72), (2, 71)] [] [] (by decide)) 2 20 40
private def goodHit := goodContext (goodValue [(2, 71)] [3] [(2, 5)] (by decide)) 3 10 30
private def goodEmpty := goodContext (goodValue [] [99] [(1, 7), (2, 2)] (by decide)) 2 5 5
private def badTwo := badContext (badValue [(1, 72), (2, 71)] [3, 4] [] (by decide)) 3 77
private def badMissing := badContext (badValue [(1, 72), (2, 71)] [3] [] (by decide)) 3 77
private def badSurplus := badContext (badValue [(1, 72), (2, 71)] [3, 4, 99, 100] [] (by decide)) 3 77
private def badRepeated := badContext (badValue [(2, 72), (2, 71)] [3, 4] [] (by decide)) 3 77
private def badReuse := badContext (badValue [(1, 72), (2, 71)] [] [] (by decide)) 2 77
private def badHit := badContext (badValue [(2, 71)] [3] [(2, (5, 2))] (by decide)) 3 77
private def badEmpty := badContext (badValue [] [99] [(1, (3, 7)), (2, (5, 0))] (by decide)) 2 0

example : BLSSignatureTail.goodReady layout goodTwo := by unfold BLSSignatureTail.goodReady; decide
example : BLSSignatureTail.badReady layout badTwo := by unfold BLSSignatureTail.badReady; decide
example : BLSSignatureTail.goodReady layout goodHit := by unfold BLSSignatureTail.goodReady; decide
example : BLSSignatureTail.badReady layout badEmpty := by unfold BLSSignatureTail.badReady; decide
example : ¬ BLSSignatureTail.goodReady layout (goodContext (goodValue [(1, 72), (2, 71)] [3, 4] [(2, 5)] (by decide)) 3 20 40) := by
  unfold BLSSignatureTail.goodReady; decide

private def run {A : Type} (input : Representation 16 A) (code : Interactive.Code 16) (value : A) (replies : List (Word 16)) := do
  let initial := input.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 50000 (code.lower port) before replies
  pure (result.state.bufs 0, result.state.bufs 200, result.state.caps 200, result.state.regs 99, result.state.tapePos,
    (List.range 32).all (fun i => result.state.caps (i + 1) == 0), result.trace, result.remaining)
private def events (values : List (Word 16)) : List (WordIO.Event 16) := values.flatMap (fun value => [.invoke, .input value])

open Lean in
run_cmd do
  for (value, replies, expected, consumed, remaining) in [
      (goodTwo, [5, 7, 55, 88], #[5, 3, 3, 55, 1, 7, 2, 5], [5, 7, 55], [88]),
      (goodMissing, [5, 7, 27], #[5, 3, 3, 27, 1, 7, 2, 5], [5, 7, 27], []),
      (goodSurplus, [5, 7, 55, 88], #[5, 3, 3, 55, 1, 7, 2, 5], [5, 7, 55], [88]),
      (goodRepeated, [5, 47], #[5, 2, 3, 47, 2, 5, 0, 0], [5, 47], []),
      (goodReuse, [5, 7, 88], #[12, 2, 1, 7, 2, 5, 0, 0], [5, 7], [88]),
      (goodHit, [23], #[5, 2, 3, 23, 2, 5, 0, 0], [23], []),
      (goodEmpty, [], #[5, 2, 1, 7, 2, 2, 0, 0], [], [])] do
    unless run (BLSSignatureTail.goodInput layout goodFits) good value replies == some (expected, #[77], 4, 91, 9, true, events consumed, remaining) do
      throwError "scalar signature tail failed for {value.1.val}"
  for (value, replies, expected, consumed, remaining) in [
      (badTwo, [5, 2, 7, 3, 55, 6, 88], #[1, 3, 3, 55, 6, 1, 7, 3, 2, 5, 2], [5, 2, 7, 3, 55, 6], [88]),
      (badMissing, [5, 2, 7, 3, 21, 0], #[1, 3, 3, 21, 0, 1, 7, 3, 2, 5, 2], [5, 2, 7, 3, 21, 0], []),
      (badSurplus, [5, 2, 7, 3, 55, 6, 88], #[1, 3, 3, 55, 6, 1, 7, 3, 2, 5, 2], [5, 2, 7, 3, 55, 6], [88]),
      (badRepeated, [5, 2, 47, 2], #[1, 2, 3, 47, 2, 2, 5, 2, 0, 0, 0], [5, 2, 47, 2], []),
      (badReuse, [5, 0, 7, 3, 88], #[0, 2, 1, 7, 3, 2, 5, 0, 0, 0, 0], [5, 0, 7, 3], [88]),
      (badHit, [21, 0], #[1, 2, 3, 21, 0, 2, 5, 2, 0, 0, 0], [21, 0], []),
      (badEmpty, [], #[0, 2, 1, 3, 7, 2, 5, 0, 0, 0, 0], [], []),
      (badTwo, [5, 2, 7, 3, 43, 6], #[0, 3, 3, 43, 6, 1, 7, 3, 2, 5, 2], [5, 2, 7, 3, 43, 6], [])] do
    unless run (BLSSignatureTail.badInput layout badFits) bad value replies == some (expected, #[77], 4, 91, 9, true, events consumed, remaining) do
      throwError "pair signature tail failed for {value.1.val}"
  unless (run (BLSSignatureTail.goodInput layout goodFits) good goodMissing [5]).isNone do throwError "zero-coefficient lookup did not need a reply"
  unless (run (BLSSignatureTail.goodInput layout goodFits) good goodTwo [5, 7]).isNone do throwError "final scalar lookup accepted no reply"
  unless (run (BLSSignatureTail.badInput layout badFits) bad badTwo [5, 2, 7, 3, 55]).isNone do throwError "final pair lookup accepted one reply"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``BLSSignatureTail.good_refines, ``BLSSignatureTail.bad_refines,
      ``BLSSignatureTail.good_preserves, ``BLSSignatureTail.bad_preserves,
      ``BLSSignatureTail.good_source, ``BLSSignatureTail.bad_source,
      ``BLSSignatureTail.good_time, ``BLSSignatureTail.bad_time,
      ``BLSSignatureTail.good_words, ``BLSSignatureTail.bad_words,
      ``BLSSignatureTail.good_names, ``BLSSignatureTail.bad_names,
      ``BLSSignatureTail.good_resources, ``BLSSignatureTail.bad_resources,
      ``BLSSignatureTail.good_descriptionFits, ``BLSSignatureTail.bad_descriptionFits,
      ``TokenEvaluation.buffers, ``good_correct, ``bad_correct, ``good_time, ``bad_time] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"
end SignaturesTest.CaliperBLSSignatureTail
