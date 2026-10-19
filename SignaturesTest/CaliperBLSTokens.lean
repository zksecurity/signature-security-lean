import Signatures.Runtime.Caliper.BLSTokensSource
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource

namespace SignaturesTest.CaliperBLSTokens

-- Word arithmetic tests the actual wiring. The field-source theorems remain
-- general; this finite executable fixture is not presented as a field model.
private def base (_ : Unit) : Type := Word 16
private instance (n : Nat) : OfNat (Ty.Value base (.atom ())) n := inferInstanceAs (OfNat (Word 16) n)
private instance : Zero (Ty.Value base (.atom ())) := inferInstanceAs (Zero (Word 16))
private instance : Mul (Ty.Value base (.atom ())) := inferInstanceAs (Mul (Word 16))
private instance : Add (Ty.Value base (.atom ())) := inferInstanceAs (Add (Word 16))
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
    capacityPred := 1
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
private def good := BLSTokens.goodCode (base := base) (key := .nat) (val := .atom ()) (slots := 3)
  layout (by trivial) primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers port draw
private def bad := BLSTokens.badCode (base := base) (key := .nat) (val := .atom ()) (slots := 3)
  layout (by trivial) primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers port draw
private def goodDenote := BLSTokens.goodDenote (base := base) (key := .nat) (val := .atom ()) (slots := 3)
  layout (by trivial) primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers drawSource
private def badDenote := BLSTokens.badDenote (base := base) (key := .nat) (val := .atom ()) (slots := 3)
  layout (by trivial) primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers drawSource

private def goodValue (tokens : List (Nat × Word 16)) (coefficients : List (Word 16)) (entries : List (Nat × Word 16))
    (valid : ((tokens.length ≤ 3 ∧ ∀ token ∈ tokens, token.1 < 256) ∧ coefficients.length ≤ 4) ∧
      entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256) : layout.good.input.Value :=
  ⟨((tokens, coefficients), entries),
    ⟨⟨valid.1.1.1, fun token member => ⟨valid.1.1.2 token member, trivial⟩⟩, valid.1.2, fun _ _ => trivial⟩,
    valid.2.1, fun entry member => ⟨valid.2.2 entry member, trivial⟩⟩
private def badValue (tokens : List (Nat × Word 16)) (coefficients : List (Word 16)) (entries : List (Nat × (Word 16 × Word 16)))
    (valid : ((tokens.length ≤ 3 ∧ ∀ token ∈ tokens, token.1 < 256) ∧ coefficients.length ≤ 4) ∧
      entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256) : layout.bad.input.Value :=
  ⟨((tokens, coefficients), entries),
    ⟨⟨valid.1.1.1, fun token member => ⟨valid.1.1.2 token member, trivial⟩⟩, valid.1.2, fun _ _ => trivial⟩,
    valid.2.1, fun entry member => ⟨valid.2.2 entry member, trivial, trivial⟩⟩
private def goodEmpty := goodValue [] [3, 4, 55, 66] [(1, 7), (2, 13)] (by decide)
private def goodTwo := goodValue [(1, 72), (2, 71)] [3, 4] [] (by decide)
private def goodMissing := goodValue [(1, 72), (2, 71)] [3] [] (by decide)
private def goodSurplus := goodValue [(1, 72), (2, 71)] [3, 4, 55, 66] [] (by decide)
private def goodRepeated := goodValue [(2, 72), (2, 71)] [3, 4] [] (by decide)
private def goodNoCoefficients := goodValue [(1, 72), (2, 71)] [] [] (by decide)
private def goodHit := goodValue [(2, 71)] [3] [(2, 7)] (by decide)
private def goodOne := goodValue [(2, 71)] [3] [] (by decide)
private def badEmpty := badValue [] [3, 4, 55, 66] [(1, (7, 13)), (2, (0, 13))] (by decide)
private def badTwo := badValue [(1, 72), (2, 71)] [3, 4] [] (by decide)
private def badMissing := badValue [(1, 72), (2, 71)] [3] [] (by decide)
private def badSurplus := badValue [(1, 72), (2, 71)] [3, 4, 55, 66] [] (by decide)
private def badRepeated := badValue [(2, 72), (2, 71)] [3, 4] [] (by decide)
private def badNoCoefficients := badValue [(1, 72), (2, 71)] [] [] (by decide)
private def badHit := badValue [(2, 71)] [3] [(2, (7, 13))] (by decide)

example : layout.good.ready goodTwo := by unfold TokenEvaluation.Layouts.ready; decide
example : layout.bad.ready badMissing := by unfold TokenEvaluation.Layouts.ready; decide
example : layout.good.ready goodEmpty := by unfold TokenEvaluation.Layouts.ready; decide
-- The two stored tokens fit, even though the allocated token capacity is three.
example : ¬ layout.good.ready (goodValue [(1, 72), (2, 71)] [3, 4] [(2, 7)] (by decide)) := by
  unfold TokenEvaluation.Layouts.ready; decide
example : ¬ layout.good.input.valid (([(256, 71)], []), []) := by
  intro valid
  have impossible : 256 < 256 := (valid.1.1.2 (256, 71) (by simp)).1
  omega
example : ¬ layout.good.input.valid (([], [1, 2, 3, 4, 5]), []) := by
  intro valid
  have impossible : 5 ≤ 4 := valid.1.2.1
  omega

private theorem good_correct : Interactive.RefinesOn layout.good.ready port .unit layout.good.input.representation
    rows.good.state.representation goodDenote good :=
  BLSTokens.good_refines (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource)
    layout (by trivial) primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers port draw_correct
private theorem bad_correct : Interactive.RefinesOn layout.bad.ready port .unit layout.bad.input.representation
    rows.bad.state.representation badDenote bad :=
  BLSTokens.bad_refines (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource)
    layout (by trivial) primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers port draw_correct
example : Interactive.TimeBoundOn layout.good.ready port .unit layout.good.input.representation good
    (TokenEvaluation.timeBudget (base := base) (key := .nat) (val := .atom ()) layout.good 4 (BLSAccumulate.goodTime accumulation.arithmetic 6 6)) :=
  BLSTokens.good_time (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource)
    layout (by trivial) primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers port draw_correct draw_time mul_bound add_bound
example : Interactive.TimeBoundOn layout.bad.ready port .unit layout.bad.input.representation bad
    (TokenEvaluation.timeBudget (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad
      (PairSampling.timeBudget accumulation.cache.value accumulation.cache.value 4 4) (BLSAccumulate.badTime accumulation.arithmetic 6 6)) :=
  BLSTokens.bad_time (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource)
    layout (by trivial) primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers port draw_correct draw_time mul_bound add_bound
example : (good.lower port).descriptionWords ≤ TokenEvaluation.codeBudget (base := base) (key := .nat) (val := .atom ())
    layout.good 20 (BLSAccumulate.goodCode accumulation.arithmetic 27 27) :=
  BLSTokens.good_words (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw)
    layout (by trivial) primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers port draw_words mul_bound add_bound
example : (bad.lower port).descriptionWords ≤ TokenEvaluation.codeBudget (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ()))
    layout.bad (PairSampling.codeBudget accumulation.cache.value accumulation.cache.value 20 20) (BLSAccumulate.badCode accumulation.arithmetic 27 27) :=
  BLSTokens.bad_words (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw)
    layout (by trivial) primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers port draw_words mul_bound add_bound

private def scalarZero : accumulation.cache.value.Value := ⟨0, trivial⟩
private def pairZero : rows.bad.accumulation.cache.value.Value := ⟨(0, 0), trivial, trivial⟩
private def goodUpdate := BLSPrivateAccumulate.goodUpdate accumulation mul add mul_names.buffers reserve
private def badUpdate := BLSPrivateAccumulate.badUpdate accumulation mul add mul_names.buffers reserve add_names.buffers
private theorem goodUpdate_buffers : goodUpdate.program.code.memBound ≤ 4 :=
  BLSPrivateAccumulate.goodUpdate_buffers accumulation mul add mul_names.buffers reserve add_names.buffers
private theorem badUpdate_buffers : badUpdate.program.code.memBound ≤ 5 :=
  BLSPrivateAccumulate.badUpdate_buffers accumulation mul add mul_names.buffers reserve add_names.buffers
example : (good.lower port).DescriptionFits := by
  have accepted := TokenEvaluation.descriptionFits (slots := 4) (drawNames := 3) (base := base) (key := .nat) (val := .atom ())
    layout.good scalarZero scalarZero scalarZero primitives comparison comparison_correct goodUpdate goodUpdate_buffers (by decide)
    port draw draw_fits draw_names (by decide)
  exact accepted
example : (bad.lower port).DescriptionFits := by
  have accepted := TokenEvaluation.descriptionFits (slots := 5) (drawNames := 4) (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ()))
    layout.bad scalarZero pairZero pairZero primitives comparison comparison_correct badUpdate badUpdate_buffers (by decide) port
    (BLSPrivateAccumulate.pairSampler (base := base) (key := .nat) (val := .atom ()) accumulation port draw)
    (PairSampling.descriptionFits accumulation.cache.value accumulation.cache.value accumulation.cache.wordFits accumulation.cache.pairValueFits port draw draw draw_fits draw_fits draw_names (by decide))
    (PairSampling.names accumulation.cache.value accumulation.cache.value accumulation.cache.wordFits accumulation.cache.pairValueFits port draw draw draw_names draw_names) (by decide)
  exact accepted
example : WordIO.NamesAccounted (good.lower port) 5 :=
  TokenEvaluation.names (slots := 4) (drawNames := 3) (updateNames := 3) (base := base) (key := .nat) (val := .atom ())
    layout.good scalarZero scalarZero scalarZero primitives comparison comparison_correct goodUpdate goodUpdate_buffers (by decide)
    port draw draw_names (BLSAccumulate.good_names accumulation.arithmetic 3 mul add mul_names.accounted add_names.accounted mul_names.buffers reserve)
example : WordIO.NamesAccounted (bad.lower port) 5 :=
  TokenEvaluation.names (slots := 5) (drawNames := 4) (updateNames := 3) (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ()))
    layout.bad scalarZero pairZero pairZero primitives comparison comparison_correct badUpdate badUpdate_buffers (by decide) port
    (BLSPrivateAccumulate.pairSampler (base := base) (key := .nat) (val := .atom ()) accumulation port draw)
    (PairSampling.names accumulation.cache.value accumulation.cache.value accumulation.cache.wordFits accumulation.cache.pairValueFits port draw draw draw_names draw_names)
    (BLSAccumulate.bad_names accumulation.arithmetic 3 mul add mul_names.accounted add_names.accounted mul_names.buffers reserve add_names.buffers)
example (answer : rows.good.state.Value) (reached : answer ∈ support (goodDenote goodOne)) : RowEvaluation.room rows.good 1 answer :=
  TokenEvaluation.remaining_room (slots := 4) (base := base) (key := .nat) (val := .atom ()) layout.good scalarZero scalarZero scalarZero
    primitives comparison comparison_correct goodUpdate goodUpdate_buffers (by decide) drawSource goodOne 1 (by decide) answer reached

private def emptyLayout : BLSTokens.Layouts 16 Nat (Word 16) (Word 16) :=
  { layout with capacity := 0, counterFits := by decide, goodStorageFits := by decide, badStorageFits := by decide }
private def emptyInput : emptyLayout.good.input.Value := ⟨(([], [3, 4]), [(1, 7), (2, 13)]), by
  change ((0 ≤ 0 ∧ ∀ token ∈ ([] : List (Nat × Word 16)), token.1 < 256 ∧ True) ∧
    2 ≤ 4 ∧ ∀ value ∈ ([3, 4] : List (Word 16)), True) ∧
    2 ≤ 2 ∧ ∀ entry ∈ ([(1, 7), (2, 13)] : List (Nat × Word 16)), entry.1 < 256 ∧ True
  simp⟩
private def emptyCode := BLSTokens.goodCode (base := base) (key := .nat) (val := .atom ()) (slots := 3)
  emptyLayout (by trivial) primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers port draw
private def run {A : Type} (input : Representation 16 A) (code : Interactive.Code 16) (value : A) (replies : List (Word 16)) := do
  let initial := input.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 200000 (code.lower port) before replies
  pure (result.state.bufs 0, result.state.bufs 200, result.state.caps 200, result.state.regs 99, result.state.tapePos,
    (List.range 24).all (fun i => result.state.caps (i + 1) == 0), result.trace, result.remaining)

open Lean in
run_cmd do
  for (value, replies, expected, trace, remaining) in [
      (goodEmpty, [88], #[0, 2, 1, 7, 2, 13], [], [88]),
      (goodTwo, [9, 12, 88], #[75, 2, 1, 12, 2, 9], [.invoke, .input 9, .invoke, .input 12], [88]),
      (goodSurplus, [9, 12, 88], #[75, 2, 1, 12, 2, 9], [.invoke, .input 9, .invoke, .input 12], [88]),
      (goodMissing, [9, 12], #[27, 2, 1, 12, 2, 9], [.invoke, .input 9, .invoke, .input 12], []),
      (goodNoCoefficients, [9, 12], #[0, 2, 1, 12, 2, 9], [.invoke, .input 9, .invoke, .input 12], []),
      (goodRepeated, [9, 88], #[63, 1, 2, 9, 0, 0], [.invoke, .input 9], [88]),
      (goodHit, [], #[21, 1, 2, 7, 0, 0], [], []),
      (goodOne, [9], #[27, 1, 2, 9, 0, 0], [.invoke, .input 9], [])] do
    unless run layout.good.input.representation good value replies == some (expected, #[77], 4, 91, 9, true, trace, remaining) do
      throwError "scalar transcript evaluation failed for {value.val}"
  for (value, replies, expected, trace, remaining) in [
      (badEmpty, [], #[0, 0, 2, 1, 7, 13, 2, 0, 13], [], []),
      (badTwo, [9, 12, 5, 6, 88], #[47, 60, 2, 1, 5, 6, 2, 9, 12], [.invoke, .input 9, .invoke, .input 12, .invoke, .input 5, .invoke, .input 6], [88]),
      (badSurplus, [9, 12, 5, 6], #[47, 60, 2, 1, 5, 6, 2, 9, 12], [.invoke, .input 9, .invoke, .input 12, .invoke, .input 5, .invoke, .input 6], []),
      (badMissing, [9, 12, 5, 6], #[27, 36, 2, 1, 5, 6, 2, 9, 12], [.invoke, .input 9, .invoke, .input 12, .invoke, .input 5, .invoke, .input 6], []),
      (badNoCoefficients, [9, 12, 5, 6], #[0, 0, 2, 1, 5, 6, 2, 9, 12], [.invoke, .input 9, .invoke, .input 12, .invoke, .input 5, .invoke, .input 6], []),
      (badRepeated, [9, 12, 88], #[63, 84, 1, 2, 9, 12, 0, 0, 0], [.invoke, .input 9, .invoke, .input 12], [88]),
      (badHit, [], #[21, 39, 1, 2, 7, 13, 0, 0, 0], [], [])] do
    unless run layout.bad.input.representation bad value replies == some (expected, #[77], 4, 91, 9, true, trace, remaining) do
      throwError "pair transcript evaluation failed for {value.val}"
  unless run emptyLayout.good.input.representation emptyCode emptyInput [] == some (#[0, 2, 1, 7, 2, 13], #[77], 4, 91, 9, true, [], []) do
    throwError "zero-capacity transcript evaluation failed"
  unless (run layout.good.input.representation good goodMissing [9]).isNone do
    throwError "missing coefficient incorrectly skipped its cache lookup"
  unless (run layout.bad.input.representation bad badMissing [9, 12, 5]).isNone do
    throwError "zero-weight pair row accepted a partial reply"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``TokenEvaluation.prepare, ``TokenEvaluation.prepare_bounded, ``TokenEvaluation.prepare_buffers,
      ``TokenEvaluation.prepare_names, ``TokenEvaluation.foldView_bytes, ``TokenEvaluation.foldValue_rows,
      ``TokenEvaluation.refines, ``TokenEvaluation.time_bound, ``TokenEvaluation.code_bound,
      ``TokenEvaluation.listCache, ``TokenEvaluation.stateFold, ``TokenEvaluation.cache_growth, ``TokenEvaluation.remaining_room,
      ``TokenEvaluation.names, ``TokenEvaluation.descriptionFits, ``TokenEvaluation.resources,
      ``BLSTokens.good_refines, ``BLSTokens.bad_refines, ``BLSTokens.good_time, ``BLSTokens.bad_time,
      ``BLSTokens.good_words, ``BLSTokens.bad_words, ``BLSTokens.good_privateOracle, ``BLSTokens.bad_privateOracle,
      ``BLSTokens.good_source, ``BLSTokens.bad_source, ``good_correct, ``bad_correct] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperBLSTokens
