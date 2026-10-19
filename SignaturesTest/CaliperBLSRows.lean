import Signatures.Runtime.Caliper.BLSRowsOracle
import Signatures.Runtime.Caliper.RowFoldPostcondition
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource

namespace SignaturesTest.CaliperBLSRows

-- Word arithmetic tests the actual wiring. The field-source theorems remain
-- general; this finite executable fixture is not presented as a field model.
private def base (_ : Unit) : Type := Word 8
private instance (n : Nat) : OfNat (Ty.Value base (.atom ())) n := inferInstanceAs (OfNat (Word 8) n)
private instance : Mul (Ty.Value base (.atom ())) := inferInstanceAs (Mul (Word 8))
private instance : Add (Ty.Value base (.atom ())) := inferInstanceAs (Add (Word 8))
private inductive Op : Ty Unit → Ty Unit → Type
  | equal : Op (.pair .nat .nat) .bool
private def primitives : Primitives base Op where
  execute instruction := match instruction with | .equal => fun value => decide (value.1 = value.2)
  cost _ _ := 1
private def comparison : Expr Op [.nat, .nat] .bool := .op .equal (.pair (.var .here) (.var (.there .here)))
private theorem comparison_correct (left right : Nat) : comparison.denote primitives (left, right, ()) = decide (left = right) := rfl

private def accumulation : BLSPrivateAccumulate.Layouts 8 Nat (Word 8) where
  cache := {
    key := Layout.counter 8 256 (by decide) (by decide)
    value := Layout.all (wordRepresentation 8 (by decide))
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
private theorem reserve : 3 + 4 < 2 ^ 8 := by decide

private def sampleSpec : OracleSpec Unit := fun _ => accumulation.cache.value.Value
private def replyView : (Σ _ : accumulation.cache.lookup.unit.Value, accumulation.cache.value.Value) ≃ accumulation.cache.value.Value where
  toFun := Sigma.snd
  invFun value := ⟨⟨(), trivial⟩, value⟩
  left_inv value := by rcases value with ⟨⟨position, valid⟩, answer⟩; cases position; rfl
  right_inv _ := rfl
private def port : Interactive.Port 8 sampleSpec where
  Request := accumulation.cache.lookup.unit.Value
  source _ := ()
  request := accumulation.cache.lookup.unit.representation
  reply := accumulation.cache.value.representation.transport replyView
private def drawSource : OracleComp sampleSpec accumulation.cache.value.Value := queryBind () Pure.pure
private def draw : Interactive.Code 8 := .query
private theorem draw_correct : Interactive.Refines port .unit accumulation.cache.lookup.unit.representation accumulation.cache.value.representation
    (fun _ => drawSource) draw := by
  have projected := (Interactive.Refines.query port .unit).viewOutput accumulation.cache.value.representation replyView (fun _ => rfl)
  convert projected using 1 <;> rfl
private theorem draw_time : Interactive.TimeBound port .unit accumulation.cache.lookup.unit.representation draw 4 := Interactive.TimeBound.query
private theorem draw_words : (draw.lower port).descriptionWords ≤ 20 := by decide
private theorem draw_names : WordIO.NamesBound (draw.lower port) 3 := by constructor <;> decide
private theorem draw_fits : (draw.lower port).DescriptionFits := WordIO.exchange_descriptionFits 0 1 (by decide) (by decide)

private def layout : BLSRows.Layouts 8 Nat (Word 8) (Word 8) where
  accumulation := accumulation
  point := Layout.all (wordRepresentation 8 (by decide))
  goodStorageFits := by decide
  badStorageFits := by decide
private def default : accumulation.cache.value.Value := ⟨99, trivial⟩
private def good (capacity : Nat) := BLSRows.goodCode (base := base) (key := .nat) (val := .atom ())
  layout default primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers capacity port draw
private def bad (capacity : Nat) := BLSRows.badCode (base := base) (key := .nat) (val := .atom ())
  layout default primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers capacity port draw
private def goodInput (capacity : Nat) (countFits : capacity < 256)
    (storageFits : 1 + capacity * 3 + 6 < 256) :=
  RowFold.input (base := base) (key := .nat) (val := .atom ()) layout.good capacity countFits storageFits
private def badInput (capacity : Nat) (countFits : capacity < 256)
    (storageFits : 1 + capacity * 3 + 9 < 256) :=
  RowFold.input (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad capacity countFits storageFits
private def row (message : Fin 256) (point coefficient : Word 8) : layout.good.row.Value :=
  ⟨((message.val, point), coefficient), ⟨message.isLt, trivial⟩, trivial⟩
private abbrev GoodInput (capacity : Nat) := RowFold.Input (base := base) (key := .nat) (val := .atom ()) layout.good capacity
private abbrev BadInput (capacity : Nat) := RowFold.Input (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad capacity
private def goodState (accumulator : Word 8) (entries : List (Nat × Word 8))
    (valid : entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256) : layout.good.state.Value :=
  ⟨(accumulator, entries), trivial, valid.1, fun entry member => ⟨valid.2 entry member, trivial⟩⟩
private def badState (accumulator : Word 8 × Word 8) (entries : List (Nat × (Word 8 × Word 8)))
    (valid : entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256) : layout.bad.state.Value :=
  ⟨(accumulator, entries), ⟨trivial, trivial⟩, valid.1, fun entry member => ⟨valid.2 entry member, trivial, trivial⟩⟩
private def goodEmpty : GoodInput 3 := (⟨[], by decide⟩, goodState 11 [(1, 7), (2, 13)] (by decide))
private def goodZeroCapacity : GoodInput 0 := (⟨[], by decide⟩, goodState 11 [(1, 7), (2, 13)] (by decide))
private def goodTwoMisses : GoodInput 3 :=
  (⟨[row 2 71 3, row 1 72 4], by decide⟩, goodState 11 [] (by decide))
private def goodRepeated : GoodInput 3 :=
  (⟨[row 2 71 3, row 2 72 4], by decide⟩, goodState 11 [] (by decide))
private def goodHit : GoodInput 3 := (⟨[row 2 71 3], by decide⟩, goodState 11 [(2, 7)] (by decide))
private def goodZero : GoodInput 3 := (⟨[row 2 71 0], by decide⟩, goodState 11 [] (by decide))
private def badEmpty : BadInput 3 := (⟨[], by decide⟩, badState (11, 17) [(1, (7, 13)), (2, (0, 13))] (by decide))
private def badTwoMisses : BadInput 3 :=
  (⟨[row 2 71 3, row 1 72 4], by decide⟩, badState (11, 17) [] (by decide))
private def badRepeated : BadInput 3 :=
  (⟨[row 2 71 3, row 2 72 4], by decide⟩, badState (11, 17) [] (by decide))
private def badHit : BadInput 3 := (⟨[row 2 71 3], by decide⟩, badState (11, 17) [(2, (7, 13))] (by decide))

example : RowFold.valid (base := base) (key := .nat) (val := .atom ()) layout.good goodEmpty := by unfold RowFold.valid RowEvaluation.room; decide
example : RowFold.valid (base := base) (key := .nat) (val := .atom ()) layout.good goodTwoMisses := by unfold RowFold.valid RowEvaluation.room; decide
example : RowFold.valid (base := base) (key := .nat) (val := .atom ()) layout.good goodRepeated := by unfold RowFold.valid RowEvaluation.room; decide
example : RowFold.valid (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad badTwoMisses := by unfold RowFold.valid RowEvaluation.room; decide
-- The physical row capacity is three, but only the two occupied rows reserve space.
example : ¬ RowEvaluation.room layout.good 3 goodTwoMisses.2 := by unfold RowEvaluation.room; decide
example : ¬ RowFold.valid (base := base) (key := .nat) (val := .atom ()) layout.good (capacity := 3)
    (⟨[row 2 71 3, row 2 72 4, row 2 73 0], by decide⟩, goodTwoMisses.2) := by unfold RowFold.valid RowEvaluation.room; decide

private theorem good_correct : Interactive.RefinesOn (RowFold.valid (base := base) (key := .nat) (val := .atom ()) layout.good)
    port .unit (goodInput 3 (by decide) (by decide)) layout.good.state.representation
    (BLSRows.goodDenote (base := base) (key := .nat) (val := .atom ()) layout default primitives comparison comparison_correct
      mul add mul_names.buffers reserve add_names.buffers drawSource) (good 3) :=
  BLSRows.good_refines (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource) layout default primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers
    port draw_correct 3 (by decide) (by decide)
private theorem bad_correct : Interactive.RefinesOn (RowFold.valid (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad)
    port .unit (badInput 3 (by decide) (by decide)) layout.bad.state.representation
    (BLSRows.badDenote (base := base) (key := .nat) (val := .atom ()) layout default primitives comparison comparison_correct
      mul add mul_names.buffers reserve add_names.buffers drawSource) (bad 3) :=
  BLSRows.bad_refines (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource) layout default primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers
    port draw_correct 3 (by decide) (by decide)
example : Interactive.TimeBoundOn (RowFold.valid (base := base) (key := .nat) (val := .atom ()) layout.good)
    port .unit (goodInput 3 (by decide) (by decide)) (good 3)
    (RowFold.timeBudget (base := base) (key := .nat) (val := .atom ()) layout.good 3 4 (BLSAccumulate.goodTime accumulation.arithmetic 6 6)) :=
  BLSRows.good_time (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource) layout default primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers
    port draw_correct 3 (by decide) draw_time mul_bound add_bound (by decide)
example : Interactive.TimeBoundOn (RowFold.valid (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad)
    port .unit (badInput 3 (by decide) (by decide)) (bad 3)
    (RowFold.timeBudget (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad 3
      (PairSampling.timeBudget accumulation.cache.value accumulation.cache.value 4 4) (BLSAccumulate.badTime accumulation.arithmetic 6 6)) :=
  BLSRows.bad_time (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource) layout default primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers
    port draw_correct 3 (by decide) draw_time mul_bound add_bound (by decide)
example : ((good 3).lower port).descriptionWords ≤ RowFold.codeBudget (base := base) (key := .nat) (val := .atom ())
    layout.good 3 20 (BLSAccumulate.goodCode accumulation.arithmetic 27 27) :=
  BLSRows.good_words (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) layout default primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers
    port 3 draw_words mul_bound add_bound
example : ((bad 3).lower port).descriptionWords ≤ RowFold.codeBudget (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ()))
    layout.bad 3 (PairSampling.codeBudget accumulation.cache.value accumulation.cache.value 20 20) (BLSAccumulate.badCode accumulation.arithmetic 27 27) :=
  BLSRows.bad_words (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) layout default primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers
    port 3 draw_words mul_bound add_bound

private def goodUpdate := BLSPrivateAccumulate.goodUpdate accumulation mul add mul_names.buffers reserve
private def badUpdate := BLSPrivateAccumulate.badUpdate accumulation mul add mul_names.buffers reserve add_names.buffers
private theorem goodUpdate_buffers : goodUpdate.program.code.memBound ≤ 4 :=
  BLSPrivateAccumulate.goodUpdate_buffers accumulation mul add mul_names.buffers reserve add_names.buffers
private theorem badUpdate_buffers : badUpdate.program.code.memBound ≤ 5 :=
  BLSPrivateAccumulate.badUpdate_buffers accumulation mul add mul_names.buffers reserve add_names.buffers
example : ((good 3).lower port).DescriptionFits :=
  RowFold.descriptionFits (slots := 4) (drawNames := 3) (base := base) (key := .nat) (val := .atom ()) layout.good default primitives comparison comparison_correct
    goodUpdate goodUpdate_buffers (by decide) port 3 (by decide) (by decide) draw draw_fits draw_names (by decide)
example : ((bad 3).lower port).DescriptionFits := by
  have accepted := RowFold.descriptionFits (slots := 5) (drawNames := 4) (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad (BLSRows.pairDefault (base := base) (key := .nat) (val := .atom ()) layout default)
    primitives comparison comparison_correct badUpdate badUpdate_buffers (by decide) port 3 (by decide) (by decide)
    (BLSPrivateAccumulate.pairSampler (base := base) (key := .nat) (val := .atom ()) accumulation port draw)
    (PairSampling.descriptionFits accumulation.cache.value accumulation.cache.value accumulation.cache.wordFits accumulation.cache.pairValueFits port draw draw draw_fits draw_fits draw_names (by decide))
    (PairSampling.names accumulation.cache.value accumulation.cache.value accumulation.cache.wordFits accumulation.cache.pairValueFits port draw draw draw_names draw_names) (by decide)
  exact accepted

private def run {A : Type} (input : Representation 8 A) (code : Interactive.Code 8) (value : A) (replies : List (Word 8)) := do
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
      (goodEmpty, [88], #[11, 2, 1, 7, 2, 13], [], [88]),
      (goodTwoMisses, [9, 12, 88], #[86, 2, 1, 12, 2, 9], [.invoke, .input 9, .invoke, .input 12], [88]),
      (goodRepeated, [9, 88], #[74, 1, 2, 9, 0, 0], [.invoke, .input 9], [88]),
      (goodHit, [], #[32, 1, 2, 7, 0, 0], [], []),
      (goodZero, [9], #[11, 1, 2, 9, 0, 0], [.invoke, .input 9], [])] do
    unless run (goodInput 3 (by decide) (by decide)) (good 3) value replies == some (expected, #[77], 4, 91, 9, true, trace, remaining) do
      throwError "scalar row loop failed for {value.1.val.map Subtype.val}"
  for (value, replies, expected, trace, remaining) in [
      (badEmpty, [], #[11, 17, 2, 1, 7, 13, 2, 0, 13], [], []),
      (badTwoMisses, [9, 12, 5, 6, 88], #[58, 77, 2, 1, 5, 6, 2, 9, 12], [.invoke, .input 9, .invoke, .input 12, .invoke, .input 5, .invoke, .input 6], [88]),
      (badRepeated, [9, 12, 88], #[74, 101, 1, 2, 9, 12, 0, 0, 0], [.invoke, .input 9, .invoke, .input 12], [88]),
      (badHit, [], #[32, 56, 1, 2, 7, 13, 0, 0, 0], [], [])] do
    unless run (badInput 3 (by decide) (by decide)) (bad 3) value replies == some (expected, #[77], 4, 91, 9, true, trace, remaining) do
      throwError "pair row loop failed for {value.1.val.map Subtype.val}"
  unless run (goodInput 0 (by decide) (by decide)) (good 0) goodZeroCapacity [] == some (#[11, 2, 1, 7, 2, 13], #[77], 4, 91, 9, true, [], []) do
    throwError "zero-capacity fold failed"
  unless (run (goodInput 3 (by decide) (by decide)) (good 3) goodTwoMisses [9]).isNone do
    throwError "second row miss accepted absent reply"
  unless (run (badInput 3 (by decide) (by decide)) (bad 3) badTwoMisses [9, 12, 5]).isNone do
    throwError "second pair miss accepted partial reply"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``InteractiveFold.prepare, ``InteractiveFold.refines, ``InteractiveFold.time_bound,
      ``InteractiveFold.code_bound, ``InteractiveFold.names, ``InteractiveFold.descriptionFits, ``InteractiveFold.resources,
      ``RowRequest.prepare, ``RowRequest.prepare_bounded, ``RowRequest.prepare_names,
      ``RowEvaluation.refines, ``RowEvaluation.preserves, ``RowEvaluation.listCache,
      ``RowEvaluation.time_bound, ``RowEvaluation.code_bound, ``RowEvaluation.names, ``RowEvaluation.descriptionFits,
      ``RowFold.refines, ``RowFold.time_bound, ``RowFold.code_bound, ``RowFold.names, ``RowFold.descriptionFits,
      ``RowFold.resources, ``RowFold.cache_growth, ``RowFold.remaining_room, ``RowFold.listCache, ``RowFold.sourceStep_fold,
      ``BLSRows.good_refines, ``BLSRows.bad_refines, ``BLSRows.good_time, ``BLSRows.bad_time,
      ``BLSRows.good_words, ``BLSRows.bad_words, ``BLSRows.good_privateOracle, ``BLSRows.bad_privateOracle,
      ``good_correct, ``bad_correct] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperBLSRows
