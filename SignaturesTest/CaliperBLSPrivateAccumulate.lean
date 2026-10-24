import Proofs.Runtime.Caliper.BLSPrivateAccumulateOracle
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource

namespace SignaturesTest.CaliperBLSPrivateAccumulate

-- Word arithmetic tests the actual wiring. The field-source theorems remain
-- general; this finite executable fixture is not presented as a field model.
private def base (_ : Unit) : Type := Word 8
private instance : Mul (Ty.Value base (.atom ())) := inferInstanceAs (Mul (Word 8))
private instance : Add (Ty.Value base (.atom ())) := inferInstanceAs (Add (Word 8))
private inductive Op : Ty Unit → Ty Unit → Type
  | equal : Op (.pair .nat .nat) .bool
private def primitives : Primitives base Op where
  execute instruction := match instruction with | .equal => fun value => decide (value.1 = value.2)
  cost _ _ := 1
private def comparison : Expr Op [.nat, .nat] .bool := .op .equal (.pair (.var .here) (.var (.there .here)))
private theorem comparison_correct (left right : Nat) : comparison.denote primitives (left, right, ()) = decide (left = right) := rfl

private def layout : BLSPrivateAccumulate.Layouts 8 Nat (Word 8) where
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

private def binary (op : BinOp) : Implementation .unit layout.arithmetic.pair layout.cache.value
    (fun value => op.eval value.1 value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit op layout.cache.wordFits).viewInput layout.arithmetic.pair.representation
    (fun value => value.val) (fun _ => rfl)).viewOutput layout.cache.value.representation
      (fun value => ⟨op.eval value.val.1 value.val.2, trivial⟩) (fun _ => rfl)
private def mul : Implementation .unit layout.arithmetic.pair layout.cache.value (fun value => value.1 * value.2) := binary .mul
private def add : Implementation .unit layout.arithmetic.pair layout.cache.value (fun value => value.1 + value.2) := binary .add
private theorem mul_bound : mul.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem add_bound : add.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem mul_names : NamesBound mul.program.code 3 := by constructor <;> decide
private theorem add_names : NamesBound add.program.code 3 := by constructor <;> decide
private theorem reserve : 3 + 4 < 2 ^ 8 := by decide

private def sampleSpec : OracleSpec Unit := fun _ => layout.cache.value.Value
private def replyView : (Σ _ : layout.cache.lookup.unit.Value, layout.cache.value.Value) ≃ layout.cache.value.Value where
  toFun := Sigma.snd
  invFun value := ⟨⟨(), trivial⟩, value⟩
  left_inv value := by rcases value with ⟨⟨position, valid⟩, answer⟩; cases position; rfl
  right_inv _ := rfl
private def port : Interactive.Port 8 sampleSpec where
  Request := layout.cache.lookup.unit.Value
  source _ := ()
  request := layout.cache.lookup.unit.representation
  reply := layout.cache.value.representation.transport replyView
private def drawSource : OracleComp sampleSpec layout.cache.value.Value := queryBind () Pure.pure
private def draw : Interactive.Code 8 := .query
private theorem draw_correct : Interactive.Refines port .unit layout.cache.lookup.unit.representation layout.cache.value.representation
    (fun _ => drawSource) draw := by
  have projected := (Interactive.Refines.query port .unit).viewOutput layout.cache.value.representation replyView (fun _ => rfl)
  convert projected using 1 <;> rfl
private theorem draw_time : Interactive.TimeBound port .unit layout.cache.lookup.unit.representation draw 4 := Interactive.TimeBound.query
private theorem draw_words : (draw.lower port).descriptionWords ≤ 20 := by decide
private theorem draw_names : WordIO.NamesBound (draw.lower port) 3 := by constructor <;> decide
private theorem draw_fits : (draw.lower port).DescriptionFits := WordIO.exchange_descriptionFits 0 1 (by decide) (by decide)

private def good := BLSPrivateAccumulate.goodCode (base := base) (key := .nat) (val := .atom ()) layout primitives comparison comparison_correct
  mul add mul_names.buffers reserve add_names.buffers port draw
private def bad := BLSPrivateAccumulate.badCode (base := base) (key := .nat) (val := .atom ()) layout primitives comparison comparison_correct
  mul add mul_names.buffers reserve add_names.buffers port draw
private def goodUpdate := BLSPrivateAccumulate.goodUpdate layout mul add mul_names.buffers reserve
private def badUpdate := BLSPrivateAccumulate.badUpdate layout mul add mul_names.buffers reserve add_names.buffers
private theorem goodUpdate_buffers : goodUpdate.program.code.memBound ≤ 4 :=
  BLSPrivateAccumulate.goodUpdate_buffers layout mul add mul_names.buffers reserve add_names.buffers
private theorem badUpdate_buffers : badUpdate.program.code.memBound ≤ 5 :=
  BLSPrivateAccumulate.badUpdate_buffers layout mul add mul_names.buffers reserve add_names.buffers

private theorem good_time : Interactive.TimeBound port .unit layout.good.input.representation good
    (EncodedCacheAccumulate.timeBudget (base := base) (key := .nat) (val := .atom ()) layout.good 4
      (BLSAccumulate.goodTime layout.arithmetic 6 6)) :=
  BLSPrivateAccumulate.good_time (base := base) (key := .nat) (val := .atom ()) layout primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers
    port draw_correct draw_time mul_bound add_bound
private theorem bad_time : Interactive.TimeBound port .unit layout.bad.input.representation bad
    (EncodedCacheAccumulate.timeBudget (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad (PairSampling.timeBudget layout.cache.value layout.cache.value 4 4)
      (BLSAccumulate.badTime layout.arithmetic 6 6)) :=
  BLSPrivateAccumulate.bad_time (base := base) (key := .nat) (val := .atom ()) layout primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers
    port draw_correct draw_time mul_bound add_bound
example : (good.lower port).descriptionWords ≤ EncodedCacheAccumulate.codeBudget (base := base) (key := .nat) (val := .atom ())
    layout.good 20 (BLSAccumulate.goodCode layout.arithmetic 27 27) :=
  BLSPrivateAccumulate.good_words (base := base) (key := .nat) (val := .atom ()) layout primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers
    port draw_words mul_bound add_bound
example : (bad.lower port).descriptionWords ≤ EncodedCacheAccumulate.codeBudget (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ()))
    layout.bad (PairSampling.codeBudget layout.cache.value layout.cache.value 20 20) (BLSAccumulate.badCode layout.arithmetic 27 27) :=
  BLSPrivateAccumulate.bad_words (base := base) (key := .nat) (val := .atom ()) layout primitives comparison comparison_correct mul add mul_names.buffers reserve add_names.buffers
    port draw_words mul_bound add_bound
example : (good.lower port).DescriptionFits :=
  EncodedCacheAccumulate.descriptionFits (base := base) (key := .nat) (val := .atom ()) layout.good primitives comparison comparison_correct
    goodUpdate goodUpdate_buffers (by decide) port draw draw_fits draw_names (by decide)
example : (bad.lower port).DescriptionFits :=
  EncodedCacheAccumulate.descriptionFits (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad primitives comparison comparison_correct
    badUpdate badUpdate_buffers (by decide) port (BLSPrivateAccumulate.pairSampler (base := base) (key := .nat) (val := .atom ()) layout port draw)
    (PairSampling.descriptionFits _ _ _ _ port draw draw draw_fits draw_fits draw_names (by decide))
    (PairSampling.names _ _ _ _ port draw draw draw_names draw_names) (by decide)
example : WordIO.NamesAccounted (good.lower port) 5 :=
  EncodedCacheAccumulate.names (drawNames := 3) (updateNames := 3) (base := base) (key := .nat) (val := .atom ()) layout.good primitives comparison comparison_correct
    goodUpdate goodUpdate_buffers (by decide) port draw draw_names
    (BLSAccumulate.good_names layout.arithmetic 3 mul add mul_names.accounted add_names.accounted mul_names.buffers reserve)
example : WordIO.NamesAccounted (bad.lower port) 5 :=
  EncodedCacheAccumulate.names (drawNames := 4) (updateNames := 3) (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad primitives comparison comparison_correct
    badUpdate badUpdate_buffers (by decide) port (BLSPrivateAccumulate.pairSampler (base := base) (key := .nat) (val := .atom ()) layout port draw)
    (PairSampling.names _ _ _ _ port draw draw draw_names draw_names)
    (BLSAccumulate.bad_names layout.arithmetic 3 mul add mul_names.accounted add_names.accounted mul_names.buffers reserve add_names.buffers)

private theorem good_valid (key : Nat) (default : Word 8) (entries : List (Nat × Word 8)) (coefficient acc : Word 8) :
    layout.good.input.valid ((key, default, entries, ()), coefficient, acc) ↔
      (key < 256 ∧ entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256) ∧
      ((lookupValue key default entries).1 = false → entries.length ≤ 1) := by
  change (((key < 256 ∧ True ∧ (entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256 ∧ True) ∧ True) ∧
    ((lookupValue key default entries).1 = false → entries.length ≤ 1)) ∧ True ∧ True) ↔ _
  simp only [and_true, true_and]
private theorem bad_valid (key : Nat) (default : Word 8 × Word 8) (entries : List (Nat × (Word 8 × Word 8)))
    (coefficient : Word 8) (acc : Word 8 × Word 8) :
    layout.bad.input.valid ((key, default, entries, ()), coefficient, acc) ↔
      (key < 256 ∧ entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256) ∧
      ((lookupValue key default entries).1 = false → entries.length ≤ 1) := by
  change (((key < 256 ∧ (True ∧ True) ∧ (entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256 ∧ True ∧ True) ∧ True) ∧
    ((lookupValue key default entries).1 = false → entries.length ≤ 1)) ∧ True ∧ True ∧ True) ↔ _
  simp only [and_true, true_and]

private def goodHit : layout.good.input.Value := ⟨((2, 99, [(1, 7), (2, 13)], ()), 3, 11), by rw [good_valid]; decide +kernel⟩
private def goodMiss : layout.good.input.Value := ⟨((2, 99, [(1, 7)], ()), 3, 11), by rw [good_valid]; decide +kernel⟩
private def goodEmpty : layout.good.input.Value := ⟨((2, 99, [], ()), 3, 11), by rw [good_valid]; decide +kernel⟩
private def goodDuplicate : layout.good.input.Value := ⟨((2, 99, [(2, 7), (2, 13)], ()), 3, 11), by rw [good_valid]; decide +kernel⟩
private def goodZero : layout.good.input.Value := ⟨((2, 99, [(2, 7)], ()), 0, 11), by rw [good_valid]; decide +kernel⟩
private def badHit : layout.bad.input.Value := ⟨((2, (99, 98), [(1, (7, 13)), (2, (0, 13))], ()), 3, (11, 17)), by rw [bad_valid]; decide +kernel⟩
private def badMiss : layout.bad.input.Value := ⟨((2, (99, 98), [(1, (7, 13))], ()), 3, (11, 17)), by rw [bad_valid]; decide +kernel⟩
private def badEmpty : layout.bad.input.Value := ⟨((2, (99, 98), [], ()), 3, (11, 17)), by rw [bad_valid]; decide +kernel⟩
private def badDuplicate : layout.bad.input.Value := ⟨((2, (99, 98), [(2, (7, 13)), (2, (0, 0))], ()), 3, (11, 17)), by rw [bad_valid]; decide +kernel⟩

example : ¬ layout.good.input.valid ((3, 99, [(1, 7), (2, 13)], ()), 3, 11) := by rw [good_valid]; decide +kernel
example : ¬ layout.bad.input.valid ((3, (99, 98), [(1, (7, 13)), (2, (0, 0))], ()), 3, (11, 17)) := by rw [bad_valid]; decide +kernel
example : ¬ layout.good.input.valid ((256, 99, [], ()), 3, 11) := by rw [good_valid]; decide +kernel

-- Runtime fixtures preserve a caller-owned buffer with spare capacity, a high
-- register and tape position. All scratch capacities must be released.
private def run {A : Type} (input : Layout 8 A) (code : Interactive.Code 8) (value : input.Value) (replies : List (Word 8)) := do
  let initial := input.representation.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 50000 (code.lower port) before replies
  pure (result.state.bufs 0, result.state.bufs 200, result.state.caps 200, result.state.regs 99, result.state.tapePos,
    (List.range 16).all (fun i => result.state.caps (i + 1) == 0), result.trace, result.remaining)

open Lean in
run_cmd do
  for (value, replies, expected, trace, remaining) in [
      (goodHit, [88], #[50, 2, 1, 7, 2, 13], [], [88]),
      (goodHit, [], #[50, 2, 1, 7, 2, 13], [], []),
      (goodMiss, [9, 88], #[38, 2, 2, 9, 1, 7], [.invoke, .input 9], [88]),
      (goodEmpty, [0], #[11, 1, 2, 0, 0, 0], [.invoke, .input 0], []),
      (goodDuplicate, [], #[32, 2, 2, 7, 2, 13], [], []),
      (goodZero, [], #[11, 1, 2, 7, 0, 0], [], [])] do
    unless run layout.good.input good value replies == some (expected, #[77], 4, 91, 9, true, trace, remaining) do
      throwError "scalar cache accumulation failed for {value.val}"
  for (value, replies, expected, trace, remaining) in [
      (badHit, [88], #[11, 56, 2, 1, 7, 13, 2, 0, 13], [], [88]),
      (badMiss, [9, 12, 88], #[38, 53, 2, 2, 9, 12, 1, 7, 13], [.invoke, .input 9, .invoke, .input 12], [88]),
      (badEmpty, [0, 1], #[11, 20, 1, 2, 0, 1, 0, 0, 0], [.invoke, .input 0, .invoke, .input 1], []),
      (badDuplicate, [], #[32, 56, 2, 2, 7, 13, 2, 0, 0], [], [])] do
    unless run layout.bad.input bad value replies == some (expected, #[77], 4, 91, 9, true, trace, remaining) do
      throwError "pair cache accumulation failed for {value.val}"
  unless (run layout.good.input good goodMiss []).isNone do throwError "scalar miss accepted absent reply"
  unless (run layout.bad.input bad badMiss [9]).isNone do throwError "pair miss accepted just one reply"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``BLSAccumulate.good, ``BLSAccumulate.bad, ``BLSAccumulate.good_bounded, ``BLSAccumulate.bad_bounded,
      ``BLSAccumulate.good_names, ``BLSAccumulate.bad_names, ``BLSAccumulate.goodSource, ``BLSAccumulate.badSource,
      ``BLSAccumulate.goodSource_bounded, ``BLSAccumulate.badSource_bounded,
      ``EncodedCacheAccumulate.refines, ``EncodedCacheAccumulate.listCache, ``EncodedCacheAccumulate.observe_listCache,
      ``EncodedCacheAccumulate.cache_growth, ``EncodedCacheAccumulate.time_bound, ``EncodedCacheAccumulate.code_bound,
      ``EncodedCacheAccumulate.names, ``EncodedCacheAccumulate.descriptionFits, ``EncodedCacheAccumulate.buffers,
      ``EncodedCacheAccumulate.staticMemory, ``EncodedCacheAccumulate.memoryBound,
      ``BLSPrivateAccumulate.good_refines, ``BLSPrivateAccumulate.bad_refines,
      ``BLSPrivateAccumulate.good_time, ``BLSPrivateAccumulate.bad_time,
      ``BLSPrivateAccumulate.good_words, ``BLSPrivateAccumulate.bad_words,
      ``BLSPrivateAccumulate.good_privateOracle, ``BLSPrivateAccumulate.bad_privateOracle,
      ``draw_correct, ``good_time, ``bad_time] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperBLSPrivateAccumulate
