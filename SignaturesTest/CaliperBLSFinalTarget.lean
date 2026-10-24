import Proofs.Runtime.Caliper.BLSFinalTargetOracle
import Proofs.Runtime.Caliper.EncodedConstant
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource

namespace SignaturesTest.CaliperBLSFinalTarget

-- Word arithmetic tests the actual wiring. The field-source theorems remain
-- general; this finite executable fixture is not presented as a field model.
private def base (_ : Unit) : Type := Word 8
private instance : Sub (Ty.Value base (.atom ())) := inferInstanceAs (Sub (Word 8))
private instance : Neg (Ty.Value base (.atom ())) := inferInstanceAs (Neg (Word 8))
private instance : Div (Ty.Value base (.atom ())) := inferInstanceAs (Div (Word 8))
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
private def sub : Implementation .unit layout.arithmetic.pair layout.cache.value (fun value => value.1 - value.2) := binary .sub
private def divide : Implementation .unit layout.arithmetic.pair layout.cache.value (fun value => value.1 / value.2) := binary .udiv
private def zero : Implementation .unit layout.cache.value layout.cache.value (fun _ => 0) :=
  Implementation.constant layout.cache.value layout.cache.value ⟨0, trivial⟩ layout.cache.wordFits
private def negArgs : Implementation .unit layout.cache.value layout.arithmetic.pair (fun value => (0, value)) :=
  zero.pair (Implementation.identity layout.cache.value (by decide)) (by decide) layout.cache.wordFits
    (by decide) (by decide) (by decide) (by decide) layout.arithmetic.pair.representation.fits
private def negate : Implementation .unit layout.cache.value layout.cache.value Neg.neg :=
  (negArgs.then sub).castFunction (by funext value; exact BitVec.zero_sub value)
private theorem sub_bound : sub.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem div_bound : divide.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem neg_bound : negate.BoundedBy 118 631 := by
  have zeroBound := Implementation.constant_bounded layout.cache.value layout.cache.value ⟨0, trivial⟩ layout.cache.wordFits
  have paired : negArgs.BoundedBy 112 603 := by
    apply (Implementation.pair_boundedBy zero (Implementation.identity layout.cache.value (by decide))
      layout.cache.wordFits (by decide) (by decide) (by decide) (by decide) layout.arithmetic.pair.representation.fits
      zeroBound (Implementation.identity_boundedBy layout.cache.value (by decide))).mono <;> decide
  apply ((paired.then sub_bound).castFunction _).mono <;> decide
private theorem sub_names : NamesBound sub.program.code 3 := by constructor <;> decide
private theorem div_names : NamesBound divide.program.code 3 := by constructor <;> decide
private theorem neg_names : NamesBound negate.program.code 3 := by constructor <;> decide
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

private def good := BLSFinalTarget.goodCode (base := base) (key := .nat) (val := .atom ()) layout primitives comparison comparison_correct
  sub divide sub_names.buffers reserve div_names.buffers port draw
private def bad := BLSFinalTarget.badCode (base := base) (key := .nat) (val := .atom ()) layout primitives comparison comparison_correct
  sub negate divide sub_names.buffers reserve neg_names.buffers div_names.buffers port draw
private def goodUpdate := BLSFinalTarget.goodUpdate (base := base) (key := .nat) (val := .atom ()) layout sub divide sub_names.buffers reserve
private def badUpdate := BLSFinalTarget.badUpdate (base := base) (key := .nat) (val := .atom ()) layout sub negate divide sub_names.buffers reserve neg_names.buffers
private theorem goodUpdate_buffers : goodUpdate.program.code.memBound ≤ 4 :=
  BLSFinalTarget.goodUpdate_buffers (base := base) (key := .nat) (val := .atom ()) layout sub divide sub_names.buffers reserve div_names.buffers
private theorem badUpdate_buffers : badUpdate.program.code.memBound ≤ 4 :=
  BLSFinalTarget.badUpdate_buffers (base := base) (key := .nat) (val := .atom ()) layout sub negate divide sub_names.buffers reserve neg_names.buffers div_names.buffers

private theorem good_time : Interactive.TimeBound port .unit layout.good.input.representation good
    (EncodedCacheScalarResult.timeBudget (base := base) (key := .nat) (val := .atom ()) layout.good 4
      (BLSExtractArithmetic.goodTime layout.arithmetic 6 6)) :=
  BLSFinalTarget.good_time (base := base) (key := .nat) (val := .atom ()) layout primitives comparison comparison_correct sub divide
    sub_names.buffers reserve div_names.buffers port draw_correct draw_time sub_bound div_bound
private theorem bad_time : Interactive.TimeBound port .unit layout.bad.input.representation bad
    (EncodedCacheScalarResult.timeBudget (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad
      (PairSampling.timeBudget layout.cache.value layout.cache.value 4 4) (BLSExtractArithmetic.badTime layout.arithmetic 6 118 6)) :=
  BLSFinalTarget.bad_time (base := base) (key := .nat) (val := .atom ()) layout primitives comparison comparison_correct sub negate divide
    sub_names.buffers reserve neg_names.buffers div_names.buffers port draw_correct draw_time sub_bound neg_bound div_bound
example : (good.lower port).descriptionWords ≤ EncodedCacheScalarResult.codeBudget (base := base) (key := .nat) (val := .atom ())
    layout.good 20 (BLSExtractArithmetic.goodCode layout.arithmetic 27 27) :=
  BLSFinalTarget.good_words (base := base) (key := .nat) (val := .atom ()) layout primitives comparison comparison_correct sub divide
    sub_names.buffers reserve div_names.buffers port draw_words sub_bound div_bound
example : (bad.lower port).descriptionWords ≤ EncodedCacheScalarResult.codeBudget (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ()))
    layout.bad (PairSampling.codeBudget layout.cache.value layout.cache.value 20 20) (BLSExtractArithmetic.badCode layout.arithmetic 27 631 27) :=
  BLSFinalTarget.bad_words (base := base) (key := .nat) (val := .atom ()) layout primitives comparison comparison_correct sub negate divide
    sub_names.buffers reserve neg_names.buffers div_names.buffers port draw_words sub_bound neg_bound div_bound
example : (good.lower port).DescriptionFits :=
  EncodedCacheScalarResult.descriptionFits (base := base) (key := .nat) (val := .atom ()) layout.good primitives comparison comparison_correct
    goodUpdate goodUpdate_buffers (by decide) port draw draw_fits draw_names (by decide)
example : (bad.lower port).DescriptionFits :=
  EncodedCacheScalarResult.descriptionFits (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad primitives comparison comparison_correct
    badUpdate badUpdate_buffers (by decide) port (BLSPrivateAccumulate.pairSampler (base := base) (key := .nat) (val := .atom ()) layout port draw)
    (PairSampling.descriptionFits _ _ _ _ port draw draw draw_fits draw_fits draw_names (by decide))
    (PairSampling.names _ _ _ _ port draw draw draw_names draw_names) (by decide)
example : WordIO.NamesAccounted (good.lower port) 5 :=
  EncodedCacheScalarResult.names (drawNames := 3) (updateNames := 3) (base := base) (key := .nat) (val := .atom ()) layout.good primitives comparison comparison_correct
    goodUpdate goodUpdate_buffers (by decide) port draw draw_names
    (BLSExtractArithmetic.good_names layout.arithmetic 3 sub sub_names.accounted sub_names.buffers (by decide) divide div_names.accounted)
example : WordIO.NamesAccounted (bad.lower port) 5 :=
  EncodedCacheScalarResult.names (drawNames := 4) (updateNames := 3) (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) layout.bad primitives comparison comparison_correct
    badUpdate badUpdate_buffers (by decide) port (BLSPrivateAccumulate.pairSampler (base := base) (key := .nat) (val := .atom ()) layout port draw)
    (PairSampling.names _ _ _ _ port draw draw draw_names draw_names)
    (BLSExtractArithmetic.bad_names layout.arithmetic 3 sub sub_names.accounted sub_names.buffers (by decide)
      negate neg_names.accounted neg_names.buffers divide div_names.accounted)

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

private def goodHit : layout.good.input.Value := ⟨((2, 99, [(1, 7), (2, 13)], ()), 30, 3), by rw [good_valid]; decide +kernel⟩
private def goodMiss : layout.good.input.Value := ⟨((2, 99, [(1, 7)], ()), 30, 3), by rw [good_valid]; decide +kernel⟩
private def goodEmpty : layout.good.input.Value := ⟨((2, 99, [], ()), 30, 3), by rw [good_valid]; decide +kernel⟩
private def goodDuplicate : layout.good.input.Value := ⟨((2, 99, [(2, 8), (2, 13)], ()), 30, 3), by rw [good_valid]; decide +kernel⟩
private def goodZero : layout.good.input.Value := ⟨((2, 99, [(2, 3)], ()), 30, 3), by rw [good_valid]; decide +kernel⟩
private def badHit : layout.bad.input.Value := ⟨((2, (99, 98), [(1, (7, 13)), (2, (7, 5))], ()), 77, (3, 17)), by rw [bad_valid]; decide +kernel⟩
private def badMiss : layout.bad.input.Value := ⟨((2, (99, 98), [(1, (7, 13))], ()), 77, (3, 17)), by rw [bad_valid]; decide +kernel⟩
private def badEmpty : layout.bad.input.Value := ⟨((2, (99, 98), [], ()), 0, (3, 17)), by rw [bad_valid]; decide +kernel⟩
private def badDuplicate : layout.bad.input.Value := ⟨((2, (99, 98), [(2, (7, 5)), (2, (0, 0))], ()), 0, (3, 17)), by rw [bad_valid]; decide +kernel⟩
private def badZero : layout.bad.input.Value := ⟨((2, (99, 98), [(2, (3, 5))], ()), 77, (3, 17)), by rw [bad_valid]; decide +kernel⟩
example : ¬ layout.good.input.valid ((3, 99, [(1, 7), (2, 13)], ()), 30, 3) := by rw [good_valid]; decide +kernel
example : ¬ layout.bad.input.valid ((3, (99, 98), [(1, (7, 13)), (2, (0, 0))], ()), 77, (3, 17)) := by rw [bad_valid]; decide +kernel
example : ¬ layout.good.input.valid ((256, 99, [], ()), 30, 3) := by rw [good_valid]; decide +kernel

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
      (goodHit, [88], #[3, 2, 1, 7, 2, 13], [], [88]),
      (goodHit, [], #[3, 2, 1, 7, 2, 13], [], []),
      (goodMiss, [9, 88], #[5, 2, 2, 9, 1, 7], [.invoke, .input 9], [88]),
      (goodEmpty, [3], #[0, 1, 2, 3, 0, 0], [.invoke, .input 3], []),
      (goodDuplicate, [], #[6, 2, 2, 8, 2, 13], [], []),
      (goodZero, [], #[0, 1, 2, 3, 0, 0], [], [])] do
    unless run layout.good.input good value replies == some (expected, #[77], 4, 91, 9, true, trace, remaining) do
      throwError "scalar final lookup failed for {value.val}"
  for (value, replies, expected, trace, remaining) in [
      (badHit, [88], #[3, 2, 1, 7, 13, 2, 7, 5], [], [88]),
      (badMiss, [9, 5, 88], #[2, 2, 2, 9, 5, 1, 7, 13], [.invoke, .input 9, .invoke, .input 5], [88]),
      (badEmpty, [7, 5], #[3, 1, 2, 7, 5, 0, 0, 0], [.invoke, .input 7, .invoke, .input 5], []),
      (badDuplicate, [], #[3, 2, 2, 7, 5, 2, 0, 0], [], []),
      (badZero, [], #[0, 1, 2, 3, 5, 0, 0, 0], [], [])] do
    unless run layout.bad.input bad value replies == some (expected, #[77], 4, 91, 9, true, trace, remaining) do
      throwError "pair final lookup failed for {value.val}"
  unless (run layout.good.input good goodMiss []).isNone do throwError "scalar miss accepted absent reply"
  unless (run layout.bad.input bad badMiss [9]).isNone do throwError "pair miss accepted just one reply"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``BLSExtractArithmetic.good, ``BLSExtractArithmetic.bad,
      ``BLSExtractArithmetic.good_bounded, ``BLSExtractArithmetic.bad_bounded,
      ``BLSExtractArithmetic.good_names, ``BLSExtractArithmetic.bad_names,
      ``CacheScalarResult.finish, ``CacheScalarResult.finish_bounded, ``CacheScalarResult.finish_names,
      ``EncodedCacheScalarResult.refines, ``EncodedCacheScalarResult.listCache, ``EncodedCacheScalarResult.observe_listCache,
      ``EncodedCacheScalarResult.privateOracle, ``EncodedCacheScalarResult.cache_growth,
      ``EncodedCacheScalarResult.time_bound, ``EncodedCacheScalarResult.code_bound,
      ``EncodedCacheScalarResult.names, ``EncodedCacheScalarResult.descriptionFits, ``EncodedCacheScalarResult.buffers,
      ``EncodedCacheScalarResult.staticMemory, ``EncodedCacheScalarResult.memoryBound,
      ``BLSFinalTarget.good_refines, ``BLSFinalTarget.bad_refines,
      ``BLSFinalTarget.good_time, ``BLSFinalTarget.bad_time,
      ``BLSFinalTarget.good_words, ``BLSFinalTarget.bad_words,
      ``BLSFinalTarget.good_privateOracle, ``BLSFinalTarget.bad_privateOracle,
      ``draw_correct, ``neg_bound, ``good_time, ``bad_time] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperBLSFinalTarget
