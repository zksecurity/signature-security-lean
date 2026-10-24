import Proofs.Runtime.Caliper.BLSFinalTargetOracle
import Proofs.Runtime.Caliper.BLSFinalFrameNames
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource

namespace SignaturesTest.CaliperBLSFinalFrame

-- Word arithmetic tests the actual wiring. The field-source theorems remain
-- general; this finite executable fixture is not presented as a field model.
private def base (_ : Unit) : Type := Word 8
private instance : Add (Ty.Value base (.atom ())) := inferInstanceAs (Add (Word 8))
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
private def add : Implementation .unit layout.arithmetic.pair layout.cache.value (fun value => value.1 + value.2) := binary .add
private theorem add_bound : add.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem add_names : NamesBound add.program.code 3 := by constructor <;> decide
private def goodFrame := BLSFinalFrame.good layout add add_names.buffers reserve (by trivial)
private def badFrame := BLSFinalFrame.bad layout (by trivial)
private def good : Interactive.Code 8 := .seq (.compute goodFrame.program.code)
  (BLSFinalTarget.goodCode (base := base) (key := .nat) (val := .atom ()) layout primitives comparison comparison_correct
    sub divide sub_names.buffers reserve div_names.buffers port draw)
private def bad : Interactive.Code 8 := .seq (.compute badFrame.program.code)
  (BLSFinalTarget.badCode (base := base) (key := .nat) (val := .atom ()) layout primitives comparison comparison_correct
    sub negate divide sub_names.buffers reserve neg_names.buffers div_names.buffers port draw)

example : goodFrame.BoundedBy (BLSFinalFrame.goodTime layout 6) (BLSFinalFrame.goodWords layout 27) :=
  BLSFinalFrame.good_bounded layout add add_names.buffers reserve add_bound (by trivial)
example : badFrame.BoundedBy (CacheTargetFrame.timeBudget layout.bad) (CacheTargetFrame.codeBudget layout.bad) :=
  BLSFinalFrame.bad_bounded layout (by trivial)
example : NamesAccounted goodFrame.program.code 3 := BLSFinalFrame.good_names layout 3 add add_names.accounted add_names.buffers reserve (by trivial)
example : NamesAccounted badFrame.program.code 3 := BLSFinalFrame.bad_names layout 3 (by trivial)
example : goodFrame.program.code.memBound ≤ 6 := BLSFinalFrame.good_buffers layout add add_names.buffers reserve (by trivial)
example : badFrame.program.code.memBound ≤ 6 := BLSFinalFrame.bad_buffers layout (by trivial)
example : DescriptionFits goodFrame.program.code := goodFrame.program.description_fits
example : DescriptionFits badFrame.program.code := badFrame.program.description_fits

private theorem good_valid (key : Nat) (entries : List (Nat × Word 8)) (signatures beta hashes : Word 8) :
    (BLSFinalFrame.goodInput layout).valid ((signatures, entries), key, beta, hashes) ↔
      ((entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256) ∧ key < 256) ∧
      ((lookupValue key (0 : Word 8) entries).1 = false → entries.length ≤ 1) := by
  change (((True ∧ (entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256 ∧ True)) ∧ key < 256 ∧ True ∧ True) ∧
    ((lookupValue key (0 : Word 8) entries).1 = false → entries.length ≤ 1)) ↔ _
  simp only [and_true, true_and]
private theorem bad_valid (key : Nat) (entries : List (Nat × (Word 8 × Word 8))) (signatures : Word 8 × Word 8) (beta : Word 8) :
    (BLSFinalFrame.badInput layout (by trivial)).valid ((signatures, entries), key, beta) ↔
      ((entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256) ∧ key < 256) ∧
      ((lookupValue key (0, 0) entries).1 = false → entries.length ≤ 1) := by
  change ((((True ∧ True) ∧ (entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256 ∧ True ∧ True)) ∧ key < 256 ∧ True) ∧
    ((lookupValue key (0, 0) entries).1 = false → entries.length ≤ 1)) ↔ _
  simp only [and_true, true_and]

private def goodHit : (BLSFinalFrame.goodInput layout).Value := ⟨((3, [(1, 7), (2, 13)]), 2, 17, 13), by rw [good_valid]; decide +kernel⟩
private def goodMiss : (BLSFinalFrame.goodInput layout).Value := ⟨((3, [(1, 7)]), 2, 17, 13), by rw [good_valid]; decide +kernel⟩
private def goodEmpty : (BLSFinalFrame.goodInput layout).Value := ⟨((3, []), 2, 17, 13), by rw [good_valid]; decide +kernel⟩
private def goodDuplicate : (BLSFinalFrame.goodInput layout).Value := ⟨((3, [(2, 8), (2, 13)]), 2, 17, 13), by rw [good_valid]; decide +kernel⟩
private def goodOverflow : (BLSFinalFrame.goodInput layout).Value := ⟨((3, [(2, 9)]), 2, 250, 12), by rw [good_valid]; decide +kernel⟩
private def badHit : (BLSFinalFrame.badInput layout (by trivial)).Value := ⟨(((3, 17), [(1, (7, 13)), (2, (7, 5))]), 2, 77), by rw [bad_valid]; decide +kernel⟩
private def badMiss : (BLSFinalFrame.badInput layout (by trivial)).Value := ⟨(((3, 17), [(1, (7, 13))]), 2, 77), by rw [bad_valid]; decide +kernel⟩
private def badEmpty : (BLSFinalFrame.badInput layout (by trivial)).Value := ⟨(((3, 17), []), 2, 0), by rw [bad_valid]; decide +kernel⟩
private def badDuplicate : (BLSFinalFrame.badInput layout (by trivial)).Value := ⟨(((3, 17), [(2, (7, 5)), (2, (0, 0))]), 2, 0), by rw [bad_valid]; decide +kernel⟩
private def badZero : (BLSFinalFrame.badInput layout (by trivial)).Value := ⟨(((3, 17), [(2, (3, 5))]), 2, 77), by rw [bad_valid]; decide +kernel⟩
example : ¬ (BLSFinalFrame.goodInput layout).valid ((3, [(1, 7), (2, 13)]), 3, 17, 13) := by rw [good_valid]; decide +kernel
example : ¬ (BLSFinalFrame.badInput layout (by trivial)).valid (((3, 17), [(1, (7, 13)), (2, (0, 0))]), 3, 77) := by rw [bad_valid]; decide +kernel
example : ¬ (BLSFinalFrame.goodInput layout).valid ((3, []), 256, 17, 13) := by rw [good_valid]; decide +kernel

-- Execute both new frames together with the existing final lookup/arithmetic.
-- Preserved caller storage and released scratch are checked on that same run.
private def run {A : Type} (input : Layout 8 A) (code : Interactive.Code 8) (value : input.Value) (replies : List (Word 8)) := do
  let initial := input.representation.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 50000 (code.lower port) before replies
  pure (result.state.bufs 0, result.state.bufs 200, result.state.caps 200, result.state.regs 99, result.state.tapePos,
    (List.range 24).all (fun i => result.state.caps (i + 1) == 0), result.trace, result.remaining)

open Lean in
run_cmd do
  for (value, replies, expected, trace, remaining) in [
      (goodHit, [88], #[3, 2, 1, 7, 2, 13], [], [88]),
      (goodMiss, [9, 88], #[5, 2, 2, 9, 1, 7], [.invoke, .input 9], [88]),
      (goodEmpty, [3], #[0, 1, 2, 3, 0, 0], [.invoke, .input 3], []),
      (goodDuplicate, [], #[6, 2, 2, 8, 2, 13], [], []),
      (goodOverflow, [], #[1, 1, 2, 9, 0, 0], [], [])] do
    unless run (BLSFinalFrame.goodInput layout) good value replies == some (expected, #[77], 4, 91, 9, true, trace, remaining) do
      throwError "scalar final frame failed for {value.val}"
  for (value, replies, expected, trace, remaining) in [
      (badHit, [88], #[3, 2, 1, 7, 13, 2, 7, 5], [], [88]),
      (badMiss, [9, 5, 88], #[2, 2, 2, 9, 5, 1, 7, 13], [.invoke, .input 9, .invoke, .input 5], [88]),
      (badEmpty, [7, 5], #[3, 1, 2, 7, 5, 0, 0, 0], [.invoke, .input 7, .invoke, .input 5], []),
      (badDuplicate, [], #[3, 2, 2, 7, 5, 2, 0, 0], [], []),
      (badZero, [], #[0, 1, 2, 3, 5, 0, 0, 0], [], [])] do
    unless run (BLSFinalFrame.badInput layout (by trivial)) bad value replies == some (expected, #[77], 4, 91, 9, true, trace, remaining) do
      throwError "pair final frame failed for {value.val}"
  unless (run (BLSFinalFrame.goodInput layout) good goodMiss []).isNone do throwError "scalar miss accepted absent reply"
  unless (run (BLSFinalFrame.badInput layout (by trivial)) bad badMiss [9]).isNone do throwError "pair miss accepted just one reply"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``CacheTargetFrame.implementation, ``CacheTargetFrame.implementation_bounded,
      ``CacheTargetFrame.implementation_names, ``CacheTargetFrame.admissible_of_room,
      ``BLSFinalFrame.good, ``BLSFinalFrame.bad, ``BLSFinalFrame.good_bounded, ``BLSFinalFrame.bad_bounded,
      ``BLSFinalFrame.good_buffers, ``BLSFinalFrame.bad_buffers, ``BLSFinalFrame.good_names, ``BLSFinalFrame.bad_names,
      ``BLSFinalFrame.admissible_of_room] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperBLSFinalFrame
