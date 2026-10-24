import Proofs.Runtime.Caliper.SchnorrROMTapeLayout
import Proofs.Runtime.Caliper.EncodedConstant

/-! Executed trim step for Schnorr replay. Only challenge-family cells consume
the prefix counter. Private-family cells are retained even after it reaches
zero. Each retained cell is copied into a growing, bounded accumulator. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape
open Caliper BoundedSource

variable {w : Nat} {F : Type} (layout : Layouts w F) (i : Fin layout.capacity)

def current : Implementation .unit (layout.body i) (layout.states i.castSucc) (fun value => value.2.1) :=
  (Implementation.second (by decide) layout.entry (layout.stateTail i.castSucc) layout.wordFits
    (layout.body i).representation.fits).then
    (Implementation.first (by decide) (layout.states i.castSucc) layout.unit layout.wordFits
      (layout.stateTail i.castSucc).representation.fits)
def entry : Implementation .unit (layout.body i) layout.entry Prod.fst :=
  Implementation.first (by decide) layout.entry (layout.stateTail i.castSucc) layout.wordFits
    (layout.body i).representation.fits
def tag : Implementation .unit (layout.body i) layout.counter (fun value => value.1.1) :=
  (entry layout i).then (Implementation.first (by decide) layout.counter layout.payload layout.wordFits layout.entry.representation.fits)
def remaining : Implementation .unit (layout.body i) layout.counter (fun value => value.2.1.1) :=
  (current layout i).then (Implementation.first (by decide) layout.counter (layout.list i.val (by omega)) layout.wordFits
    (layout.states i.castSucc).representation.fits)
def accumulated : Implementation .unit (layout.body i) (layout.list i.val (by omega)) (fun value => value.2.1.2) :=
  (current layout i).then (Implementation.second (by decide) layout.counter (layout.list i.val (by omega)) layout.wordFits
    (layout.states i.castSucc).representation.fits)

theorem current_buffers : (current layout i).program.code.memBound ≤ 2 :=
  max_le (Implementation.second_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _)
theorem entry_buffers : (entry layout i).program.code.memBound ≤ 2 := Implementation.first_buffers _ _ _ _ _
theorem tag_buffers : (tag layout i).program.code.memBound ≤ 2 :=
  max_le (entry_buffers layout i) (Implementation.first_buffers _ _ _ _ _)
theorem remaining_buffers : (remaining layout i).program.code.memBound ≤ 2 :=
  max_le (current_buffers layout i) (Implementation.first_buffers _ _ _ _ _)
theorem accumulated_buffers : (accumulated layout i).program.code.memBound ≤ 2 :=
  max_le (current_buffers layout i) (Implementation.second_buffers _ _ _ _ _)

def constant (n : Nat) (valid : n < 2 ^ w) : Implementation .unit (layout.body i) layout.counter (fun _ => n) :=
  Implementation.constant (layout.body i) layout.counter ⟨n, valid⟩ layout.wordFits
theorem constant_buffers (n : Nat) (valid : n < 2 ^ w) : (constant layout i n valid).program.code.memBound ≤ 2 :=
  Implementation.constant_buffers _ _ _ _

def arguments {f : Schnorr.TapeCell F × ((Nat × List (Schnorr.TapeCell F)) × Unit) → Nat}
    (get : Implementation .unit (layout.body i) layout.counter f)
    (getBuffers : get.program.code.memBound ≤ 2) (n : Nat) (valid : n < 2 ^ w) :
    Implementation .unit (layout.body i) (Natural.pair (2 ^ w) (2 ^ w) layout.wordFits le_rfl le_rfl)
      (fun value => (f value, n)) :=
  get.pair (constant layout i n valid) (by decide) layout.wordFits
    (layout.nameFits _ getBuffers (by decide))
    (layout.nameFits _ (constant_buffers layout i n valid) (by decide))
    (layout.bodyDuplicate i)
    (layout.fits_of_le (by rw [Layouts.counter_words]; have := layout.body_le i; unfold Layouts.width at *; omega))
    (by have := layout.wordFits; change 1 + 1 < _; omega)
theorem arguments_buffers {f : Schnorr.TapeCell F × ((Nat × List (Schnorr.TapeCell F)) × Unit) → Nat}
    (get : Implementation .unit (layout.body i) layout.counter f)
    (getBuffers : get.program.code.memBound ≤ 2) (n : Nat) (valid : n < 2 ^ w) :
    (arguments layout i get getBuffers n valid).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 2) _ _ _ _ _ _ _ _
    getBuffers (constant_buffers layout i n valid)

def isChallenge : Implementation .unit (layout.body i) layout.boolean (fun value => decide (value.1.1 = 1)) :=
  (arguments layout i (tag layout i) (tag_buffers layout i) 1 (by have := layout.wordFits; omega)).then
    (Natural.equal .unit (2 ^ w) (2 ^ w) layout.wordFits le_rfl le_rfl)
def isZero : Implementation .unit (layout.body i) layout.boolean (fun value => decide (value.2.1.1 = 0)) :=
  (arguments layout i (remaining layout i) (remaining_buffers layout i) 0 (by positivity)).then
    (Natural.equal .unit (2 ^ w) (2 ^ w) layout.wordFits le_rfl le_rfl)
def decrement : Implementation .unit (layout.body i) layout.counter (fun value => value.2.1.1 - 1) :=
  (arguments layout i (remaining layout i) (remaining_buffers layout i) 1 (by have := layout.wordFits; omega)).then
    (Natural.subtract .unit (2 ^ w) (2 ^ w) layout.wordFits le_rfl le_rfl)
theorem isChallenge_buffers : (isChallenge layout i).program.code.memBound ≤ 3 :=
  max_le (arguments_buffers layout i _ (tag_buffers layout i) _ _) (by change 1 ≤ 3; decide)
theorem isZero_buffers : (isZero layout i).program.code.memBound ≤ 3 :=
  max_le (arguments_buffers layout i _ (remaining_buffers layout i) _ _) (by change 1 ≤ 3; decide)
theorem decrement_buffers : (decrement layout i).program.code.memBound ≤ 3 :=
  max_le (arguments_buffers layout i _ (remaining_buffers layout i) _ _) (by change 1 ≤ 3; decide)

def consArgs : Implementation .unit (layout.body i)
    (ListData.consInput layout.entry i.val layout.wordFits (by have := layout.countFits; omega)
      (layout.list (i.val + 1) (by omega)).representation.fits)
    (fun value => (value.1, value.2.1.2)) :=
  (entry layout i).pair (accumulated layout i) (by decide) layout.wordFits
    (layout.nameFits _ (entry_buffers layout i) (by decide))
    (layout.nameFits _ (accumulated_buffers layout i) (by decide))
    (layout.bodyDuplicate i)
    (layout.fits_of_le (by have := layout.entry_le; have := layout.body_le i; omega)) _
def cons : Implementation .unit (layout.body i) (layout.list (i.val + 1) (by omega))
    (fun value => value.1 :: value.2.1.2) :=
  (consArgs layout i).then (ListData.cons .unit (by decide) layout.entry i.val layout.wordFits
    (by have := layout.countFits; omega) (layout.list (i.val + 1) (by omega)).representation.fits)
def widen : Implementation .unit (layout.body i) (layout.list (i.val + 1) (by omega))
    (fun value => value.2.1.2) :=
  (accumulated layout i).then (ListData.widen .unit (by decide) layout.entry i.val (i.val + 1) (by omega)
    layout.wordFits (by have := layout.countFits; omega) (layout.list (i.val + 1) (by omega)).representation.fits)
theorem consArgs_buffers : (consArgs layout i).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 2) _ _ _ _ _ _ _ _
    (entry_buffers layout i) (accumulated_buffers layout i)
theorem cons_buffers : (cons layout i).program.code.memBound ≤ 3 :=
  max_le (consArgs_buffers layout i) ((ListReverse.body_buffers layout.reverse
    ⟨i.val, by change i.val < layout.capacity + 1; omega⟩).trans (by decide))
theorem widen_buffers : (widen layout i).program.code.memBound ≤ 2 :=
  max_le (accumulated_buffers layout i)
    ((Assembly.code_names _ 1 ((Assembly.sourcesBound_append _ _ _).mpr
      ⟨Assembly.sourcesBound_reads _ _ _ _ (by decide), Assembly.sourcesBound_replicate _ _ _⟩)).2)

def assemble {f : Schnorr.TapeCell F × ((Nat × List (Schnorr.TapeCell F)) × Unit) → Nat}
    {g : Schnorr.TapeCell F × ((Nat × List (Schnorr.TapeCell F)) × Unit) → List (Schnorr.TapeCell F)}
    (count : Implementation .unit (layout.body i) layout.counter f)
    (values : Implementation .unit (layout.body i) (layout.list (i.val + 1) (by omega)) g)
    (countBuffers : count.program.code.memBound ≤ 3) (valuesBuffers : values.program.code.memBound ≤ 3) :
    Implementation .unit (layout.body i) (layout.states i.succ) (fun value => (f value, g value)) :=
  count.pair values (by decide) layout.wordFits
    (layout.nameFits _ countBuffers (by decide)) (layout.nameFits _ valuesBuffers (by decide))
    (layout.bodyDuplicate i)
    (layout.fits_of_le (by rw [Layouts.counter_words]; have := layout.body_le i; unfold Layouts.width at *; omega))
    (layout.states i.succ).representation.fits
theorem assemble_buffers {f : Schnorr.TapeCell F × ((Nat × List (Schnorr.TapeCell F)) × Unit) → Nat}
    {g : Schnorr.TapeCell F × ((Nat × List (Schnorr.TapeCell F)) × Unit) → List (Schnorr.TapeCell F)}
    (count : Implementation .unit (layout.body i) layout.counter f)
    (values : Implementation .unit (layout.body i) (layout.list (i.val + 1) (by omega)) g)
    (countBuffers : count.program.code.memBound ≤ 3) (valuesBuffers : values.program.code.memBound ≤ 3) :
    (assemble layout i count values countBuffers valuesBuffers).program.code.memBound ≤ 4 :=
  Implementation.pair_buffers (firstBuffers := 3) (secondBuffers := 3) _ _ _ _ _ _ _ _ countBuffers valuesBuffers

def skip := assemble layout i (remaining layout i) (widen layout i)
  ((remaining_buffers layout i).trans (by decide)) ((widen_buffers layout i).trans (by decide))
def keep := assemble layout i (remaining layout i) (cons layout i)
  ((remaining_buffers layout i).trans (by decide)) (cons_buffers layout i)
def consume := assemble layout i (decrement layout i) (cons layout i)
  (decrement_buffers layout i) (cons_buffers layout i)
theorem skip_buffers : (skip layout i).program.code.memBound ≤ 4 := assemble_buffers layout i _ _ _ _
theorem keep_buffers : (keep layout i).program.code.memBound ≤ 4 := assemble_buffers layout i _ _ _ _
theorem consume_buffers : (consume layout i).program.code.memBound ≤ 4 := assemble_buffers layout i _ _ _ _

def challengeCompiled := (isZero layout i).checkedBranch (hw := layout.wordFits)
  (skip layout i) (consume layout i) (by decide) (layout.bodyDuplicate i) (layout.bodyTag i)
theorem challenge_accepted : (challengeCompiled layout i).isSome := by
  obtain ⟨implementation, equal, _⟩ := Implementation.checkedBranch_accept (isZero layout i) (skip layout i) (consume layout i)
    (by decide) (isZero_buffers layout i) (skip_buffers layout i) (consume_buffers layout i)
    (by have := layout.wordFits; omega) (layout.bodyDuplicate i) (layout.bodyTag i)
  rw [challengeCompiled, equal]; rfl
def challenge := (challengeCompiled layout i).get (challenge_accepted layout i)
theorem challenge_buffers : (challenge layout i).program.code.memBound ≤ 4 := by
  obtain ⟨implementation, equal, bound⟩ := Implementation.checkedBranch_accept (isZero layout i) (skip layout i) (consume layout i)
    (by decide) (isZero_buffers layout i) (skip_buffers layout i) (consume_buffers layout i)
    (by have := layout.wordFits; omega) (layout.bodyDuplicate i) (layout.bodyTag i)
  rw [show challenge layout i = implementation from Option.get_of_eq_some (challenge_accepted layout i) equal]
  exact bound

def bodyCompiled := (isChallenge layout i).checkedBranch (hw := layout.wordFits)
  (challenge layout i) (keep layout i) (by decide) (layout.bodyDuplicate i) (layout.bodyTag i)
theorem body_accepted : (bodyCompiled layout i).isSome := by
  obtain ⟨implementation, equal, _⟩ := Implementation.checkedBranch_accept (isChallenge layout i) (challenge layout i) (keep layout i)
    (by decide) (isChallenge_buffers layout i) (challenge_buffers layout i) (keep_buffers layout i)
    (by have := layout.wordFits; omega) (layout.bodyDuplicate i) (layout.bodyTag i)
  rw [bodyCompiled, equal]; rfl
def step (value : Schnorr.TapeCell F × ((Nat × List (Schnorr.TapeCell F)) × Unit)) :=
  Schnorr.SeedTape.trimStep 1 value.2.1 value.1
def body : Implementation .unit (layout.body i) (layout.states i.succ) step :=
  ((bodyCompiled layout i).get (body_accepted layout i)).castFunction (by
    funext value
    simp only [step, Schnorr.SeedTape.trimStep, decide_eq_true_eq])
theorem body_buffers : (body layout i).program.code.memBound ≤ 4 := by
  obtain ⟨implementation, equal, bound⟩ := Implementation.checkedBranch_accept (isChallenge layout i) (challenge layout i) (keep layout i)
    (by decide) (isChallenge_buffers layout i) (challenge_buffers layout i) (keep_buffers layout i)
    (by have := layout.wordFits; omega) (layout.bodyDuplicate i) (layout.bodyTag i)
  change ((bodyCompiled layout i).get (body_accepted layout i)).program.code.memBound ≤ 4
  rw [Option.get_of_eq_some (body_accepted layout i) equal]
  exact bound

end Signatures.Runtime.CaliperBackend.SchnorrROMTape
