import Signatures.Runtime.Caliper.SchnorrROMTapePopLayout

/-! Executed first-match removal. After finding a cell the scan retains every
later cell, including later replies from the same family. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Pop
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : Layouts w F) (i : Fin layout.capacity)

def head : Constructed (bodyInput layout i) layout.entry Prod.fst :=
  Constructed.first layout.entry (tail layout i.castSucc) layout.wordFits (bodyInput layout i).representation.fits
def current : Constructed (bodyInput layout i) (states layout i.castSucc) (fun value => value.2.1) :=
  (Constructed.second layout.entry (tail layout i.castSucc) layout.wordFits (bodyInput layout i).representation.fits).then
    (Constructed.first (states layout i.castSucc) layout.counter layout.wordFits (tail layout i.castSucc).representation.fits)
def requested : Constructed (bodyInput layout i) layout.counter (fun value => value.2.2) :=
  (Constructed.second layout.entry (tail layout i.castSucc) layout.wordFits (bodyInput layout i).representation.fits).then
    (Constructed.second (states layout i.castSucc) layout.counter layout.wordFits (tail layout i.castSucc).representation.fits)
def tag : Constructed (bodyInput layout i) layout.counter (fun value => value.1.1) :=
  (head layout i).then (Constructed.first layout.counter layout.payload layout.wordFits layout.entry.representation.fits)
def found : Constructed (bodyInput layout i) layout.boolean (fun value => value.2.1.1) :=
  (current layout i).then (Constructed.first layout.boolean (payload layout i.val (by omega))
    layout.wordFits (states layout i.castSucc).representation.fits)
def prior : Constructed (bodyInput layout i) (payload layout i.val (by omega)) (fun value => value.2.1.2) :=
  (current layout i).then (Constructed.second layout.boolean (payload layout i.val (by omega))
    layout.wordFits (states layout i.castSucc).representation.fits)
def saved : Constructed (bodyInput layout i) layout.entry (fun value => value.2.1.2.1) :=
  (prior layout i).then (Constructed.first layout.entry (layout.list i.val (by omega))
    layout.wordFits (payload layout i.val (by omega)).representation.fits)
def rest : Constructed (bodyInput layout i) (layout.list i.val (by omega)) (fun value => value.2.1.2.2) :=
  (prior layout i).then (Constructed.second layout.entry (layout.list i.val (by omega))
    layout.wordFits (payload layout i.val (by omega)).representation.fits)

def tagEqual : Constructed (bodyInput layout i) layout.boolean (fun value => decide (value.1.1 = value.2.2)) :=
  ((tag layout i).pair (requested layout i) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 2 < _; have := layout.wordFits; omega)
    (duplicateFits layout i)
    (layout.fits_of_le (by rw [Layouts.counter_words]; have := body_le layout i; unfold Layouts.width at *; omega))
    (by change 1 + 1 < _; have := layout.wordFits; omega)).then
      (Constructed.equal (2 ^ w) (2 ^ w) layout.wordFits le_rfl le_rfl)

def retained : Constructed (bodyInput layout i) (layout.list (i.val + 1) (by omega)) (fun value => value.1 :: value.2.1.2.2) :=
  ((head layout i).pair (rest layout i) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 2 < _; have := layout.wordFits; omega)
    (duplicateFits layout i)
    (layout.fits_of_le (by have := layout.entry_le; have := body_le layout i; omega))
    (ListData.consInput layout.entry i.val layout.wordFits (by have := layout.countFits; omega)
      (layout.list (i.val + 1) (by omega)).representation.fits).representation.fits).then
      (Constructed.cons layout.entry i.val layout.wordFits (by have := layout.countFits; omega)
        (layout.list (i.val + 1) (by omega)).representation.fits)
def unchanged : Constructed (bodyInput layout i) (layout.list (i.val + 1) (by omega)) (fun value => value.2.1.2.2) :=
  (rest layout i).then (Constructed.widen layout.entry i.val (i.val + 1) (by omega) layout.wordFits
    (by have := layout.countFits; omega) (layout.list (i.val + 1) (by omega)).representation.fits)

def keptPayload : Constructed (bodyInput layout i) (payload layout (i.val + 1) (by omega))
    (fun value => (value.2.1.2.1, value.1 :: value.2.1.2.2)) :=
  (saved layout i).pair (retained layout i) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 3 < _; have := layout.wordFits; omega)
    (duplicateFits layout i)
    (layout.fits_of_le (by have := layout.entry_le; have := body_le layout i; omega))
    (payload layout (i.val + 1) (by omega)).representation.fits
def takenPayload : Constructed (bodyInput layout i) (payload layout (i.val + 1) (by omega))
    (fun value => (value.1, value.2.1.2.2)) :=
  (head layout i).pair (unchanged layout i) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 2 < _; have := layout.wordFits; omega)
    (duplicateFits layout i)
    (layout.fits_of_le (by have := layout.entry_le; have := body_le layout i; omega))
    (payload layout (i.val + 1) (by omega)).representation.fits
def kept : Constructed (bodyInput layout i) (states layout i.succ)
    (fun value => (value.2.1.1, value.2.1.2.1, value.1 :: value.2.1.2.2)) :=
  (found layout i).pair (keptPayload layout i) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 4 < _; have := layout.wordFits; omega)
    (duplicateFits layout i)
    (layout.fits_of_le (by rw [Layouts.boolean_words]; have := body_le layout i; unfold Layouts.width at *; omega))
    (states layout i.succ).representation.fits
def taken : Constructed (bodyInput layout i) (states layout i.succ)
    (fun value => (true, value.1, value.2.1.2.2)) :=
  (Constructed.constant (bodyInput layout i) layout.boolean ⟨true, trivial⟩ layout.wordFits).pair
    (takenPayload layout i) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 3 < _; have := layout.wordFits; omega)
    (duplicateFits layout i)
    (layout.fits_of_le (by rw [Layouts.boolean_words]; have := body_le layout i; unfold Layouts.width at *; omega))
    (states layout i.succ).representation.fits
def search := Constructed.branch layout.wordFits (tagEqual layout i) (taken layout i) (kept layout i)
  (by change 3 < _; have := layout.wordFits; omega) (duplicateFits layout i) (tagFits layout i)
def step (value : Schnorr.TapeCell F × ((Bool × Schnorr.TapeCell F × List (Schnorr.TapeCell F)) × Nat)) :=
  Schnorr.SeedTape.popStep value.2.2 value.2.1 value.1
def body : Constructed (bodyInput layout i) (states layout i.succ) step :=
  (Constructed.branch layout.wordFits (found layout i) (kept layout i) (search layout i)
    (by change 2 < _; have := layout.wordFits; omega) (duplicateFits layout i) (tagFits layout i)).castFunction (by
      funext value
      cases flag : value.2.1.1 <;> simp [step, Schnorr.SeedTape.popStep, flag])

theorem body_buffers : (body layout i).buffers = 5 := rfl

theorem body_budget :
    (body layout i).budget.time ≤ 3000 * layout.width + 500 ∧
      (body layout i).budget.words ≤ 12000 * layout.width + 6000 := by
  have b := body_le layout i
  have t := tail_le layout i.castSucc
  have s : (states layout i.castSucc).representation.encoding.words ≤ layout.width := state_le layout i.val (by omega)
  have p := payload_le layout i.val (by omega)
  have p' := payload_le layout (i.val + 1) (by omega)
  have l := layout.list_le i.val (by omega)
  have l' := layout.list_le (i.val + 1) (by omega)
  have encodedNext := l'
  have e := layout.entry_le
  dsimp only [body, search, tagEqual, kept, taken, keptPayload, takenPayload, retained, unchanged,
    saved, rest, prior, found, current, requested, tag, head, Constructed.castFunction, Constructed.branch,
    Constructed.then, Constructed.pair, Constructed.first, Constructed.second, Constructed.constant,
    Constructed.cons, Constructed.widen, Constructed.equal,
    Budget.branch, Budget.pair, Budget.seq, Budget.storage, Budget.cons]
  simp only [Layouts.counter_words, Layouts.boolean_words]
  change 1 + (i.val + 1) * layout.entry.representation.encoding.words ≤ layout.width at l'
  constructor <;> omega

theorem body_bounded : (body layout i).implementation.BoundedBy
    (3000 * layout.width + 500) (12000 * layout.width + 6000) :=
  (body layout i).bounded.mono (body_budget layout i).1 (body_budget layout i).2

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Pop
