import Proofs.Runtime.Caliper.ChronologicalIndexLayout

/-! The scan body compares encoded keys, sets a hit's counter to zero, and
otherwise increments the counter. Both branches and all retained copies are
constructed code with derived time, description and scratch bounds. -/
namespace Signatures.Runtime.CaliperBackend.ChronologicalIndex
open Caliper BoundedSource
variable {w : Nat} {K V : Type} [DecidableEq K] (layout : Layouts w K V) (i : Fin layout.capacity)

def tail : Constructed (layout.body i) (layout.stateTail i.castSucc) Prod.snd :=
  Constructed.second layout.entry (layout.stateTail i.castSucc) layout.wordFits (layout.body i).representation.fits
def current : Constructed (layout.body i) (layout.state i.castSucc) (fun value => value.2.1) :=
  (tail layout i).then (Constructed.first (layout.state i.castSucc) layout.key layout.wordFits (layout.stateTail i.castSucc).representation.fits)
def requested : Constructed (layout.body i) layout.key (fun value => value.2.2) :=
  (tail layout i).then (Constructed.second (layout.state i.castSucc) layout.key layout.wordFits (layout.stateTail i.castSucc).representation.fits)
def key : Constructed (layout.body i) layout.key (fun value => value.1.1) :=
  (Constructed.first layout.entry (layout.stateTail i.castSucc) layout.wordFits (layout.body i).representation.fits).then
    (Constructed.first layout.key layout.value layout.wordFits layout.entry.representation.fits)
def keyPair := layout.key.prod layout.key (layout.fits (by have := layout.sizes 0; omega))
def arguments : Constructed (layout.body i) (keyPair layout) (fun value => (value.1.1, value.2.2)) :=
  (key layout i).pair (requested layout i) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 2 < _; have := layout.wordFits; omega)
    (layout.duplicate i) (layout.fits (by have := layout.sizes 0; have := layout.body_size i; omega)) (keyPair layout).representation.fits
def equal : Constructed (keyPair layout) layout.boolean (fun value => decide (value.1 = value.2)) where
  implementation := EncodedEquality.implementation .unit layout.key layout.wordFits (keyPair layout).representation.fits
  budget := ⟨6 * layout.key.representation.encoding.words + 3, 30 * layout.key.representation.encoding.words + 13⟩
  bounded := EncodedEquality.implementation_boundedBy _ _ _
  buffers := 5
  buffers_le := (EncodedEquality.implementation_names .unit _ _ _).buffers
  names slots := (EncodedEquality.implementation_names .unit _ _ _).mono (by
    change 5 ≤ slots + descriptionWords (EncodedEquality.code (w := w) layout.key.representation.encoding.words)
    rw [EncodedEquality.code_descriptionWords]
    omega)
def test := (arguments layout i).then (equal layout)
def flag := (current layout i).then
  (Constructed.first layout.boolean (layout.counter i.castSucc) layout.wordFits (layout.state i.castSucc).representation.fits)
def count := (current layout i).then
  (Constructed.second layout.boolean (layout.counter i.castSucc) layout.wordFits (layout.state i.castSucc).representation.fits)
def increment : Constructed (layout.body i) (layout.counter i.succ) (fun value => value.2.1.2 + 1) :=
  (count layout i).then (Constructed.addLiteral (i.val + 1) 1 layout.wordFits (by have := layout.countFits; omega))
def hit : Constructed (layout.body i) (layout.state i.succ) (fun _ => (true, 0)) :=
  Constructed.constant (layout.body i) (layout.state i.succ)
    ⟨(true, 0), trivial, by change 0 < i.val + 1 + 1; omega⟩ layout.wordFits
def miss : Constructed (layout.body i) (layout.state i.succ) (fun value => (value.2.1.1, value.2.1.2 + 1)) :=
  (flag layout i).pair (increment layout i) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change max 2 1 < _; have := layout.wordFits; omega)
    (layout.duplicate i) (layout.fits (by have := layout.body_size i; change 1 + _ ≤ _; unfold Layouts.width at *; omega))
    (layout.state i.succ).representation.fits
def body : Constructed (layout.body i) (layout.state i.succ) step :=
  (Constructed.branch layout.wordFits (test layout i) (hit layout i) (miss layout i)
    (by change max 3 5 < _; have := layout.wordFits; omega) (layout.duplicate i) (layout.tagged i)).castFunction (by
      funext value
      simp only [Function.comp_apply, step, decide_eq_true_eq])
theorem body_buffers : (body layout i).buffers = 6 := rfl

theorem body_budget : (body layout i).budget.time ≤ 600 * layout.width + 100 ∧
    (body layout i).budget.words ≤ 2000 * layout.width + 1000 := by
  have sizes := layout.sizes i.castSucc
  have bodySize := layout.body_size i
  have positive : 4 ≤ layout.width := by unfold Layouts.width; omega
  dsimp only [body, test, arguments, key, requested, tail, equal, hit, miss, flag, increment, count, current,
    Constructed.then, Constructed.first, Constructed.second, Constructed.pair, Constructed.constant,
    Constructed.addLiteral, Constructed.branch, Constructed.castFunction, Budget.seq, Budget.pair, Budget.storage, Budget.branch]
  have stateSize : (layout.state i.succ).representation.encoding.words = 2 := rfl
  have booleanSize : layout.boolean.representation.encoding.words = 1 := rfl
  have countSize : (layout.counter i.castSucc).representation.encoding.words = 1 := rfl
  have nextSize : (layout.counter i.succ).representation.encoding.words = 1 := rfl
  simp only [stateSize, booleanSize, countSize, nextSize, sizes.2.2.2.2.1]
  exact ⟨by omega, by omega⟩

end Signatures.Runtime.CaliperBackend.ChronologicalIndex
