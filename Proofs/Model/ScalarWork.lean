import Signatures.Model.LazyAGM

/-!
# Scalar extraction in an explicit unit-operation model

One field operation, indexed table read, equality/branch, or list-cell visit costs one unit.
A fold charges one addition and one iteration per entry. Field operations are atomic here;
these are not bit-complexity or Lean evaluator bounds. Table reads require a random-access
representation. The concrete extraction routines below, rather than arbitrary user programs,
are the subjects of the bounds.
-/

open scoped BigOperators

namespace Model.ScalarWork

structure Result (α : Type) where
  value : α
  work : Nat

variable {F I M G : Type} [Field F]

def input (x : F) : Result F := ⟨x, 0⟩
def add (x y : Result F) : Result F := ⟨x.value + y.value, x.work + y.work + 1⟩
def sub (x y : Result F) : Result F := ⟨x.value - y.value, x.work + y.work + 1⟩
def mul (x y : Result F) : Result F := ⟨x.value * y.value, x.work + y.work + 1⟩
def div (x y : Result F) : Result F := ⟨x.value / y.value, x.work + y.work + 1⟩
def neg (x : Result F) : Result F := ⟨-x.value, x.work + 1⟩
def table (rho : I → F) (i : I) : Result F := ⟨rho i, 1⟩

def coefficient : List F → Nat → Result F
  | [], _ => ⟨0, 1⟩
  | x :: _, 0 => ⟨x, 1⟩
  | _ :: xs, n + 1 =>
      let r := coefficient xs n
      ⟨r.value, r.work + 1⟩

@[simp] theorem coefficient_value (xs : List F) (n : Nat) :
    (coefficient xs n).value = LazyAGM.tokenCoeff xs n := by
  induction xs generalizing n with
  | nil => simp [coefficient, LazyAGM.tokenCoeff]
  | cons x xs ih =>
      cases n <;> simp [coefficient, LazyAGM.tokenCoeff, ih, LazyAGM.tokenCoeff] at *

theorem coefficient_work (xs : List F) (n : Nat) :
    (coefficient xs n).work ≤ xs.length + 1 := by
  induction xs generalizing n with
  | nil => simp [coefficient]
  | cons x xs ih =>
      cases n with
      | zero => simp [coefficient]
      | succ n => simpa [coefficient] using Nat.add_le_add_right (ih n) 1

def sumTable {α : Type} [AddCommMonoid α] [Fintype I] (f : I → Result α) : Result α :=
  ⟨∑ i, (f i).value, (∑ i, (f i).work) + 2 * Fintype.card I⟩

theorem sumTable_work {α : Type} [AddCommMonoid α] [Fintype I] (f : I → Result α) (c : Nat)
    (h : ∀ i, (f i).work ≤ c) :
    (sumTable f).work ≤ Fintype.card I * (c + 2) := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun i _ => h i)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  dsimp [sumTable]
  nlinarith

def sumList {α : Type} (f : Nat → α → Result F) (xs : List α) : Result F :=
  ⟨(xs.mapIdx fun i x => (f i x).value).sum,
    (xs.mapIdx fun i x => (f i x).work).sum + 2 * xs.length⟩

theorem sumList_work {α : Type} (f : Nat → α → Result F) (xs : List α) (c : Nat)
    (h : ∀ i x, (f i x).work ≤ c) :
    (sumList f xs).work ≤ xs.length * (c + 2) := by
  have hsum : (xs.mapIdx fun i x => (f i x).work).sum ≤ xs.length * c := by
    induction xs generalizing f with
    | nil => simp
    | cons x xs ih =>
        have hi := ih (fun i x => f (i + 1) x) (fun i x => h (i + 1) x)
        simp only [List.mapIdx_cons, List.sum_cons, List.length_cons]
        have hx := h 0 x
        nlinarith
  dsimp [sumList]
  nlinarith

def baseCoeff [DecidableEq I] (gamma : List F) (tr : List (I × G)) (i : I) : Result F :=
  sumList (fun n p =>
    let r := if p.1 = i then coefficient gamma n else input 0
    ⟨r.value, r.work + 1⟩) tr

@[simp] theorem baseCoeff_value [DecidableEq I] (gamma : List F) (tr : List (I × G)) (i : I) :
    (baseCoeff gamma tr i).value = LazyAGM.baseCoeff gamma tr i := by
  simp [baseCoeff, sumList, LazyAGM.baseCoeff, input, apply_ite]

theorem baseCoeff_work [DecidableEq I] (gamma : List F) (tr : List (I × G)) (i : I) :
    (baseCoeff gamma tr i).work ≤ tr.length * (gamma.length + 4) := by
  have h := sumList_work (fun n (p : I × G) =>
      let r := if p.1 = i then coefficient gamma n else input 0
      ⟨r.value, r.work + 1⟩) tr (gamma.length + 2) (by
    intro n p
    dsimp
    split
    · have h := coefficient_work gamma n
      omega
    · simp [input])
  simpa [baseCoeff, Nat.add_assoc] using h

def weighted [Fintype I] (w : I → M → Result F) (rho : I → F) (m : M) : Result F :=
  sumTable fun i => mul (table rho i) (w i m)

theorem weighted_work [Fintype I] (w : I → M → Result F) (rho : I → F)
    (m : M) (c : Nat) (hw : ∀ i m, (w i m).work ≤ c) :
    (weighted w rho m).work ≤ Fintype.card I * (c + 4) := by
  have h := sumTable_work (fun i => mul (table rho i) (w i m)) (c + 2) (by
    intro i
    dsimp [mul, table]
    have := hw i m
    omega)
  simpa [weighted, Nat.add_assoc] using h

def good [Fintype I] [DecidableEq I] (w : I → M → Result F) (rho : I → F)
    (out : LazyAGM.Output F M) (tr : LazyAGM.Transcript I M G) : Result F :=
  let constant := add (input out.β) (sumTable fun i => mul (baseCoeff out.γ tr.1 i) (table rho i))
  let linear := sumList (fun n q => mul (coefficient out.ξ n) (weighted w rho q.1)) tr.2
  div constant (sub (weighted w rho out.mstar) linear)

def goodBound (n qH qS lenGamma lenXi weightCost : Nat) : Nat :=
  n * (qH * (lenGamma + 4) + 4) +
    qS * (lenXi + n * (weightCost + 4) + 4) + n * (weightCost + 4) + 3

theorem good_value [Fintype I] [DecidableEq I] (w : I → M → Result F) (rho : I → F)
    (out : LazyAGM.Output F M) (tr : LazyAGM.Transcript I M G) :
    (good w rho out tr).value =
      (out.β + ∑ i, LazyAGM.baseCoeff out.γ tr.1 i * rho i) /
        ((∑ i, rho i * (w i out.mstar).value) -
          (tr.2.mapIdx fun n q => LazyAGM.tokenCoeff out.ξ n *
            (∑ i, rho i * (w i q.1).value)).sum) := by
  simp [good, weighted, add, sub, mul, div, input, table, sumTable, sumList]

theorem good_work [Fintype I] [DecidableEq I] (w : I → M → Result F) (rho : I → F)
    (out : LazyAGM.Output F M) (tr : LazyAGM.Transcript I M G)
    (c : Nat) (hw : ∀ i m, (w i m).work ≤ c) :
    (good w rho out tr).work ≤
      goodBound (Fintype.card I) tr.1.length tr.2.length out.γ.length out.ξ.length c := by
  have hc := sumTable_work (fun i => mul (baseCoeff out.γ tr.1 i) (table rho i))
    (tr.1.length * (out.γ.length + 4) + 2) (by
      intro i
      dsimp [mul, table]
      have := baseCoeff_work out.γ tr.1 i
      omega)
  have hl := sumList_work (fun n q => mul (coefficient out.ξ n) (weighted w rho q.1)) tr.2
    (out.ξ.length + Fintype.card I * (c + 4) + 2) (by
      intro n q
      dsimp [mul]
      have := coefficient_work out.ξ n
      have := weighted_work w rho q.1 c hw
      omega)
  have ht := weighted_work w rho out.mstar c hw
  dsimp [good, add, sub, div, input, goodBound]
  nlinarith

def denominator [Fintype I] (w : I → M → Result F) (out : LazyAGM.Output F M)
    (tr : LazyAGM.Transcript I M G) (i : I) : Result F :=
  sub (w i out.mstar) (sumList (fun n q => mul (coefficient out.ξ n) (w i q.1)) tr.2)

def bad [Fintype I] (w : I → M → Result F) (a b : I → F)
    (out : LazyAGM.Output F M) (tr : LazyAGM.Transcript I M G) : Result F :=
  div (neg (sumTable fun i => mul (denominator w out tr i) (table b i)))
    (sumTable fun i => mul (denominator w out tr i) (table a i))

def badBound (n qS lenXi weightCost : Nat) : Nat :=
  2 * n * (weightCost + qS * (lenXi + weightCost + 4) + 5) + 2

theorem bad_value [Fintype I] (w : I → M → Result F) (a b : I → F)
    (out : LazyAGM.Output F M) (tr : LazyAGM.Transcript I M G) :
    (bad w a b out tr).value =
      -(∑ i, LazyAGM.denominatorCoeff (fun i m => (w i m).value) out tr i * b i) /
        (∑ i, LazyAGM.denominatorCoeff (fun i m => (w i m).value) out tr i * a i) := by
  simp [bad, denominator, LazyAGM.denominatorCoeff, sub, mul, div, neg, table, sumTable, sumList]

theorem bad_work [Fintype I] (w : I → M → Result F) (a b : I → F)
    (out : LazyAGM.Output F M) (tr : LazyAGM.Transcript I M G)
    (c : Nat) (hw : ∀ i m, (w i m).work ≤ c) :
    (bad w a b out tr).work ≤ badBound (Fintype.card I) tr.2.length out.ξ.length c := by
  have hd : ∀ i, (denominator w out tr i).work ≤
      c + tr.2.length * (out.ξ.length + c + 4) + 1 := by
    intro i
    have hl := sumList_work (fun n q => mul (coefficient out.ξ n) (w i q.1)) tr.2
      (out.ξ.length + c + 2) (by
        intro n q
        dsimp [mul]
        have := coefficient_work out.ξ n
        have := hw i q.1
        omega)
    dsimp [denominator, sub]
    have := hw i out.mstar
    nlinarith
  have hs : ∀ rho : I → F,
      (sumTable fun i => mul (denominator w out tr i) (table rho i)).work ≤
        Fintype.card I * (c + tr.2.length * (out.ξ.length + c + 4) + 5) := by
    intro rho
    have h := sumTable_work (fun i => mul (denominator w out tr i) (table rho i))
      (c + tr.2.length * (out.ξ.length + c + 4) + 3) (by
      intro i
      dsimp [mul, table]
      have := hd i
      omega)
    simpa [Nat.add_assoc] using h
  have ha := hs a
  have hb := hs b
  dsimp [bad, div, neg, badBound]
  nlinarith

end Model.ScalarWork
