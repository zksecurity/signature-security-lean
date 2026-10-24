import Proofs.Model.ScalarWork

/-! Algebraic reply costs and list-transcript bookkeeping for the private-table simulators.
Group scalar multiplication and group addition are atomic unit operations. Sampling and the
adversary's local computation are not included. A table read assumes random-access storage. -/

namespace Model.ScalarWork

variable {F I M G : Type} [Field F] [Fintype I] [AddCommGroup G] [Module F G]

def point (P : G) : Result G := ⟨P, 0⟩
def scale (x : Result F) (P : Result G) : Result G :=
  ⟨x.value • P.value, x.work + P.work + 1⟩
def pointAdd (P Q : Result G) : Result G :=
  ⟨P.value + Q.value, P.work + Q.work + 1⟩

def goodHash (rho : I → F) (g : G) (i : I) : Result G := scale (table rho i) (point g)
def goodSign (w : I → M → Result F) (rho : I → F) (X : G) (m : M) : Result G :=
  scale (weighted w rho m) (point X)
def badHash (a b : I → F) (g X : G) (i : I) : Result G :=
  pointAdd (scale (table a i) (point X)) (scale (table b i) (point g))
def badSign (w : I → M → Result F) (a b : I → F) (g X : G) (kappa : F) (m : M) : Result G :=
  scale (input kappa) (sumTable fun i => scale (w i m) (badHash a b g X i))

omit [Fintype I] in
@[simp] theorem goodHash_value (rho : I → F) (g : G) (i : I) :
    (goodHash rho g i).value = rho i • g := rfl
omit [Fintype I] in
@[simp] theorem goodHash_work (rho : I → F) (g : G) (i : I) :
    (goodHash rho g i).work = 2 := rfl
@[simp] theorem goodSign_value (w : I → M → Result F) (rho : I → F) (X : G) (m : M) :
    (goodSign w rho X m).value = (∑ i, rho i * (w i m).value) • X := rfl
omit [Fintype I] in
@[simp] theorem badHash_value (a b : I → F) (g X : G) (i : I) :
    (badHash a b g X i).value = a i • X + b i • g := rfl
omit [Fintype I] in
@[simp] theorem badHash_work (a b : I → F) (g X : G) (i : I) :
    (badHash a b g X i).work = 5 := rfl
@[simp] theorem badSign_value (w : I → M → Result F) (a b : I → F)
    (g X : G) (kappa : F) (m : M) :
    (badSign w a b g X kappa m).value = kappa • ∑ i, (w i m).value • (a i • X + b i • g) := rfl

theorem goodSign_work (w : I → M → Result F) (rho : I → F) (X : G) (m : M)
    (c : Nat) (hw : ∀ i m, (w i m).work ≤ c) :
    (goodSign w rho X m).work ≤ Fintype.card I * (c + 4) + 1 := by
  simpa [goodSign, scale, point] using Nat.add_le_add_right (weighted_work w rho m c hw) 1

theorem badSign_work (w : I → M → Result F) (a b : I → F) (g X : G) (kappa : F) (m : M)
    (c : Nat) (hw : ∀ i m, (w i m).work ≤ c) :
    (badSign w a b g X kappa m).work ≤ Fintype.card I * (c + 8) + 1 := by
  have h := sumTable_work (fun i => scale (w i m) (badHash a b g X i)) (c + 6) (by
    intro i
    dsimp [scale]
    have := hw i m
    omega)
  simpa [badSign, scale, input, Nat.add_assoc] using Nat.add_le_add_right h 1

/-- Appending the next singleton copies the previous list and creates one new cell. -/
def appendWork : Nat → Nat
  | 0 => 0
  | n + 1 => appendWork n + n + 1

theorem appendWork_bound (n : Nat) : appendWork n ≤ n * (n + 1) := by
  induction n with
  | zero => simp [appendWork]
  | succ n ih => dsimp [appendWork]; nlinarith

def responseWork (hash : I → Result G) (sign : M → Result G)
    (tr : LazyAGM.Transcript I M G) : Nat :=
  (tr.1.map fun p => (hash p.1).work).sum + (tr.2.map fun p => (sign p.1).work).sum +
    appendWork tr.1.length + appendWork tr.2.length + tr.1.length + tr.2.length

private theorem listWork_bound {α β : Type} (f : α → Result β) (xs : List α) (c : Nat)
    (h : ∀ x, (f x).work ≤ c) : (xs.map fun x => (f x).work).sum ≤ xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have := h x
      nlinarith

omit [Fintype I] [AddCommGroup G] in
theorem responseWork_bound (hash : I → Result G) (sign : M → Result G)
    (tr : LazyAGM.Transcript I M G) (cH cS : Nat)
    (hh : ∀ i, (hash i).work ≤ cH) (hs : ∀ m, (sign m).work ≤ cS) :
    responseWork hash sign tr ≤
      tr.1.length * (cH + tr.1.length + 2) + tr.2.length * (cS + tr.2.length + 2) := by
  have h1 := listWork_bound (fun p : I × G => hash p.1) tr.1 cH (fun p => hh p.1)
  have h2 := listWork_bound (fun p : M × G => sign p.1) tr.2 cS (fun p => hs p.1)
  have h3 := appendWork_bound tr.1.length
  have h4 := appendWork_bound tr.2.length
  unfold responseWork
  nlinarith

def goodTotalBound (n qH qS lenGamma lenXi weightCost : Nat) : Nat :=
  goodBound n qH qS lenGamma lenXi weightCost +
    qH * (qH + 4) + qS * (n * (weightCost + 4) + qS + 3)

def badTotalBound (n qH qS lenXi weightCost : Nat) : Nat :=
  badBound n qS lenXi weightCost +
    qH * (qH + 7) + qS * (n * (weightCost + 8) + qS + 3) + 1

end Model.ScalarWork
