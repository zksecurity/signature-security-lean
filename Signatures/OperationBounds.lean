import Signatures.BLS.Proofs.LazyAGM
import Signatures.OOPS.Proofs.LazyAGM
import Signatures.Proximity.Proofs.LazyAGM
import Signatures.BLS.CoCDH.Proofs.OperationCost
import Signatures.LinearFunctional.Proofs.OperationCost

/-! Scheme-specific arithmetic implementations of the weights used in the extraction bounds.
These bounds count arithmetic operations and indexed reads, not encoded bit operations. -/

namespace Model.ScalarWork

variable {F : Type} [Field F]

/-- Straight-line repeated multiplication, charging one multiplication and one loop step. -/
def power (x : F) : Nat → Result F
  | 0 => ⟨1, 0⟩
  | n + 1 =>
      let r := power x n
      ⟨r.value * x, r.work + 2⟩

@[simp] theorem power_value (x : F) (n : Nat) : (power x n).value = x ^ n := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp [power, ih, pow_succ]

@[simp] theorem power_work (x : F) (n : Nat) : (power x n).work = 2 * n := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp [power, ih, Nat.mul_add]

def blsWeight {M : Type} [DecidableEq M] (i m : M) : Result F :=
  ⟨if i = m then 1 else 0, 1⟩

@[simp] theorem blsWeight_value {M : Type} [DecidableEq M] (i m : M) :
    (blsWeight (F := F) i m).value = BLS.Proofs.indicatorWeight i m := rfl

theorem blsWeight_work {M : Type} [DecidableEq M] (i m : M) :
    (blsWeight (F := F) i m).work ≤ 1 := le_rfl

def oopsWeight {T : Type} [DecidableEq T] (d : Nat)
    (b : T × Fin (d + 1)) (mt : F × T) : Result F :=
  if b.1 = mt.2 then
    let r := power mt.1 b.2.val
    ⟨r.value, r.work + 1⟩
  else ⟨0, 1⟩

@[simp] theorem oopsWeight_value {T : Type} [DecidableEq T] (d : Nat)
    (b : T × Fin (d + 1)) (mt : F × T) :
    (oopsWeight d b mt).value = OOPS.Handle.oopsWMulti d b mt := by
  by_cases h : b.1 = mt.2 <;> simp [oopsWeight, OOPS.Handle.oopsWMulti, h]

theorem oopsWeight_work {T : Type} [DecidableEq T] (d : Nat)
    (b : T × Fin (d + 1)) (mt : F × T) :
    (oopsWeight d b mt).work ≤ 2 * d + 1 := by
  dsimp [oopsWeight]
  split
  · simp only [power_work]
    have := b.2.isLt
    omega
  · simp

def proximityWeight {S : Type} [DecidableEq S] (ell : Nat)
    (b : Option (Fin ell) × S) (ms : (Fin ell → F) × S) : Result F :=
  if b.2 = ms.2 then
    match b.1 with
    | none => ⟨1, 1⟩
    | some k => ⟨ms.1 k, 2⟩
  else ⟨0, 1⟩

@[simp] theorem proximityWeight_value {S : Type} [DecidableEq S] (ell : Nat)
    (b : Option (Fin ell) × S) (ms : (Fin ell → F) × S) :
    (proximityWeight ell b ms).value = Proximity.Proofs.coordinateWeight ell b ms := by
  by_cases h : b.2 = ms.2 <;> cases hb : b.1 <;>
    simp [proximityWeight, Proximity.Proofs.coordinateWeight, h, hb]

theorem proximityWeight_work {S : Type} [DecidableEq S] (ell : Nat)
    (b : Option (Fin ell) × S) (ms : (Fin ell → F) × S) :
    (proximityWeight ell b ms).work ≤ 2 := by
  by_cases h : b.2 = ms.2 <;> cases hb : b.1 <;> simp [proximityWeight, h, hb]

-- The finite-domain factors are not replaced by the number of oracle queries.
example {T : Type} [Fintype T] (d : Nat) :
    Fintype.card (T × Fin (d + 1)) = Fintype.card T * (d + 1) := by simp

example {S : Type} [Fintype S] (ell : Nat) :
    Fintype.card (Option (Fin ell) × S) = (ell + 1) * Fintype.card S := by simp

end Model.ScalarWork

open OracleComp Model.ScalarWork

namespace Model.LazyAGM.Cost

variable {F G₁ G₂ : Type} [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

theorem bls_bounds {M : Type} [Fintype M] [DecidableEq M]
    (A : Adversary F M M G₁ G₂) (g₁ X₁ : G₁) (g₂ : G₂) (x : F)
    (qH qS lH lS : Nat)
    (hh : ∀ k : F, IsQueryBoundP (A.main (k • g₂)) isHash qH)
    (hs : ∀ k : F, IsQueryBoundP (A.main (k • g₂)) (fun i => Sum.isRight i = true) qS)
    (hl : ∀ k : F, ∀ out ∈ support (A.main (k • g₂)),
      out.γ.length ≤ lH ∧ out.ξ.length ≤ lS) :
    (∀ z ∈ support (good blsWeight A g₁ X₁ g₂ (x • g₂)),
      z.work ≤ goodTotalBound (Fintype.card M) qH qS lH lS 1) ∧
    (∀ z ∈ support (bad blsWeight A g₁ X₁ g₂ (x • g₂)),
      z.work ≤ badTotalBound (Fintype.card M) qH qS lS 1) :=
  bounds blsWeight A g₁ X₁ g₂ x qH qS lH lS 1 hh hs hl blsWeight_work

theorem oops_bounds {T : Type} [Fintype T] [DecidableEq T] (d : Nat)
    (A : Adversary F (T × Fin (d + 1)) (F × T) G₁ G₂)
    (g₁ X₁ : G₁) (g₂ : G₂) (x : F) (qH qS lH lS : Nat)
    (hh : ∀ k : F, IsQueryBoundP (A.main (k • g₂)) isHash qH)
    (hs : ∀ k : F, IsQueryBoundP (A.main (k • g₂)) (fun i => Sum.isRight i = true) qS)
    (hl : ∀ k : F, ∀ out ∈ support (A.main (k • g₂)),
      out.γ.length ≤ lH ∧ out.ξ.length ≤ lS) :
    (∀ z ∈ support (good (oopsWeight d) A g₁ X₁ g₂ (x • g₂)),
      z.work ≤ goodTotalBound (Fintype.card T * (d + 1)) qH qS lH lS (2 * d + 1)) ∧
    (∀ z ∈ support (bad (oopsWeight d) A g₁ X₁ g₂ (x • g₂)),
      z.work ≤ badTotalBound (Fintype.card T * (d + 1)) qH qS lS (2 * d + 1)) := by
  simpa using bounds (oopsWeight d) A g₁ X₁ g₂ x qH qS lH lS (2 * d + 1)
    hh hs hl (oopsWeight_work d)

theorem proximity_bounds {S : Type} [Fintype S] [DecidableEq S] (ell : Nat)
    (A : Adversary F (Option (Fin ell) × S) ((Fin ell → F) × S) G₁ G₂)
    (g₁ X₁ : G₁) (g₂ : G₂) (x : F) (qH qS lH lS : Nat)
    (hh : ∀ k : F, IsQueryBoundP (A.main (k • g₂)) isHash qH)
    (hs : ∀ k : F, IsQueryBoundP (A.main (k • g₂)) (fun i => Sum.isRight i = true) qS)
    (hl : ∀ k : F, ∀ out ∈ support (A.main (k • g₂)),
      out.γ.length ≤ lH ∧ out.ξ.length ≤ lS) :
    (∀ z ∈ support (good (proximityWeight ell) A g₁ X₁ g₂ (x • g₂)),
      z.work ≤ goodTotalBound ((ell + 1) * Fintype.card S) qH qS lH lS 2) ∧
    (∀ z ∈ support (bad (proximityWeight ell) A g₁ X₁ g₂ (x • g₂)),
      z.work ≤ badTotalBound ((ell + 1) * Fintype.card S) qH qS lS 2) := by
  simpa using bounds (proximityWeight ell) A g₁ X₁ g₂ x qH qS lH lS 2
    hh hs hl (proximityWeight_work ell)

end Model.LazyAGM.Cost
