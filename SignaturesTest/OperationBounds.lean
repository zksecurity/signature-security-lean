import Signatures
import Mathlib.Algebra.Field.ZMod

/-! Operation-ledger regressions. These do not assert machine-time or PPT adequacy. -/

open OracleComp OracleSpec Model.ScalarWork

namespace SignaturesTest.OperationBounds

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- Missing coefficients still cost a list scan; they are not free zeroes.
example : (coefficient ([] : List (ZMod 5)) 100).value = 0 ∧
    (coefficient ([] : List (ZMod 5)) 100).work = 1 := by decide
example : (coefficient ([2, 3] : List (ZMod 5)) 100).value = 0 ∧
    (coefficient ([2, 3] : List (ZMod 5)) 100).work = 3 := by decide
example : (coefficient ([2, 3] : List (ZMod 5)) 1).value = 3 ∧
    (coefficient ([2, 3] : List (ZMod 5)) 1).work = 2 := by decide

-- Repeated base queries contribute separately to extraction and append costs.
example : (baseCoeff ([2, 3] : List (ZMod 5)) [(true, ()), (true, ())] true).value = 0 := by
  decide
example : appendWork 3 = 6 := rfl
example : responseWork (fun _ : Unit => (⟨0, 2⟩ : Result Nat))
    (fun _ : Unit => (⟨0, 1⟩ : Result Nat)) ([((), 0), ((), 0)], []) = 9 := rfl

-- Degree, topic checks, and indexed coordinate reads are charged explicitly.
example : (power (2 : ZMod 5) 3).value = 3 ∧ (power (2 : ZMod 5) 3).work = 6 := by decide
example : (oopsWeight 3 (true, (3 : Fin 4)) ((2 : ZMod 5), true)).work = 7 := rfl
example : (oopsWeight 3 (false, (3 : Fin 4)) ((2 : ZMod 5), true)).work = 1 := rfl
example : (proximityWeight 1 (some (0 : Fin 1), true)
    ((fun _ => (2 : ZMod 5)), true)).work = 2 := rfl
example : (proximityWeight 0 (none, true)
    ((fun _ => (2 : ZMod 5)), true)).work = 1 := rfl

-- Even without source queries, full-domain extraction and division have nonzero cost.
example : goodTotalBound 10 0 0 0 0 1 = 93 := rfl
example : badTotalBound 10 0 0 0 1 = 123 := rfl

private def adaptive : OracleComp (BLS.ROM.advSpec Unit Bool) (Unit × Bool) := do
  let h ← liftM ((BLS.ROM.advSpec Unit Bool).query (.inl (.inr ())))
  if h then
    let _ ← liftM ((BLS.ROM.advSpec Unit Bool).query (.inl (.inr ())))
    pure ((), h)
  else
    let _ ← liftM ((BLS.ROM.advSpec Unit Bool).query (.inr ()))
    pure ((), h)

private theorem adaptive_budget : Model.OperationCost.Bounded BLS.CoCDH.Cost.kind
    (BLS.CoCDH.Cost.budgets 0 2 1) adaptive := by
  intro k
  fin_cases k <;> simp [adaptive, BLS.CoCDH.Cost.kind, BLS.CoCDH.Cost.budgets]

-- Both possible continuations must fit the budget; the repeated hash cannot be ignored.
example : ¬ IsQueryBoundP adaptive (fun q => BLS.CoCDH.Cost.kind q = 1) 1 := by
  simp [adaptive, BLS.CoCDH.Cost.kind]

example (z : (Unit × Bool) × Multiplicative Nat)
    (hz : z ∈ support (costDist (BLS.ROM.cacheForgery adaptive) BLS.CoCDH.Cost.groupModel)) :
    Multiplicative.toAdd z.2 ≤ 7 :=
  BLS.CoCDH.Cost.source_group_bound adaptive 0 2 1 adaptive_budget z hz

-- The final hash is present even when the adversary makes no queries.
example : ¬ IsQueryBoundP (BLS.ROM.cacheForgery
    (pure ((), false) : OracleComp (BLS.ROM.advSpec Unit Bool) (Unit × Bool)))
    (fun q => BLS.CoCDH.Cost.kind q = 1) 0 := by
  simp [BLS.ROM.cacheForgery, BLS.CoCDH.Cost.kind]

section Erasure

variable {F G₁ G₂ : Type} [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  (g₁ X₁ : G₁) (g₂ X₂ : G₂)

open Model.LazyAGM

example {M : Type} [Fintype M] [DecidableEq M] (A : Adversary F M M G₁ G₂) :
    Result.value <$> Cost.good blsWeight A g₁ X₁ g₂ X₂ =
      goodReduction BLS.Proofs.indicatorWeight A g₁ X₁ g₂ X₂ := by
  simpa only [blsWeight_value] using Cost.good_erase blsWeight A g₁ X₁ g₂ X₂

example {M : Type} [Fintype M] [DecidableEq M] (A : Adversary F M M G₁ G₂) :
    Result.value <$> Cost.bad blsWeight A g₁ X₁ g₂ X₂ =
      badReduction BLS.Proofs.indicatorWeight A g₁ X₁ g₂ X₂ := by
  simpa only [blsWeight_value] using Cost.bad_erase blsWeight A g₁ X₁ g₂ X₂

example {T : Type} [Fintype T] [DecidableEq T] (d : Nat)
    (A : Adversary F (T × Fin (d + 1)) (F × T) G₁ G₂) :
    Result.value <$> Cost.good (oopsWeight d) A g₁ X₁ g₂ X₂ =
      goodReduction (OOPS.Handle.oopsWMulti d) A g₁ X₁ g₂ X₂ := by
  simpa only [oopsWeight_value] using Cost.good_erase (oopsWeight d) A g₁ X₁ g₂ X₂

example {T : Type} [Fintype T] [DecidableEq T] (d : Nat)
    (A : Adversary F (T × Fin (d + 1)) (F × T) G₁ G₂) :
    Result.value <$> Cost.bad (oopsWeight d) A g₁ X₁ g₂ X₂ =
      badReduction (OOPS.Handle.oopsWMulti d) A g₁ X₁ g₂ X₂ := by
  simpa only [oopsWeight_value] using Cost.bad_erase (oopsWeight d) A g₁ X₁ g₂ X₂

example {S : Type} [Fintype S] [DecidableEq S] (ell : Nat)
    (A : Adversary F (Option (Fin ell) × S) ((Fin ell → F) × S) G₁ G₂) :
    Result.value <$> Cost.good (proximityWeight ell) A g₁ X₁ g₂ X₂ =
      goodReduction (Proximity.Proofs.coordinateWeight ell) A g₁ X₁ g₂ X₂ := by
  simpa only [proximityWeight_value] using Cost.good_erase (proximityWeight ell) A g₁ X₁ g₂ X₂

example {S : Type} [Fintype S] [DecidableEq S] (ell : Nat)
    (A : Adversary F (Option (Fin ell) × S) ((Fin ell → F) × S) G₁ G₂) :
    Result.value <$> Cost.bad (proximityWeight ell) A g₁ X₁ g₂ X₂ =
      badReduction (Proximity.Proofs.coordinateWeight ell) A g₁ X₁ g₂ X₂ := by
  simpa only [proximityWeight_value] using Cost.bad_erase (proximityWeight ell) A g₁ X₁ g₂ X₂

end Erasure

end SignaturesTest.OperationBounds

/-- info: 'BLS.CoCDH.Cost.reduction_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BLS.CoCDH.Cost.reduction_bound

/-- info: 'BLS.CoCDH.Cost.reduction_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BLS.CoCDH.Cost.reduction_erase

/-- info: 'Model.LazyAGM.Cost.bls_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Model.LazyAGM.Cost.bls_bounds

/-- info: 'Model.LazyAGM.Cost.oops_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Model.LazyAGM.Cost.oops_bounds

/-- info: 'Model.LazyAGM.Cost.proximity_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Model.LazyAGM.Cost.proximity_bounds

/-- info: 'Model.LazyAGM.Cost.good_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Model.LazyAGM.Cost.good_erase

/-- info: 'Model.LazyAGM.Cost.bad_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Model.LazyAGM.Cost.bad_erase
