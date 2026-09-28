import Signatures.Model.OperationCost
import Signatures.Model.SimulationWork

/-! Concrete algebraic-operation and transcript costs for the exact private-table AGM reductions.
Sampling and the adversary's local computation are separate from this ledger. -/

open OracleComp OracleSpec

namespace Model.LazyAGM.Cost

variable {F I M G₁ G₂ : Type}

def isHash : (advSpec I M Unit).Domain → Prop
  | .inl (.inr _) => True
  | _ => False

instance : DecidablePred (isHash (I := I) (M := M)) :=
  fun q => by cases q with
  | inl q => cases q <;> simp [isHash] <;> infer_instance
  | inr q => simp [isHash]; infer_instance

theorem fixedRun_lengths (A : Adversary F I M G₁ G₂) (pk : G₂)
    (H : I → G₁) (sign : M → G₁) (qH qS : Nat)
    (hh : IsQueryBoundP (A.main pk) isHash qH)
    (hs : IsQueryBoundP (A.main pk) (fun i => Sum.isRight i = true) qS)
    (z : Output F M × Transcript I M G₁) (hz : z ∈ support (fixedRun A pk H sign)) :
    z.2.1.length ≤ qH ∧ z.2.2.length ≤ qS := by
  constructor
  · simpa using OperationCost.state_growth (fixedImpl H sign) isHash
      (fun tr => tr.1.length) (by
        intro q tr p hp
        rcases q with (q | i) | m <;>
          simp [fixedImpl, handler, isHash] at hp ⊢ <;> rcases hp with ⟨u, rfl⟩ <;> simp)
      (A.main pk) qH hh ([], []) z hz
  · simpa using OperationCost.state_growth (fixedImpl H sign)
      (fun i => Sum.isRight i = true) (fun tr => tr.2.length) (by
        intro q tr p hp
        rcases q with (q | i) | m <;>
          simp [fixedImpl, handler] at hp ⊢ <;> rcases hp with ⟨u, rfl⟩ <;> simp)
      (A.main pk) qS hs ([], []) z hz

theorem fixedRun_output (A : Adversary F I M G₁ G₂) (pk : G₂)
    (H : I → G₁) (sign : M → G₁) (z : Output F M × Transcript I M G₁)
    (hz : z ∈ support (fixedRun A pk H sign)) : z.1 ∈ support (A.main pk) := by
  apply support_simulateQ_run'_subset (fixedImpl H sign) (A.main pk) ([], [])
  rw [StateT.run'_eq, support_map]
  exact ⟨z, hz, rfl⟩

variable [Field F] [SampleableType F] [Fintype I] [DecidableEq I]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

noncomputable def good (w : I → M → ScalarWork.Result F) (A : Adversary F I M G₁ G₂)
    (g₁ X₁ : G₁) (_g₂ X₂ : G₂) : ProbComp (ScalarWork.Result F) := do
  let rho ← ($ᵗ (I → F) : ProbComp (I → F))
  let (out, tr) ← fixedRun A X₂ (fun i => rho i • g₁)
    (fun m => (∑ i, rho i * (w i m).value) • X₁)
  let extraction := ScalarWork.good w rho out tr
  pure ⟨extraction.value, extraction.work +
    ScalarWork.responseWork (ScalarWork.goodHash rho g₁) (ScalarWork.goodSign w rho X₁) tr⟩

noncomputable def bad (w : I → M → ScalarWork.Result F) (A : Adversary F I M G₁ G₂)
    (g₁ X₁ : G₁) (g₂ _X₂ : G₂) : ProbComp (ScalarWork.Result F) := do
  let kappa ← ($ᵗ F : ProbComp F)
  let a ← ($ᵗ (I → F) : ProbComp (I → F))
  let b ← ($ᵗ (I → F) : ProbComp (I → F))
  let H := fun i => a i • X₁ + b i • g₁
  let (out, tr) ← fixedRun A (kappa • g₂) H (fun m => kappa • ∑ i, (w i m).value • H i)
  let extraction := ScalarWork.bad w a b out tr
  pure ⟨extraction.value, extraction.work +
    ScalarWork.responseWork (ScalarWork.badHash a b g₁ X₁) (ScalarWork.badSign w a b g₁ X₁ kappa) tr + 1⟩

omit [AddCommGroup G₂] [Module F G₂] in
theorem good_erase (w : I → M → ScalarWork.Result F) (A : Adversary F I M G₁ G₂)
    (g₁ X₁ : G₁) (g₂ X₂ : G₂) :
    ScalarWork.Result.value <$> good w A g₁ X₁ g₂ X₂ =
      goodReduction (fun i m => (w i m).value) A g₁ X₁ g₂ X₂ := by
  simp [good, goodReduction, map_bind, ScalarWork.good_value]

theorem bad_erase (w : I → M → ScalarWork.Result F) (A : Adversary F I M G₁ G₂)
    (g₁ X₁ : G₁) (g₂ X₂ : G₂) :
    ScalarWork.Result.value <$> bad w A g₁ X₁ g₂ X₂ =
      badReduction (fun i m => (w i m).value) A g₁ X₁ g₂ X₂ := by
  simp [bad, badReduction, map_bind, ScalarWork.bad_value]

omit [AddCommGroup G₂] [Module F G₂] in
theorem good_bound (w : I → M → ScalarWork.Result F) (A : Adversary F I M G₁ G₂)
    (g₁ X₁ : G₁) (g₂ X₂ : G₂) (qH qS lH lS c : Nat)
    (hh : IsQueryBoundP (A.main X₂) isHash qH)
    (hs : IsQueryBoundP (A.main X₂) (fun i => Sum.isRight i = true) qS)
    (hl : ∀ out ∈ support (A.main X₂), out.γ.length ≤ lH ∧ out.ξ.length ≤ lS)
    (hw : ∀ i m, (w i m).work ≤ c)
    (z : ScalarWork.Result F) (hz : z ∈ support (good w A g₁ X₁ g₂ X₂)) :
    z.work ≤ ScalarWork.goodTotalBound (Fintype.card I) qH qS lH lS c := by
  simp only [good, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨rho, _, ⟨out, tr⟩, htr, rfl⟩ := hz
  have hq := fixedRun_lengths A X₂ _ _ qH qS hh hs (out, tr) htr
  have ho := hl out (fixedRun_output A X₂ _ _ (out, tr) htr)
  have he := ScalarWork.good_work w rho out tr c hw
  have hr := ScalarWork.responseWork_bound (ScalarWork.goodHash rho g₁)
    (ScalarWork.goodSign w rho X₁) tr 2 (Fintype.card I * (c + 4) + 1)
    (fun i => le_of_eq (ScalarWork.goodHash_work rho g₁ i))
    (fun m => ScalarWork.goodSign_work w rho X₁ m c hw)
  have htotal : (ScalarWork.good w rho out tr).work +
      ScalarWork.responseWork (ScalarWork.goodHash rho g₁) (ScalarWork.goodSign w rho X₁) tr ≤
      ScalarWork.goodTotalBound (Fintype.card I) tr.1.length tr.2.length out.γ.length out.ξ.length c := by
    unfold ScalarWork.goodTotalBound
    nlinarith
  apply htotal.trans
  unfold ScalarWork.goodTotalBound ScalarWork.goodBound
  gcongr <;> first | exact hq.1 | exact hq.2 | exact ho.1 | exact ho.2

theorem bad_bound (w : I → M → ScalarWork.Result F) (A : Adversary F I M G₁ G₂)
    (g₁ X₁ : G₁) (g₂ X₂ : G₂) (qH qS lS c : Nat)
    (hh : ∀ kappa : F, IsQueryBoundP (A.main (kappa • g₂)) isHash qH)
    (hs : ∀ kappa : F, IsQueryBoundP (A.main (kappa • g₂)) (fun i => Sum.isRight i = true) qS)
    (hl : ∀ kappa : F, ∀ out ∈ support (A.main (kappa • g₂)), out.ξ.length ≤ lS)
    (hw : ∀ i m, (w i m).work ≤ c)
    (z : ScalarWork.Result F) (hz : z ∈ support (bad w A g₁ X₁ g₂ X₂)) :
    z.work ≤ ScalarWork.badTotalBound (Fintype.card I) qH qS lS c := by
  simp only [bad, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨kappa, _, a, _, b, _, ⟨out, tr⟩, htr, rfl⟩ := hz
  have hq := fixedRun_lengths A (kappa • g₂) _ _ qH qS (hh kappa) (hs kappa) (out, tr) htr
  have ho := hl kappa out (fixedRun_output A (kappa • g₂) _ _ (out, tr) htr)
  have he := ScalarWork.bad_work w a b out tr c hw
  have hr := ScalarWork.responseWork_bound (ScalarWork.badHash a b g₁ X₁)
    (ScalarWork.badSign w a b g₁ X₁ kappa) tr 5 (Fintype.card I * (c + 8) + 1)
    (fun i => le_of_eq (ScalarWork.badHash_work a b g₁ X₁ i))
    (fun m => ScalarWork.badSign_work w a b g₁ X₁ kappa m c hw)
  have htotal : (ScalarWork.bad w a b out tr).work +
      ScalarWork.responseWork (ScalarWork.badHash a b g₁ X₁) (ScalarWork.badSign w a b g₁ X₁ kappa) tr + 1 ≤
      ScalarWork.badTotalBound (Fintype.card I) tr.1.length tr.2.length out.ξ.length c := by
    unfold ScalarWork.badTotalBound
    nlinarith
  apply htotal.trans
  unfold ScalarWork.badTotalBound ScalarWork.badBound
  gcongr <;> first | exact hq.1 | exact hq.2

/-- Both branch ledgers under uniform source-query and coefficient-size bounds. -/
theorem bounds (w : I → M → ScalarWork.Result F) (A : Adversary F I M G₁ G₂)
    (g₁ X₁ : G₁) (g₂ : G₂) (x : F) (qH qS lH lS c : Nat)
    (hh : ∀ k : F, IsQueryBoundP (A.main (k • g₂)) isHash qH)
    (hs : ∀ k : F, IsQueryBoundP (A.main (k • g₂)) (fun i => Sum.isRight i = true) qS)
    (hl : ∀ k : F, ∀ out ∈ support (A.main (k • g₂)),
      out.γ.length ≤ lH ∧ out.ξ.length ≤ lS)
    (hw : ∀ i m, (w i m).work ≤ c) :
    (∀ z ∈ support (good w A g₁ X₁ g₂ (x • g₂)),
      z.work ≤ ScalarWork.goodTotalBound (Fintype.card I) qH qS lH lS c) ∧
    (∀ z ∈ support (bad w A g₁ X₁ g₂ (x • g₂)),
      z.work ≤ ScalarWork.badTotalBound (Fintype.card I) qH qS lS c) :=
  ⟨good_bound w A g₁ X₁ g₂ (x • g₂) qH qS lH lS c (hh x) (hs x) (hl x) hw,
   bad_bound w A g₁ X₁ g₂ (x • g₂) qH qS lS c hh hs (fun k out h => (hl k out h).2) hw⟩

end Model.LazyAGM.Cost
