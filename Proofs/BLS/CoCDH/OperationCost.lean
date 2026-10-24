import Signatures.BLS.CoCDH.Spec.Coron
import Proofs.Model.OperationCost

/-!
# Coron group-operation accounting

Each hash response uses one G1 scalar multiplication and one addition. A signing response
uses at most one scalar multiplication. Extraction uses one multiplication and one subtraction.
The automatically inserted forgery hash is counted. This ledger does not count sampling,
cache implementation, scalar/bit arithmetic, or the adversary's local computation.
-/

open OracleComp OracleSpec Model.OperationCost

namespace BLS.CoCDH.Cost

def kind {M : Type} : (BLS.ROM.advSpec M Unit).Domain → Fin 3
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => 2

def budgets (qR qH qS : Nat) : Fin 3 → Nat := ![qR, qH, qS]
def prices : Fin 3 → Nat := ![0, 2, 1]

def groupModel {M G : Type} : CostModel (BLS.ROM.advSpec M G) Nat :=
  ⟨fun q => prices (kind q)⟩

variable {M G₁ : Type}

theorem cached_budget (oa : BLS.ROM.Adversary M G₁) (qR qH qS : Nat)
    (h : Bounded kind (budgets qR qH qS) oa) :
    Bounded kind (budgets qR (qH + 1) qS) (BLS.ROM.cacheForgery oa) := by
  intro k
  have hb := isQueryBoundP_bind (p := fun q => kind q = k) (h k)
    (fun out _ => show IsQueryBoundP
      (do let _ ← (liftM ((BLS.ROM.advSpec M G₁).query (.inl (.inr out.1))) :
            OracleComp (BLS.ROM.advSpec M G₁) G₁)
          pure out) (fun q => kind q = k) (if k = 1 then 1 else 0) from by
      fin_cases k <;> simp [kind])
  fin_cases k <;> simpa [BLS.ROM.cacheForgery, budgets] using hb

theorem source_group_bound (oa : BLS.ROM.Adversary M G₁) (qR qH qS : Nat)
    (h : Bounded kind (budgets qR qH qS) oa) :
    ∀ z ∈ support (costDist (BLS.ROM.cacheForgery oa) groupModel),
      Multiplicative.toAdd z.2 ≤ 2 * (qH + 1) + qS := by
  have hb := simulate_bound kind prices (budgets qR (qH + 1) qS)
    (addCostOracle groupModel.queryCost)
    (by
      intro q
      simp [addCostOracle, QueryImpl.withAddCost, QueryImpl.withCost,
        AddWriterT.PathwiseCostAtMost, groupModel])
    (BLS.ROM.cacheForgery oa) (cached_budget oa qR qH qS h)
  simpa [AddWriterT.PathwiseCostAtMost, costDist, instrumentedRun,
    addCostOracle, QueryImpl.withAddCost, allowance, Fin.sum_univ_succ, prices, budgets] using hb

variable {F G₂ : Type} [Field F] [SampleableType F]
  [DecidableEq M] [AddCommGroup G₁] [Module F G₁]

noncomputable def program (g₁ X₁ : G₁) (X₂ : G₂) (h : G₁) (qS : Nat)
    (adv : BLS.ROM.AdversaryPK M G₁ G₂) :
    OracleComp (unifSpec + (M →ₒ Fin (qS + 1))) (G₁ × Nat) := do
  let ((out, cost), st) ← (simulateQ (coronOracleLazy (F := F) g₁ X₁ h qS)
    (costDist (BLS.ROM.cacheForgeryPK adv X₂) groupModel)).run ((fun _ => none), ∅)
  pure (out.2 - ((st.1 out.1).getD 0) • X₁, Multiplicative.toAdd cost + 2)

noncomputable def reduction (qS : Nat) (adv : BLS.ROM.AdversaryPK M G₁ G₂)
    (g₁ : G₁) (_g₂ : G₂) (X₁ : G₁) (X₂ : G₂) (h : G₁) : ProbComp (G₁ × Nat) :=
  (simulateQ (lazyCoinImpl (D := M) (R := Fin (qS + 1)))
    (program (F := F) g₁ X₁ X₂ h qS adv)).run' ∅

theorem program_erase (g₁ X₁ : G₁) (X₂ : G₂) (h : G₁) (qS : Nat)
    (adv : BLS.ROM.AdversaryPK M G₁ G₂) :
    Prod.fst <$> program (F := F) g₁ X₁ X₂ h qS adv =
      coronReductionProgram (F := F) g₁ X₁ X₂ h qS (BLS.ROM.cacheForgeryPK adv) := by
  have hp := congrArg
    (fun oa => (simulateQ (coronOracleLazy (F := F) g₁ X₁ h qS) oa).run ((fun _ => none), ∅))
    (fst_map_costDist (BLS.ROM.cacheForgeryPK adv X₂) groupModel)
  simp only [simulateQ_map, StateT.run_map] at hp
  simp only [program, coronReductionProgram, map_bind, map_pure]
  rw [← hp, bind_map_left]

theorem reduction_erase (qS : Nat) (adv : BLS.ROM.AdversaryPK M G₁ G₂)
    (g₁ : G₁) (g₂ : G₂) (X₁ : G₁) (X₂ : G₂) (h : G₁) :
    Prod.fst <$> reduction (F := F) qS adv g₁ g₂ X₁ X₂ h =
      coronReductionLazyPK (F := F) qS (BLS.ROM.cacheForgeryPK adv) g₁ g₂ X₁ X₂ h := by
  simpa [reduction, coronReductionLazyPK, simulateQ_map] using
    congrArg (fun oa => (simulateQ (lazyCoinImpl (D := M) (R := Fin (qS + 1))) oa).run' ∅)
      (program_erase (F := F) g₁ X₁ X₂ h qS adv)

theorem reduction_bound (qR qH qS : Nat) (adv : BLS.ROM.AdversaryPK M G₁ G₂)
    (g₁ : G₁) (g₂ : G₂) (X₁ : G₁) (X₂ : G₂) (h : G₁)
    (hq : Bounded kind (budgets qR qH qS) (adv X₂))
    (z : G₁ × Nat) (hz : z ∈ support (reduction (F := F) qS adv g₁ g₂ X₁ X₂ h)) :
    z.2 ≤ 2 * (qH + 1) + qS + 2 := by
  have hp := support_simulateQ_run'_subset
    (lazyCoinImpl (D := M) (R := Fin (qS + 1))) _ ∅ hz
  simp only [program, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
  obtain ⟨⟨⟨out, cost⟩, st⟩, hs, rfl⟩ := hp
  have hc : (out, cost) ∈ support (costDist (BLS.ROM.cacheForgeryPK adv X₂) groupModel) := by
    apply support_simulateQ_run'_subset (coronOracleLazy (F := F) g₁ X₁ h qS) _
      ((fun _ => none), ∅)
    rw [StateT.run'_eq, support_map]
    exact ⟨((out, cost), st), hs, rfl⟩
  exact Nat.add_le_add_right (source_group_bound (adv X₂) qR qH qS hq (out, cost) hc) 2

end BLS.CoCDH.Cost
