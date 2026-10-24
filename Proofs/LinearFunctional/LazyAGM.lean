import Signatures.Model.LazyAGM
import Signatures.Model.CoCDH
import Proofs.LinearFunctional.Adaptive
import Proofs.BLS.CoCDH.LazyCoin
import Mathlib.Data.List.Indexes
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-! # Lazy-oracle coupling and adaptive algebraic extraction -/

open BilinearGroup

open OracleComp OracleSpec AlgebraicGroupModel AlgebraicGroupModel.LinFunctional

namespace Model.LazyAGM.Proofs

variable {F ι M G₁ G₂ : Type}

/-- Interpreting base queries can only restrict the original program's operational support. -/
theorem table_support {B : Type} (H : ι → G₁)
    (oa : OracleComp (baseSpec ι G₁) B) (z : B)
    (hz : z ∈ support (simulateQ (BLS.CoCDH.coinTableImpl H) oa)) : z ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simpa using hz
  | query_bind q k ih =>
      simp only [simulateQ_bind, mem_support_bind_iff] at hz
      obtain ⟨u, _, hu⟩ := hz
      exact (mem_support_bind_iff _ _ _).mpr ⟨u, mem_support_query q u, ih u hu⟩

def Consistent (H : ι → G₁) (signO : M → G₁) (tr : Transcript ι M G₁) : Prop :=
  (∀ p ∈ tr.1, p.2 = H p.1) ∧ (∀ p ∈ tr.2, p.2 = signO p.1)

theorem fixed_consistent {B : Type} (H : ι → G₁) (signO : M → G₁)
    (oa : OracleComp (advSpec ι M G₁) B) (tr : Transcript ι M G₁)
    (hc : Consistent H signO tr) (z : B × Transcript ι M G₁)
    (hz : z ∈ support ((simulateQ (fixedImpl H signO) oa).run tr)) :
    Consistent H signO z.2 := by
  apply simulateQ_run_preservesInv (fixedImpl H signO) (Consistent H signO) ?_ oa tr hc z hz
  intro q tr hc z hz
  rcases q with (n | i) | m <;> simp [fixedImpl, handler] at hz
  · obtain ⟨u, rfl⟩ := hz
    exact hc
  all_goals
    subst z
    simpa only [Consistent, List.forall_mem_append, List.forall_mem_singleton,
      and_true, eq_self] using hc

def toForgery [AddCommMonoid F] [DecidableEq ι]
    (z : Output F M × Transcript ι M G₁) : DynForgery F M ι :=
  ⟨z.2.2.length, {
    mstar := z.1.mstar
    v := fun q => (z.2.2.get q).1
    β := z.1.β
    γ := baseCoeff z.1.γ z.2.1
    ξ := fun q => tokenCoeff z.1.ξ q }⟩

def extracted [AddCommMonoid F] [DecidableEq ι] (A : Adversary F ι M G₁ G₂) :
    AdaptiveAdv F M ι G₁ G₂ :=
  fun pk H signO => toForgery <$> fixedRun A pk H signO

theorem toForgery_messages [AddCommMonoid F] [DecidableEq ι]
    (z : Output F M × Transcript ι M G₁) :
    List.ofFn (toForgery z).2.v = z.2.2.map Prod.fst := by
  simp [toForgery, ← List.map_ofFn, List.ofFn_get]

theorem toForgery_fresh [AddCommMonoid F] [DecidableEq ι]
    (z : Output F M × Transcript ι M G₁) :
    (toForgery z).Fresh ↔ z.1.mstar ∉ z.2.2.map Prod.fst := by
  rw [← toForgery_messages z]
  change (toForgery z).Fresh ↔ (toForgery z).2.mstar ∉ List.ofFn (toForgery z).2.v
  simp [DynForgery.Fresh, eq_comm]

section Algebra

variable [Field F] [Fintype ι] [DecidableEq ι] [AddCommGroup G₁] [Module F G₁]

theorem baseCoeff_sum (coeff : List F) (tr : List (ι × G₁)) (H : ι → G₁) :
    (∑ i, baseCoeff coeff tr i • H i) =
      (tr.mapIdx fun n p => tokenCoeff coeff n • H p.1).sum := by
  simp only [baseCoeff, List.mapIdx_eq_ofFn, List.sum_ofFn, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp

theorem materialize_eq (g₁ : G₁) (H : ι → G₁) (signO : M → G₁)
    (z : Output F M × Transcript ι M G₁) (hc : Consistent H signO z.2) :
    materialize g₁ z.1 z.2 = dynForgeryElem g₁ (toForgery z) H signO := by
  simp only [materialize_eq_weightedReplies, dynForgeryElem, forgeryElem, toForgery, baseCoeff_sum,
    weightedReplies, List.mapIdx_eq_ofFn, List.sum_ofFn]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun q _ => by rw [hc.1 _ (List.get_mem _ q)]
  · exact Finset.sum_congr rfl fun q _ => by rw [hc.2 _ (List.get_mem _ q)]

theorem evalTerms_table (H : ι → G₁) (ts : List (ι × F)) :
    simulateQ (BLS.CoCDH.coinTableImpl H) (evalTerms ts) =
      pure ((ts.map fun p => p.2 • H p.1).sum) := by
  induction ts with
  | nil => simp [evalTerms]
  | cons p ts ih =>
      simp only [evalTerms, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
        List.map_cons, List.sum_cons]
      change (pure (H p.1) >>= fun h => simulateQ (BLS.CoCDH.coinTableImpl H) (evalTerms ts)
        >>= fun r => pure (p.2 • h + r)) = _
      rw [pure_bind, ih, pure_bind]

theorem run_table [SampleableType F] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂]
    (terms : M → List (ι × F)) (w : ι → M → F)
    (ht : ∀ (H : ι → G₁) m, (List.map (fun p => p.2 • H p.1) (terms m)).sum =
      ∑ i, w i m • H i)
    (α : F) (A : Adversary F ι M G₁ G₂) (pk : G₂) (H : ι → G₁) :
    simulateQ (BLS.CoCDH.coinTableImpl H) (run terms α A pk) =
      fixedRun A pk H (realSign w α H) := by
  unfold run fixedRun
  apply simulateQ_StateT_compose
  intro q tr
  rcases q with (n | i) | m <;>
    simp only [handler, fixedImpl, StateT.run, StateT.mk, simulateQ_bind, simulateQ_spec_query,
      simulateQ_pure, signing, evalTerms_table, pure_bind, ht] <;> rfl

end Algebra

def admissibleForgery (admissible : M → List M → Prop) (fo : DynForgery F M ι) : Prop :=
  admissible fo.2.mstar (List.ofFn fo.2.v)

section Security

attribute [local instance] Classical.propDecidable

variable {Gₜ : Type}
  [Field F] [SampleableType F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

theorem experiment_table (terms : M → List (ι × F)) (w : ι → M → F)
    (ht : ∀ (H : ι → G₁) m, (List.map (fun p => p.2 • H p.1) (terms m)).sum =
      ∑ i, w i m • H i)
    (admissible : M → List M → Prop) (g₁ : G₁) (g₂ : G₂)
    (A : Adversary F ι M G₁ G₂) (H : ι → G₁) :
    simulateQ (BLS.CoCDH.coinTableImpl H) (experiment (Gₜ := Gₜ) terms admissible g₁ g₂ A) =
      (do
        let α ← ($ᵗ F : ProbComp F)
        let (out, tr) ← fixedRun A (α • g₂) H (realSign w α H)
        pure (decide (admissible out.mstar (tr.2.map Prod.fst) ∧
          pairing (F := F) (Gₜ := Gₜ) (materialize g₁ out tr) g₂ =
            pairing (F := F) (Gₜ := Gₜ) (∑ i, w i out.mstar • H i) (α • g₂) ∧
          out.mstar ∉ tr.2.map Prod.fst))) := by
  classical
  rw [experiment_eq]
  simp only [simulateQ_bind, simulateQ_pure, evalTerms_table, pure_bind, ht,
    run_table terms w ht]
  congr 1
  · simp [BLS.CoCDH.coinTableImpl, QueryImpl.simulateQ_add_liftM_left]
  · funext α
    apply bind_congr
    intro z
    apply congrArg (pure : Bool → ProbComp Bool)
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]

/-- Exact success-probability bridge. The full table is hidden in the proof-side simulator. -/
theorem advantage_eq_realGame (terms : M → List (ι × F)) (w : ι → M → F)
    (ht : ∀ (H : ι → G₁) m, (List.map (fun p => p.2 • H p.1) (terms m)).sum =
      ∑ i, w i m • H i)
    (admissible : M → List M → Prop) (g₁ : G₁) (g₂ : G₂)
    (A : Adversary F ι M G₁ G₂) :
    advantage (Gₜ := Gₜ) terms admissible g₁ g₂ A =
      Pr[fun x => admissibleForgery admissible x.1 ∧ dynForgerySucc (Gₜ := Gₜ) w g₁ g₂ x |
        realGameDynAdaptive (G₁ := G₁) w g₂ (extracted A)] := by
  classical
  have hd := BLS.CoCDH.evalSPMF_lazyCoin_eq_table
    (experiment (Gₜ := Gₜ) terms admissible g₁ g₂ A) ∅
  simp only [tableExtending_empty, experiment_table terms w ht] at hd
  change 𝒮[game (Gₜ := Gₜ) terms admissible g₁ g₂ A] = _ at hd
  rw [DeferredSampling.evalSPMF_bind_comm] at hd
  rw [advantage, evalDist_apply_singleton, probOutput_congr rfl hd,
    ← probEvent_true_eq_probOutput]
  unfold realGameDynAdaptive extracted
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
    probEvent_bind_eq_tsum]
  refine tsum_congr fun α => ?_
  congr 1
  refine tsum_congr fun H => ?_
  congr 1
  refine tsum_congr fun z => ?_
  by_cases hz : z ∈ support (fixedRun A (α • g₂) H (realSign w α H))
  · have hc := fixed_consistent H (realSign w α H) (A.main (α • g₂)) ([], [])
      (by simp [Consistent]) z hz
    congr 1
    simp only [probEvent_pure]
    apply if_congr _ rfl rfl
    simp only [decide_eq_true_eq, admissibleForgery, toForgery_messages, dynForgerySucc]
    rw [materialize_eq g₁ H (realSign w α H) z hc, ← toForgery_fresh]
    rfl
  · simp [probOutput_eq_zero_of_not_mem_support hz]

theorem goodReduction_eq (w : ι → M → F) (A : Adversary F ι M G₁ G₂) :
    goodReduction w A = adaptiveGoodDlogReduction w (extracted A) := by
  funext g₁ X₁ g₂ X₂
  unfold goodReduction adaptiveGoodDlogReduction extracted
  apply bind_congr
  intro ρ
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  apply bind_congr
  intro z
  simp only [dynReprA, reprA, toForgery, muW, List.mapIdx_eq_ofFn, List.sum_ofFn]
  congr 2

theorem badReduction_eq (w : ι → M → F) (A : Adversary F ι M G₁ G₂) :
    badReduction w A = adaptiveBadDlogReduction w (extracted A) := by
  funext g₁ X₁ g₂ X₂
  unfold badReduction adaptiveBadDlogReduction extracted
  apply bind_congr
  intro κ
  apply bind_congr
  intro a
  apply bind_congr
  intro b
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  apply bind_congr
  intro z
  simp only [dynDenomMask, dynDenomSlope, dynDenomCoeff, Lcoeff, toForgery,
    denominatorCoeff, List.mapIdx_eq_ofFn, List.sum_ofFn]
  congr 2

theorem goodAdvantage_eq (w : ι → M → F) (g₁ : G₁) (g₂ : G₂)
    (A : Adversary F ι M G₁ G₂) :
    Model.dlog11Advantage g₁ g₂ (goodReduction w A) =
      Pr[= true | dlog11Exp g₁ g₂ (adaptiveGoodDlogReduction w (extracted A))] := by
  rw [Model.dlog11Advantage, goodReduction_eq, evalDist_apply_singleton]

theorem badAdvantage_eq (w : ι → M → F) (g₁ : G₁) (g₂ : G₂)
    (A : Adversary F ι M G₁ G₂) :
    Model.dlog11Advantage g₁ g₂ (badReduction w A) =
      Pr[= true | dlog11Exp g₁ g₂ (adaptiveBadDlogReduction w (extracted A))] := by
  rw [Model.dlog11Advantage, badReduction_eq, evalDist_apply_singleton]

/-- Lazy-ROM security, with explicit solvers and no assumed game-equivalence premise. -/
theorem security (terms : M → List (ι × F)) (w : ι → M → F)
    (ht : ∀ (H : ι → G₁) m, (List.map (fun p => p.2 • H p.1) (terms m)).sum =
      ∑ i, w i m • H i)
    (admissible : M → List M → Prop) (g₁ : G₁) (g₂ : G₂)
    (A : Adversary F ι M G₁ G₂) (jk : DynForgery F M ι → ι)
    (hgen : Function.Bijective (fun ρ : F => ρ • g₁))
    (hvand : ∀ fo, admissibleForgery admissible fo → fo.Fresh →
      dynDenomCoeff w fo (jk fo) ≠ 0)
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ))) :
    advantage (Gₜ := Gₜ) terms admissible g₁ g₂ A ≤
      Model.dlog11Advantage g₁ g₂ (goodReduction w A) +
      Model.dlog11Advantage g₁ g₂ (badReduction w A) + 1 / (Fintype.card F : ENNReal) := by
  rw [advantage_eq_realGame terms w ht, goodAdvantage_eq, badAdvantage_eq]
  exact functional_euf_cma_adaptive w g₁ g₂ (extracted A)
    (admissibleForgery admissible) jk hgen hvand hpair

end Security

end Model.LazyAGM.Proofs
