import Signatures.Proximity.Spec.LazyAGM
import Signatures.Proximity.Proofs.Adaptive
import Signatures.LinearFunctional.Proofs.LazyAGM

open BilinearGroup

open OracleComp AlgebraicGroupModel AlgebraicGroupModel.LinFunctional
open Model.LazyAGM Model.LazyAGM.Proofs

namespace Proximity.LazyAGM.Proofs

attribute [local instance] Classical.propDecidable

variable {F S G₁ G₂ Gₜ : Type} {ℓ : Nat}
  [Field F] [SampleableType F] [Fintype F] [DecidableEq F] [Fintype S] [DecidableEq S]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

theorem terms_eq (H : Option (Fin ℓ) × S → G₁) (ms : (Fin ℓ → F) × S) :
    (List.map (fun p => p.2 • H p.1) (terms ms)).sum =
      ∑ i, Proximity.Proofs.coordinateWeight ℓ i ms • H i := by
  simp [terms, Proximity.Proofs.coordinateWeight, List.sum_ofFn,
    Fintype.sum_prod_type, Fintype.sum_option]

/-- The collision observer runs the same certified adversary as the source game's experiment. -/
theorem collisionExperiment_eq_interactive (g₁ : G₁) (g₂ : G₂)
    (A : Adversary F (Option (Fin ℓ) × S) ((Fin ℓ → F) × S) G₁ G₂) :
    collisionExperiment g₂ A = (do
      let α ← (liftM ($ᵗ F) : OracleComp (baseSpec (Option (Fin ℓ) × S) G₁) F)
      let result ← interactiveRun terms α A g₁ (α • g₂)
      match result.data with
      | some (out, signed) => pure (decide (Collision out signed))
      | none => pure false) := by
  simp only [collisionExperiment, interactiveRun_eq, bind_map_left, Interactive.observe]

theorem collision_toForgery
    (z : Output F ((Fin ℓ → F) × S) × Transcript (Option (Fin ℓ) × S) ((Fin ℓ → F) × S) G₁) :
    Collision z.1 (z.2.2.map Prod.fst) ↔
      (toForgery z).Fresh ∧ ¬ Proximity.Proofs.Noncollision (toForgery z) := by
  rw [toForgery_fresh]
  simp [Collision, Proximity.Proofs.Noncollision, toForgery,
    List.mapIdx_eq_ofFn, List.sum_ofFn]
  intro _
  rfl

theorem collisionExperiment_table (g₂ : G₂)
    (A : Adversary F (Option (Fin ℓ) × S) ((Fin ℓ → F) × S) G₁ G₂)
    (H : Option (Fin ℓ) × S → G₁) :
    simulateQ (BLS.CoCDH.coinTableImpl H) (collisionExperiment g₂ A) = (do
      let α ← ($ᵗ F : ProbComp F)
      let (out, tr) ← fixedRun A (α • g₂) H (realSign (Proximity.Proofs.coordinateWeight ℓ) α H)
      pure (decide (Collision out (tr.2.map Prod.fst)))) := by
  classical
  simp only [collisionExperiment, simulateQ_bind, simulateQ_pure,
    run_table terms (Proximity.Proofs.coordinateWeight ℓ) terms_eq]
  congr 1
  simp [BLS.CoCDH.coinTableImpl, QueryImpl.simulateQ_add_liftM_left]

/-- Exact collision probability in the original lazy execution, not a worst-case reply-path bound. -/
theorem collision_eq_realGame (g₂ : G₂)
    (A : Adversary F (Option (Fin ℓ) × S) ((Fin ℓ → F) × S) G₁ G₂) :
    𝒟[collisionGame g₂ A] {true} =
      Pr[fun x => x.1.Fresh ∧ ¬ Proximity.Proofs.Noncollision x.1 |
        realGameDynAdaptive (Proximity.Proofs.coordinateWeight ℓ) g₂ (extracted A)] := by
  classical
  have hd := BLS.CoCDH.evalSPMF_lazyCoin_eq_table (collisionExperiment g₂ A) ∅
  simp only [tableExtending_empty, collisionExperiment_table] at hd
  change 𝒮[collisionGame g₂ A] = _ at hd
  rw [DeferredSampling.evalSPMF_bind_comm] at hd
  rw [evalDist_apply_singleton, probOutput_congr rfl hd, ← probEvent_true_eq_probOutput]
  unfold realGameDynAdaptive extracted
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
    probEvent_bind_eq_tsum]
  refine tsum_congr fun α => ?_
  congr 1
  refine tsum_congr fun H => ?_
  congr 1
  refine tsum_congr fun z => ?_
  simp only [probEvent_pure, decide_eq_true_eq, collision_toForgery]

theorem security (g₁ : G₁) (g₂ : G₂)
    (A : Adversary F (Option (Fin ℓ) × S) ((Fin ℓ → F) × S) G₁ G₂)
    (hgen : Function.Bijective (fun ρ : F => ρ • g₁))
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ))) :
    𝒟[Proximity.LazyAGM.game (Gₜ := Gₜ) g₁ g₂ A] {true} ≤
      Model.dlog11Advantage g₁ g₂ (goodReduction (Proximity.Proofs.coordinateWeight ℓ) A) +
      Model.dlog11Advantage g₁ g₂ (badReduction (Proximity.Proofs.coordinateWeight ℓ) A) +
      1 / (Fintype.card F : ENNReal) + 𝒟[collisionGame g₂ A] {true} := by
  change advantage (Gₜ := Gₜ) terms (fun _ _ => True) g₁ g₂ A ≤ _
  rw [advantage_eq_realGame terms (Proximity.Proofs.coordinateWeight ℓ) terms_eq,
    goodAdvantage_eq, badAdvantage_eq, collision_eq_realGame]
  simp only [admissibleForgery, true_and]
  exact Proximity.Proofs.adaptive_security g₁ g₂ (extracted A) hgen hpair

end Proximity.LazyAGM.Proofs
