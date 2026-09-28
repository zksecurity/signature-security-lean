import Signatures.OOPS.Spec.LazyAGM
import Signatures.LinearFunctional.Proofs.LazyAGM

/-! OOPS game comparison for the paper's fixed-degree signing-call convention, including repeats.
Compose callGame_le_game with the machine-bounded OOPS statement for a security bound. -/

open OracleComp AlgebraicGroupModel
open scoped ENNReal

namespace OOPS.LazyAGM

/-- Fixed-degree specialization of the paper's target-topic signing-call limit. -/
def callAdmissible {F T : Type} [DecidableEq T]
    (d : Nat) (mt : F × T) (signed : List (F × T)) : Prop :=
  (signed.filter fun q => q.2 = mt.2).length ≤ d

theorem callAdmissible_implies_admissible {F T : Type} [DecidableEq F] [DecidableEq T]
    (d : Nat) (mt : F × T) (signed : List (F × T))
    (h : callAdmissible d mt signed) : admissible d mt signed := by
  exact (List.toFinset_card_le _).trans (by simpa [callAdmissible] using h)

noncomputable def callGame {F T G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [DecidableEq T]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [BilinearPairing F G₁ G₂ Gₜ]
    (g₁ : G₁) (g₂ : G₂) (d : Nat)
    (A : Model.LazyAGM.Adversary F (T × Fin (d + 1)) (F × T) G₁ G₂) : ProbComp Bool :=
  Model.LazyAGM.game (Gₜ := Gₜ) (terms d) (callAdmissible d) g₁ g₂ A

theorem callGame_le_game {F T G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [DecidableEq T]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [BilinearPairing F G₁ G₂ Gₜ]
    (g₁ : G₁) (g₂ : G₂) (d : Nat)
    (A : Model.LazyAGM.Adversary F (T × Fin (d + 1)) (F × T) G₁ G₂) :
    𝒟[callGame (Gₜ := Gₜ) g₁ g₂ d A] {true} ≤
      𝒟[game (Gₜ := Gₜ) g₁ g₂ d A] {true} := by
  classical
  simp only [callGame, game, Model.LazyAGM.game, Model.LazyAGM.experiment_eq,
    simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind, StateT.run_pure,
    map_bind, map_pure]
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  rintro ⟨alpha, cache⟩ _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  rintro ⟨⟨out, tr⟩, cache⟩ _
  apply evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  rintro ⟨target, cache⟩ _
  by_cases h : callAdmissible d out.mstar (tr.2.map Prod.fst)
  · simp [h, callAdmissible_implies_admissible d _ _ h]
  · simp [h]

end OOPS.LazyAGM
