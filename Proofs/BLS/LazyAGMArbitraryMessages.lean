import Proofs.BLS.LazyAGMGameTransport
import Proofs.BLS.LazyAGMSecurity
import Proofs.BLS.LazyAGMList

/-! BLS AGM security over arbitrary message types. The finite proof cover ranges
over generated keys and all adaptive reply paths. Exact transport returns the
original game and both lazy solvers, without executing or charging that cover. -/

open BilinearGroup

open OracleComp OracleSpec Model.LazyAGM AlgebraicGroupModel
open BLS.LazyAGM.Reduction

namespace BLS.LazyAGM.MessageTransport

variable {F M G₁ G₂ Gₜ : Type} [Field F] [SampleableType F] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁]

theorem goodReduction_congr_at (g X : G₁) (g₂ pk : G₂)
    (A B : Adversary F M M G₁ G₂) (h : A.main pk = B.main pk) :
    goodReductionLazy A g X g₂ pk = goodReductionLazy B g X g₂ pk := by
  simp only [goodReductionLazy, goodProgram, privateRun, h]

variable [AddCommGroup G₂] [Module F G₂]

theorem badReduction_congr_generated (g X : G₁) (g₂ pk : G₂)
    (A B : Adversary F M M G₁ G₂) (h : ∀ r : F, A.main (r • g₂) = B.main (r • g₂)) :
    badReductionLazy A g X g₂ pk = badReductionLazy B g X g₂ pk := by
  unfold badReductionLazy
  apply bind_congr
  intro kappa
  simp only [badProgram, privateRun, h kappa]

theorem goodExp_congr_generated (g : G₁) (g₂ : G₂)
    (A B : Adversary F M M G₁ G₂) (h : ∀ r : F, A.main (r • g₂) = B.main (r • g₂)) :
    dlog11Exp g g₂ (goodReductionLazy A) = dlog11Exp g g₂ (goodReductionLazy B) := by
  unfold dlog11Exp
  apply bind_congr
  intro r
  rw [goodReduction_congr_at g (r • g) g₂ (r • g₂) A B (h r)]

theorem badExp_congr_generated (g : G₁) (g₂ : G₂)
    (A B : Adversary F M M G₁ G₂) (h : ∀ r : F, A.main (r • g₂) = B.main (r • g₂)) :
    dlog11Exp g g₂ (badReductionLazy A) = dlog11Exp g g₂ (badReductionLazy B) := by
  unfold dlog11Exp
  apply bind_congr
  intro r
  rw [badReduction_congr_generated g (r • g) g₂ (r • g₂) A B h]

variable [SampleableType G₁] [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]

theorem game_congr_generated (g : G₁) (g₂ : G₂)
    (A B : Adversary F M M G₁ G₂) (h : ∀ r : F, A.main (r • g₂) = B.main (r • g₂)) :
    BLS.LazyAGM.game (Gₜ := Gₜ) g g₂ A = BLS.LazyAGM.game (Gₜ := Gₜ) g g₂ B := by
  have he : experiment (Gₜ := Gₜ) BLS.LazyAGM.terms (fun _ _ => True) g g₂ A =
      experiment (Gₜ := Gₜ) BLS.LazyAGM.terms (fun _ _ => True) g g₂ B := by
    rw [experiment_eq, experiment_eq]
    apply bind_congr
    intro r
    simp only [run, h r]
  unfold BLS.LazyAGM.game Model.LazyAGM.game
  rw [he]

end BLS.LazyAGM.MessageTransport

namespace BLS.LazyAGM.Reduction

open BLS.LazyAGM.MessageTransport

variable {F M G₁ G₂ Gₜ : Type}
  [Field F] [SampleableType F] [Fintype F] [DecidableEq F] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

theorem security_arbitrary_messages (g : G₁) (g₂ : G₂) (A : Adversary F M M G₁ G₂)
    (hgen : Function.Bijective (fun rho : F => rho • g))
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g g₂ : Gₜ))) :
    𝒟[BLS.LazyAGM.game (Gₜ := Gₜ) g g₂ A] {true} ≤
      Model.dlog11Advantage g g₂ (goodReductionLazy A) +
      Model.dlog11Advantage g g₂ (badReductionLazy A) +
      1 / (Fintype.card F : ENNReal) := by
  classical
  obtain ⟨cover, restricted, heq⟩ := exists_restricted_publicKeys (fun r : F => r • g₂) A
  let mapped := mapAdversary Subtype.val restricted
  have hkey : ∀ r : F, A.main (r • g₂) = mapped.main (r • g₂) := fun r => (heq r).symm
  have hsource := (game_congr_generated (Gₜ := Gₜ) g g₂ A mapped hkey).trans
    (game_map (Gₜ := Gₜ) Subtype.val Subtype.val_injective g g₂ restricted)
  have hgood := goodExp_congr_generated g g₂ A mapped hkey
  have hbad := badExp_congr_generated g g₂ A mapped hkey
  dsimp only [mapped] at hgood hbad
  rw [goodReduction_map Subtype.val Subtype.val_injective] at hgood
  rw [badReduction_map Subtype.val Subtype.val_injective] at hbad
  rw [hsource, Model.dlog11Advantage, Model.dlog11Advantage, hgood, hbad]
  exact security_finite_messages g g₂ restricted hgen hpair

/-- The same arbitrary-message bound for the concrete finite-list cache
representation. Its full runtime/code budget remains a separate obligation. -/
theorem security_arbitrary_messages_list (g : G₁) (g₂ : G₂) (A : Adversary F M M G₁ G₂)
    (hgen : Function.Bijective (fun rho : F => rho • g))
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g g₂ : Gₜ))) :
    𝒟[BLS.LazyAGM.game (Gₜ := Gₜ) g g₂ A] {true} ≤
      Model.dlog11Advantage g g₂ (goodReductionList A) +
      Model.dlog11Advantage g g₂ (badReductionList A) +
      1 / (Fintype.card F : ENNReal) := by
  rw [goodReductionList_eq, badReductionList_eq]
  exact security_arbitrary_messages g g₂ A hgen hpair

end BLS.LazyAGM.Reduction
