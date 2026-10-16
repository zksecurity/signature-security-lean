import Signatures.Proximity.Spec.LazyAGM
import Signatures.LinearFunctional.Proofs.LazyAGMFiniteLabels
import Signatures.LinearFunctional.Proofs.LazyAGMGameTransport

/-! Injective slot renaming preserves Proximity's source game and its separate
fresh-collision observer. Finite covers range over generated keys and all reply
paths; coordinates and coefficient lists are unchanged. -/

open OracleComp OracleSpec Model.LazyAGM Model.LazyAGM.WeightedTransport
open BLS.CoCDH.MessageTransport
open BLS.LazyAGM.MessageTransport (mapOutput)

namespace Proximity.LazyAGM.SlotTransport

variable {F S U G₁ G₂ Gₜ : Type} {ℓ : Nat}

def index (f : U → S) : Option (Fin ℓ) × U → Option (Fin ℓ) × S := Prod.map id f
def message (f : U → S) : (Fin ℓ → F) × U → (Fin ℓ → F) × S := Prod.map id f

theorem index_injective (f : U → S) (hf : Function.Injective f) :
    Function.Injective (index (ℓ := ℓ) f) := by
  intro a b h
  change (a.1, f a.2) = (b.1, f b.2) at h
  exact Prod.ext (Prod.mk.inj h).1 (hf (Prod.mk.inj h).2)

theorem message_injective (f : U → S) (hf : Function.Injective f) :
    Function.Injective (message (F := F) (ℓ := ℓ) f) := by
  intro a b h
  change (a.1, f a.2) = (b.1, f b.2) at h
  exact Prod.ext (Prod.mk.inj h).1 (hf (Prod.mk.inj h).2)

theorem terms_map [One F] (f : U → S) (m : (Fin ℓ → F) × U) :
    terms (message f m) = (terms m).map (Prod.map (index f) id) := by
  simp [terms, message, index, List.map_ofFn, Function.comp_def]

theorem collision_map [Semiring F] (f : U → S) (hf : Function.Injective f)
    (out : Output F ((Fin ℓ → F) × U)) (signed : List ((Fin ℓ → F) × U)) :
    Collision (mapOutput (message f) out) (signed.map (message f)) ↔ Collision out signed := by
  have hFresh : message f out.mstar ∉ signed.map (message f) ↔ out.mstar ∉ signed := by
    simp [List.mem_map, (message_injective f hf).eq_iff]
  simp only [Collision, mapOutput, hFresh]
  simp [message, List.mapIdx_eq_ofFn]

variable [Field F] [SampleableType F] [DecidableEq S] [DecidableEq U]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ]

theorem game_map (f : U → S) (hf : Function.Injective f) (g₁ : G₁) (g₂ : G₂)
    (A : Adversary F (Option (Fin ℓ) × U) ((Fin ℓ → F) × U) G₁ G₂) :
    Proximity.LazyAGM.game (Gₜ := Gₜ) g₁ g₂ (mapAdversary (index f) (message f) A) =
      Proximity.LazyAGM.game (Gₜ := Gₜ) g₁ g₂ A :=
  WeightedTransport.game_map (index f) (index_injective f hf)
    (message f) (message_injective f hf) terms terms (terms_map f)
    (fun _ _ => True) (fun _ _ => True) (by intros; rfl) g₁ g₂ A

omit [SampleableType G₁] [DecidableEq S] [DecidableEq U]
    [AddCommGroup Gₜ] [Module F Gₜ] [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ] in
theorem collisionExperiment_map (f : U → S) (hf : Function.Injective f) (g₂ : G₂)
    (A : Adversary F (Option (Fin ℓ) × U) ((Fin ℓ → F) × U) G₁ G₂) :
    collisionExperiment g₂ (mapAdversary (index f) (message f) A) =
      simulateQ (baseQueries (index f)) (collisionExperiment g₂ A) := by
  classical
  unfold collisionExperiment
  simp only [run_eq_private, privateRun_map (index f) (message f) terms terms (terms_map f),
    simulateQ_bind, simulateQ_pure, baseQueries_lift, bind_map_left]
  apply bind_congr
  intro kappa
  apply bind_congr
  rintro ⟨out, tr⟩
  simp only [Prod.map_apply]
  have htr : (mapTranscript (index f) (message f) tr).2.map Prod.fst =
      (tr.2.map Prod.fst).map (message f) := by
    simp [mapTranscript, List.map_map, Function.comp_def]
  simp only [htr, collision_map f hf]

omit [AddCommGroup Gₜ] [Module F Gₜ] [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ] in
theorem collisionGame_map (f : U → S) (hf : Function.Injective f) (g₂ : G₂)
    (A : Adversary F (Option (Fin ℓ) × U) ((Fin ℓ → F) × U) G₁ G₂) :
    collisionGame g₂ (mapAdversary (index f) (message f) A) = collisionGame g₂ A := by
  unfold collisionGame
  rw [collisionExperiment_map f hf]
  exact lazyRun_rename (index f) (index_injective f hf) _

omit [DecidableEq U] [AddCommGroup Gₜ] [Module F Gₜ]
    [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ] in
theorem collisionGame_congr_generated (g₂ : G₂)
    (A B : Adversary F (Option (Fin ℓ) × S) ((Fin ℓ → F) × S) G₁ G₂)
    (h : ∀ r : F, A.main (r • g₂) = B.main (r • g₂)) : collisionGame g₂ A = collisionGame g₂ B := by
  have he : collisionExperiment g₂ A = collisionExperiment g₂ B := by
    unfold collisionExperiment
    apply bind_congr
    intro r
    simp only [run, h r]
  unfold collisionGame
  rw [he]

omit [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [DecidableEq S] [DecidableEq U] [SampleableType G₁]
    [AddCommGroup Gₜ] [Module F Gₜ] [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ] in
theorem exists_restricted_publicKeys [Finite F] [Finite G₁] (g₂ : G₂)
    (A : Adversary F (Option (Fin ℓ) × S) ((Fin ℓ → F) × S) G₁ G₂) :
    ∃ cover : Finset S,
      ∃ restricted : Adversary F (Option (Fin ℓ) × {s // s ∈ cover})
        ((Fin ℓ → F) × {s // s ∈ cover}) G₁ G₂,
        ∀ r : F, (mapAdversary (index Subtype.val) (message Subtype.val) restricted).main (r • g₂) =
          A.main (r • g₂) := by
  classical
  obtain ⟨cover, hcover⟩ := exists_label_cover Prod.snd Prod.snd (fun r : F => A.main (r • g₂))
  have hLift : ∀ r : F, Liftable (index (ℓ := ℓ) (Subtype.val : {s // s ∈ cover} → S))
      (message (Subtype.val : {s // s ∈ cover} → S)) (A.main (r • g₂)) := by
    intro r
    apply LabelCovered.liftable Prod.snd Prod.snd cover _ _ ?_ ?_ _ (hcover r)
    · intro i hi
      exact ⟨(i.1, ⟨i.2, hi⟩), rfl⟩
    · intro m hm
      exact ⟨(m.1, ⟨m.2, hm⟩), rfl⟩
  refine ⟨cover, restrictPublicKeys _ _ A ((0 : F) • g₂) (hLift 0), fun r => ?_⟩
  exact restrictPublicKeys_map_at _ _ A _ (hLift 0) _ (hLift r)

end Proximity.LazyAGM.SlotTransport
