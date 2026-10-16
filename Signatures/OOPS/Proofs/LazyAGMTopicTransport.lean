import Signatures.OOPS.Spec.LazyAGM
import Signatures.LinearFunctional.Proofs.LazyAGMFiniteLabels
import Signatures.LinearFunctional.Proofs.LazyAGMGameTransport

/-! A topic embedding preserves the degree-indexed OOPS bases, signed scalar
messages, distinct-message admissibility, and actual source game. A finite
proof cover is chosen only over generated verification keys. -/

open OracleComp OracleSpec Model.LazyAGM Model.LazyAGM.WeightedTransport

namespace OOPS.LazyAGM.TopicTransport

variable {F T U G₁ G₂ Gₜ : Type} {d : Nat}

def index (f : U → T) : U × Fin (d + 1) → T × Fin (d + 1) := Prod.map f id
def message (f : U → T) : F × U → F × T := Prod.map id f

theorem index_injective (f : U → T) (hf : Function.Injective f) :
    Function.Injective (index (d := d) f) := by
  intro a b h
  change (f a.1, a.2) = (f b.1, b.2) at h
  exact Prod.ext (hf (Prod.mk.inj h).1) (Prod.mk.inj h).2

theorem message_injective (f : U → T) (hf : Function.Injective f) :
    Function.Injective (message (F := F) f) := by
  intro a b h
  change (a.1, f a.2) = (b.1, f b.2) at h
  exact Prod.ext (Prod.mk.inj h).1 (hf (Prod.mk.inj h).2)

theorem terms_map [Monoid F] (f : U → T) (m : F × U) :
    terms d (message f m) = (terms d m).map (Prod.map (index f) id) := by
  simp [terms, message, index, List.map_ofFn, Function.comp_def]

theorem admissible_map [DecidableEq F] [DecidableEq T] [DecidableEq U]
    (f : U → T) (hf : Function.Injective f) (m : F × U) (signed : List (F × U)) :
    admissible d (message f m) (signed.map (message f)) ↔ admissible d m signed := by
  simp [admissible, message, List.filter_map, List.map_map, Function.comp_def, hf.eq_iff]

variable [Field F] [SampleableType F] [DecidableEq F] [DecidableEq T] [DecidableEq U]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ]

theorem game_map (f : U → T) (hf : Function.Injective f) (g₁ : G₁) (g₂ : G₂)
    (A : Adversary F (U × Fin (d + 1)) (F × U) G₁ G₂) :
    OOPS.LazyAGM.game (Gₜ := Gₜ) g₁ g₂ d (mapAdversary (index f) (message f) A) =
      OOPS.LazyAGM.game (Gₜ := Gₜ) g₁ g₂ d A := by
  rw [game_eq_of_decidableEq, game_eq_of_decidableEq]
  exact WeightedTransport.game_map (index f) (index_injective f hf)
    (message f) (message_injective f hf) (terms d) (terms d) (terms_map f)
    (admissible d) (admissible d) (admissible_map f hf) g₁ g₂ A

omit [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [DecidableEq F] [DecidableEq T] [DecidableEq U] [SampleableType G₁]
    [AddCommGroup Gₜ] [Module F Gₜ] [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ] in
theorem exists_restricted_publicKeys [Finite F] [Finite G₁] (g₂ : G₂) (d : Nat)
    (A : Adversary F (T × Fin (d + 1)) (F × T) G₁ G₂) :
    ∃ cover : Finset T,
      ∃ restricted : Adversary F ({t // t ∈ cover} × Fin (d + 1)) (F × {t // t ∈ cover}) G₁ G₂,
        ∀ r : F, (mapAdversary (index Subtype.val) (message Subtype.val) restricted).main (r • g₂) =
          A.main (r • g₂) := by
  classical
  obtain ⟨cover, hcover⟩ := exists_label_cover Prod.fst Prod.snd (fun r : F => A.main (r • g₂))
  have hLift : ∀ r : F, Liftable (index (d := d) (Subtype.val : {t // t ∈ cover} → T))
      (message (Subtype.val : {t // t ∈ cover} → T)) (A.main (r • g₂)) := by
    intro r
    apply LabelCovered.liftable Prod.fst Prod.snd cover _ _ ?_ ?_ _ (hcover r)
    · intro i hi
      exact ⟨(⟨i.1, hi⟩, i.2), rfl⟩
    · intro m hm
      exact ⟨(m.1, ⟨m.2, hm⟩), rfl⟩
  refine ⟨cover, restrictPublicKeys _ _ A ((0 : F) • g₂) (hLift 0), fun r => ?_⟩
  exact restrictPublicKeys_map_at _ _ A _ (hLift 0) _ (hLift r)

end OOPS.LazyAGM.TopicTransport
