import Signatures.BLS.Proofs.LazyAGMTransport

/-! Injective message renaming preserves the actual BLS AGM source game,
including the certified interaction adapter, final hash, and freshness test. -/

open BilinearGroup

open OracleComp OracleSpec Model.LazyAGM BLS.LazyAGM.Reduction AlgebraicGroupModel
open BLS.CoCDH.MessageTransport

namespace BLS.LazyAGM.MessageTransport

variable {F N M G₁ G₂ Gₜ : Type}

theorem materialize_map [Zero F] [AddCommMonoid G₁] [SMul F G₁]
    (f : N → M) (g : G₁) (out : Output F N) (tr : Transcript N N G₁) :
    materialize g (mapOutput f out) (mapTranscript f tr) = materialize g out tr := by
  simp [materialize_eq_weightedReplies, mapOutput, mapTranscript, weightedReplies,
    List.mapIdx_eq_ofFn]

theorem fresh_map (f : N → M) (hf : Function.Injective f) (m : N) (tr : Transcript N N G₁) :
    f m ∉ (mapTranscript f tr).2.map Prod.fst ↔ m ∉ tr.2.map Prod.fst := by
  simp [mapTranscript, List.mem_map, hf.eq_iff]

variable [Field F] [AddCommGroup G₁] [Module F G₁]

theorem run_eq_private (kappa : F) (A : Adversary F M M G₁ G₂) (pk : G₂) :
    run BLS.LazyAGM.terms kappa A pk = privateRun id (fun r => kappa • r) A pk := by
  unfold run privateRun
  congr 2
  funext q tr
  rcases q with ((n | m) | m) <;>
    simp [privateOracle, handler, signing, BLS.LazyAGM.terms, evalTerms]

variable [SampleableType F] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]

theorem experiment_map (f : N → M) (hf : Function.Injective f)
    (g : G₁) (g₂ : G₂) (A : Adversary F N N G₁ G₂) :
    experiment (Gₜ := Gₜ) BLS.LazyAGM.terms (fun _ _ => True) g g₂ (mapAdversary f A) =
      simulateQ (baseQueries f)
        (experiment (Gₜ := Gₜ) BLS.LazyAGM.terms (fun _ _ => True) g g₂ A) := by
  classical
  rw [experiment_eq, experiment_eq]
  simp only [run_eq_private, privateRun_map, simulateQ_bind, baseQueries_lift, bind_map_left]
  apply bind_congr
  intro kappa
  apply bind_congr
  rintro ⟨out, tr⟩
  simp only [Prod.map_apply, materialize_map]
  simp [mapOutput, BLS.LazyAGM.terms, evalTerms, baseQueries,
    mapTranscript, List.mem_map, hf.eq_iff]

variable [SampleableType G₁] [DecidableEq N] [DecidableEq M]

theorem game_map (f : N → M) (hf : Function.Injective f)
    (g : G₁) (g₂ : G₂) (A : Adversary F N N G₁ G₂) :
    BLS.LazyAGM.game (Gₜ := Gₜ) g g₂ (mapAdversary f A) =
      BLS.LazyAGM.game (Gₜ := Gₜ) g g₂ A := by
  unfold BLS.LazyAGM.game Model.LazyAGM.game
  rw [experiment_map f hf]
  exact lazyRun_rename f hf _

end BLS.LazyAGM.MessageTransport
