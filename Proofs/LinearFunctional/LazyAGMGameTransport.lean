import Proofs.LinearFunctional.LazyAGMTransport

/-! Renaming preserves the actual weighted source game, including certified
interaction, target evaluation, freshness, and any transported admissibility
predicate. Equality only at generated keys is enough for the game and solvers. -/

open BilinearGroup

open OracleComp OracleSpec Model.LazyAGM Model.LazyAGM.WeightedReduction AlgebraicGroupModel
open BLS.CoCDH.MessageTransport
open BLS.LazyAGM.MessageTransport (mapOutput evalTerms_map)

namespace Model.LazyAGM.WeightedTransport

variable {F ι κ M N G₁ G₂ Gₜ : Type}

theorem materialize_map [Zero F] [AddCommMonoid G₁] [SMul F G₁]
    (index : κ → ι) (message : N → M) (g : G₁) (out : Output F N) (tr : Transcript κ N G₁) :
    materialize g (mapOutput message out) (mapTranscript index message tr) = materialize g out tr := by
  simp [materialize_eq_weightedReplies, mapOutput, mapTranscript, weightedReplies, List.mapIdx_eq_ofFn]

theorem fresh_map (index : κ → ι) (message : N → M) (hm : Function.Injective message)
    (m : N) (tr : Transcript κ N G₁) :
    message m ∉ (mapTranscript index message tr).2.map Prod.fst ↔ m ∉ tr.2.map Prod.fst := by
  simp [mapTranscript, List.mem_map, hm.eq_iff]

variable [Field F] [AddCommGroup G₁] [Module F G₁]

theorem run_eq_private (terms : M → List (ι × F)) (kappa : F)
    (A : Adversary F ι M G₁ G₂) (pk : G₂) :
    run terms kappa A pk = privateRun terms id (fun r => kappa • r) A pk := by
  unfold run privateRun
  congr 2
  funext q tr
  rcases q with ((n | i) | m) <;> simp [privateOracle, handler, signing]

variable [SampleableType F] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]

theorem experiment_map (index : κ → ι) (message : N → M) (hm : Function.Injective message)
    (terms : M → List (ι × F)) (smallTerms : N → List (κ × F))
    (ht : ∀ m, terms (message m) = (smallTerms m).map (Prod.map index id))
    (admissible : M → List M → Prop) (smallAdmissible : N → List N → Prop)
    (ha : ∀ m signed, admissible (message m) (signed.map message) ↔ smallAdmissible m signed)
    (g : G₁) (g₂ : G₂) (A : Adversary F κ N G₁ G₂) :
    experiment (Gₜ := Gₜ) terms admissible g g₂ (mapAdversary index message A) =
      simulateQ (baseQueries index) (experiment (Gₜ := Gₜ) smallTerms smallAdmissible g g₂ A) := by
  classical
  rw [experiment_eq, experiment_eq]
  simp only [run_eq_private, privateRun_map index message terms smallTerms ht,
    simulateQ_bind, baseQueries_lift, bind_map_left]
  apply bind_congr
  intro kappa
  apply bind_congr
  rintro ⟨out, tr⟩
  simp only [Prod.map_apply, materialize_map]
  have ha' := ha out.mstar (tr.2.map Prod.fst)
  simp only [List.map_map, Function.comp_def] at ha'
  simp [mapOutput, ht, evalTerms_map, mapTranscript, List.map_map, Function.comp_def,
    List.mem_map, hm.eq_iff, ha']

variable [SampleableType G₁] [DecidableEq κ] [DecidableEq ι]

theorem game_map (index : κ → ι) (hi : Function.Injective index)
    (message : N → M) (hm : Function.Injective message)
    (terms : M → List (ι × F)) (smallTerms : N → List (κ × F))
    (ht : ∀ m, terms (message m) = (smallTerms m).map (Prod.map index id))
    (admissible : M → List M → Prop) (smallAdmissible : N → List N → Prop)
    (ha : ∀ m signed, admissible (message m) (signed.map message) ↔ smallAdmissible m signed)
    (g : G₁) (g₂ : G₂) (A : Adversary F κ N G₁ G₂) :
    Model.LazyAGM.game (Gₜ := Gₜ) terms admissible g g₂ (mapAdversary index message A) =
      Model.LazyAGM.game (Gₜ := Gₜ) smallTerms smallAdmissible g g₂ A := by
  unfold Model.LazyAGM.game
  rw [experiment_map index message hm terms smallTerms ht admissible smallAdmissible ha]
  exact lazyRun_rename index hi _

omit [SampleableType G₁] [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq κ] in
theorem goodExp_congr_generated (terms : M → List (ι × F)) (g : G₁) (g₂ : G₂)
    (A B : Adversary F ι M G₁ G₂) (h : ∀ r : F, A.main (r • g₂) = B.main (r • g₂)) :
    dlog11Exp g g₂ (goodReductionList terms A) = dlog11Exp g g₂ (goodReductionList terms B) := by
  unfold dlog11Exp
  apply bind_congr
  intro r
  simp only [goodReductionList, goodProgram, privateRun, h r]

omit [SampleableType G₁] [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq κ] in
theorem badExp_congr_generated (terms : M → List (ι × F)) (g : G₁) (g₂ : G₂)
    (A B : Adversary F ι M G₁ G₂) (h : ∀ r : F, A.main (r • g₂) = B.main (r • g₂)) :
    dlog11Exp g g₂ (badReductionList terms A) = dlog11Exp g g₂ (badReductionList terms B) := by
  unfold dlog11Exp
  apply bind_congr
  intro r
  unfold badReductionList
  congr 1
  apply bind_congr
  intro kappa
  simp only [badProgram, privateRun, h kappa]

omit [DecidableEq κ] in
theorem game_congr_generated (terms : M → List (ι × F)) (admissible : M → List M → Prop)
    (g : G₁) (g₂ : G₂) (A B : Adversary F ι M G₁ G₂)
    (h : ∀ r : F, A.main (r • g₂) = B.main (r • g₂)) :
    Model.LazyAGM.game (Gₜ := Gₜ) terms admissible g g₂ A =
      Model.LazyAGM.game (Gₜ := Gₜ) terms admissible g g₂ B := by
  have he : experiment (Gₜ := Gₜ) terms admissible g g₂ A =
      experiment (Gₜ := Gₜ) terms admissible g g₂ B := by
    rw [experiment_eq, experiment_eq]
    apply bind_congr
    intro r
    simp only [run, h r]
  unfold Model.LazyAGM.game
  rw [he]

end Model.LazyAGM.WeightedTransport
