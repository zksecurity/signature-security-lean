import Signatures.BLS.CoCDH.Proofs.FiniteMessages
import Signatures.BLS.CoCDH.Proofs.LazyGame
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-! Injective message renaming preserves adaptive BLS interactions, signing
counts, and lazy state. These are exact computation laws, with no enumeration
or cardinality bound on the message domains. -/

open OracleComp OracleSpec

namespace BLS.CoCDH.Tight

variable {N M G₁ : Type}

theorem mapMessages_signing_bound (f : N → M) (adv : TightAdv N G₁) (qS : Nat) :
    IsQueryBoundP (mapMessages f adv) (fun i => Sum.isRight i = true) qS ↔
      IsQueryBoundP adv (fun i => Sum.isRight i = true) qS := by
  induction adv using OracleComp.inductionOn generalizing qS with
  | pure out => simp [mapMessages]
  | query_bind q next ih =>
      change IsQueryBoundP
        (mapMessages f (show OracleComp (advSpec N G₁) (N × G₁) from query q >>= next)) _ _ ↔ _
      rw [mapMessages_query_bind]
      rcases q with ((n | m) | m) <;>
        simp [messageQueries, isQueryBoundP_query_bind_iff, ih]

theorem mapMessages_cacheForgery (f : N → M) (adv : TightAdv N G₁) :
    mapMessages f (cacheForgery adv) = cacheForgery (mapMessages f adv) := by
  simp [mapMessages, cacheForgery, simulateQ_bind, messageQueries,
    map_bind, bind_map_left, bind_pure_comp]

/-- A state projection commuting with each renamed query also commutes with
arbitrary adaptive execution. The output here still uses the original labels. -/
theorem run_messageQueries_project {S T A : Type}
    (f : N → M) (large : QueryImpl (advSpec M G₁) (StateT S ProbComp))
    (small : QueryImpl (advSpec N G₁) (StateT T ProbComp)) (proj : S → T)
    (step : ∀ q s, Prod.map id proj <$>
      (simulateQ large (messageQueries f q)).run s = (small q).run (proj s))
    (oa : OracleComp (advSpec N G₁) A) (s : S) :
    Prod.map id proj <$> (simulateQ large (simulateQ (messageQueries f) oa)).run s =
      (simulateQ small oa).run (proj s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [← step q s, bind_map_left]
      exact bind_congr fun p => ih p.1 p.2

section State

variable {F : Type} (f : N → M) (hf : Function.Injective f)

noncomputable def projectState (st : (M → Option F) × Finset M) : (N → Option F) × Finset N :=
  (st.1 ∘ f, st.2.preimage f hf.injOn)

@[simp] theorem projectState_empty :
    projectState (F := F) f hf ((fun _ => none), ∅) = ((fun _ => none), ∅) := by
  simp [projectState, Function.comp_def]

@[simp] theorem mem_projectState (st : (M → Option F) × Finset M) (n : N) :
    n ∈ (projectState f hf st).2 ↔ f n ∈ st.2 := by
  simp [projectState]

variable [DecidableEq N] [DecidableEq M]

theorem projectState_insert (st : (M → Option F) × Finset M) (n : N) :
    projectState f hf (st.1, insert (f n) st.2) =
      ((projectState f hf st).1, insert n (projectState f hf st).2) := by
  apply Prod.ext
  · rfl
  · ext k
    simp [projectState, hf.eq_iff]

theorem projectState_update (st : (M → Option F) × Finset M) (n : N) (x : Option F) :
    projectState f hf (Function.update st.1 (f n) x, st.2) =
      (Function.update (projectState f hf st).1 n x, (projectState f hf st).2) := by
  exact Prod.ext (Function.update_comp_eq_of_injective st.1 hf n x) rfl

variable [SampleableType F]

theorem getDlogS_project (n : N) (st : (M → Option F) × Finset M) :
    Prod.map id (projectState f hf) <$> (getDlogS (F := F) (f n)).run st =
      (getDlogS (F := F) n).run (projectState f hf st) := by
  rw [getDlogS_run, getDlogS_run]
  change Prod.map id (projectState f hf) <$> (match st.1 (f n) with
    | some rho => pure (rho, st)
    | none => ($ᵗ F) >>= fun rho => pure (rho, (Function.update st.1 (f n) (some rho), st.2))) = _
  cases h : st.1 (f n) <;>
    simp [projectState, h, Function.update_comp_eq_of_injective _ hf]

variable [SMul F G₁]

theorem realOracle_project (g X : G₁) (q : (advSpec N G₁).Domain)
    (st : (M → Option F) × Finset M) :
    Prod.map id (projectState f hf) <$>
      (simulateQ (realOracle (F := F) g X) (messageQueries f q)).run st =
      (realOracle (F := F) g X q).run (projectState f hf st) := by
  rcases q with ((n | m) | m)
  · simp [messageQueries, realOracle, Functor.map_map]
  · simp only [messageQueries, simulateQ_HasQuery_query, realOracle, StateT.run_bind,
      StateT.run_pure, map_bind]
    rw [← getDlogS_project f hf m st, bind_map_left]
    simp
  · simp only [messageQueries, simulateQ_HasQuery_query, realOracle, StateT.run_bind,
      StateT.run_modify, StateT.run_pure, pure_bind, map_bind]
    rw [← projectState_insert f hf st m, ← getDlogS_project f hf m (st.1, insert (f m) st.2),
      bind_map_left]
    simp

end State

section Games

open AlgebraicGroupModel

variable {F G₂ Gₜ : Type} [Field F] [SampleableType F]
  [DecidableEq N] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]

theorem blsEufTightPK_mapMessages (f : N → M) (hf : Function.Injective f)
    (g : G₁) (g₂ : G₂) (adv : TightAdvPK N G₁ G₂) :
    blsEufTightPK (F := F) (Gₜ := Gₜ) g g₂ (fun pk => mapMessages f (adv pk)) =
      blsEufTightPK (F := F) (Gₜ := Gₜ) g g₂ adv := by
  classical
  unfold blsEufTightPK
  apply bind_congr
  intro x
  have hs := run_messageQueries_project f (realOracle (F := F) g (x • g))
    (realOracle (F := F) g (x • g)) (projectState f hf)
    (realOracle_project f hf g (x • g)) (adv (x • g₂)) ((fun _ => none), ∅)
  rw [projectState_empty] at hs
  simp only [mapMessages, simulateQ_map, StateT.run_map, bind_map_left]
  rw [← hs, bind_map_left]
  apply bind_congr
  intro p
  simp [projectState, Function.comp_def]

theorem blsEufLazyPK_mapMessages (f : N → M) (hf : Function.Injective f)
    (g : G₁) (g₂ : G₂) (adv : TightAdvPK N G₁ G₂) :
    blsEufLazyPK (F := F) (Gₜ := Gₜ) g g₂ (fun pk => mapMessages f (adv pk)) =
      blsEufLazyPK (F := F) (Gₜ := Gₜ) g g₂ adv := by
  unfold blsEufLazyPK cacheForgeryPK
  simp_rw [← mapMessages_cacheForgery]
  exact blsEufTightPK_mapMessages f hf g g₂ (fun pk => cacheForgery (adv pk))

end Games

end BLS.CoCDH.Tight
