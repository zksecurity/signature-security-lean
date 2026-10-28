import Proofs.SynchronizedPS.WrappedBound
import Proofs.LinearFunctional.LazyAGMFiniteLabels

/-! Synchronized PS security for arbitrary period types. The attacker's proof view at the
generated keys touches finitely many periods, so it is the relabeling of a view over a finite
cover; the lazy game and the four wrapped solvers are invariant under injective period
relabelings and agree on views that agree at the generated keys. The finite presentation is
used only inside the proof. -/

open OracleComp OracleSpec Model Model.LazyAGM Model.LazyAGM.WeightedTransport Model.LazyAGM.WeightedReduction
open BLS.CoCDH.MessageTransport (baseQueries baseQueries_lift lazyRun_rename)
open SynchronizedPS.Proofs (View)

namespace SynchronizedPS.Transport

set_option linter.unusedSectionVars false

variable {F T U G₁ G₂ Gₜ : Type}

/-! ## Relabeling periods -/

def message (f : U → T) : U × F → T × F := Prod.map f id
@[simp] theorem message_fst (f : U → T) (m : U × F) : (message f m).1 = f m.1 := rfl
@[simp] theorem message_snd (f : U → T) (m : U × F) : (message f m).2 = m.2 := rfl
def forgery (f : U → T) : Forgery F U → Forgery F T := Prod.map (message f) id
def mapOut (f : U → T) (out : Output F (Forgery F U)) : Output F (Forgery F T) :=
  ⟨forgery f out.mstar, out.β, out.γ, out.ξ⟩
def mapMain (f : U → T) (oa : OracleComp (advSpec U (U × F) G₁) (Output F (Forgery F U))) :
    OracleComp (advSpec T (T × F) G₁) (Output F (Forgery F T)) :=
  mapOut f <$> simulateQ (queries f (message f)) oa
/-- A view over the relabeled periods. -/
def mapView (f : U → T) (V : View F U G₁ G₂) : View F T G₁ G₂ := ⟨fun pk => mapMain f (V.main pk)⟩

theorem message_injective (f : U → T) (hf : Function.Injective f) : Function.Injective (message (F := F) f) := by
  intro a b h
  change (f a.1, a.2) = (f b.1, b.2) at h
  exact Prod.ext (hf (Prod.mk.inj h).1) (Prod.mk.inj h).2

theorem mapMain_query_bind (f : U → T) (q : (advSpec U (U × F) G₁).Domain)
    (next : (advSpec U (U × F) G₁).Range q → OracleComp (advSpec U (U × F) G₁) (Output F (Forgery F U))) :
    mapMain f (show OracleComp (advSpec U (U × F) G₁) (Output F (Forgery F U)) from query q >>= next) =
      (queries f (message f) q >>= fun r => mapMain f (next r) : OracleComp (advSpec T (T × F) G₁) (Output F (Forgery F T))) := by
  simp only [mapMain, simulateQ_bind, simulateQ_HasQuery_query, map_bind]

/-! ## Restriction to a finite cover -/

/-- Every requested period, signed period and attacked period has a preimage. -/
def Liftable (f : U → T) (oa : OracleComp (advSpec T (T × F) G₁) (Output F (Forgery F T))) : Prop :=
  allPathsSatisfy
    (fun q => match q with
      | .inl (.inl _) => True
      | .inl (.inr i) => i ∈ Set.range f
      | .inr m => m.1 ∈ Set.range f)
    (fun out => out.mstar.1.1 ∈ Set.range f) (fun _ => Set.univ) oa

noncomputable def restrictMain (f : U → T) (oa : OracleComp (advSpec T (T × F) G₁) (Output F (Forgery F T)))
    (h : Liftable f oa) : OracleComp (advSpec U (U × F) G₁) (Output F (Forgery F U)) := by
  induction oa using OracleComp.recOn with
  | pure out =>
      have hout : out.mstar.1.1 ∈ Set.range f := (allPathsSatisfy_pure out).mp h
      exact pure ⟨((Classical.choose hout, out.mstar.1.2), out.mstar.2), out.β, out.γ, out.ξ⟩
  | queryBind q next ih =>
      have hq := ((allPathsSatisfy_query_bind q next).mp h).1
      have hn := ((allPathsSatisfy_query_bind q next).mp h).2
      rcases q with ((n | i) | m)
      · exact query (spec := advSpec U (U × F) G₁) (.inl (.inl n)) >>= fun r => ih r (hn r (Set.mem_univ _))
      · exact query (spec := advSpec U (U × F) G₁) (.inl (.inr (Classical.choose hq))) >>= fun r => ih r (hn r (Set.mem_univ _))
      · exact query (spec := advSpec U (U × F) G₁) (.inr (Classical.choose hq, m.2)) >>= fun r => ih r (hn r (Set.mem_univ _))

theorem restrictMain_random (f : U → T) (n : Nat) (next : Fin (n + 1) → OracleComp (advSpec T (T × F) G₁) (Output F (Forgery F T)))
    (h : Liftable f (OracleComp.queryBind (spec := advSpec T (T × F) G₁) (.inl (.inl n)) next)) :
    restrictMain f (OracleComp.queryBind (spec := advSpec T (T × F) G₁) (.inl (.inl n)) next) h =
      (query (spec := advSpec U (U × F) G₁) (.inl (.inl n)) >>= fun r => restrictMain f (next r)
        (((allPathsSatisfy_query_bind (spec := advSpec T (T × F) G₁) (.inl (.inl n)) next).mp h).2 r (Set.mem_univ _))) := rfl

theorem restrictMain_hash (f : U → T) (i : T) (next : G₁ → OracleComp (advSpec T (T × F) G₁) (Output F (Forgery F T)))
    (h : Liftable f (OracleComp.queryBind (spec := advSpec T (T × F) G₁) (.inl (.inr i)) next)) :
    restrictMain f (OracleComp.queryBind (spec := advSpec T (T × F) G₁) (.inl (.inr i)) next) h =
      (query (spec := advSpec U (U × F) G₁) (.inl (.inr (Classical.choose
        (((allPathsSatisfy_query_bind (spec := advSpec T (T × F) G₁) (.inl (.inr i)) next).mp h).1)))) >>= fun r =>
        restrictMain f (next r)
          (((allPathsSatisfy_query_bind (spec := advSpec T (T × F) G₁) (.inl (.inr i)) next).mp h).2 r (Set.mem_univ _))) := rfl

theorem restrictMain_sign (f : U → T) (m : T × F) (next : G₁ → OracleComp (advSpec T (T × F) G₁) (Output F (Forgery F T)))
    (h : Liftable f (OracleComp.queryBind (spec := advSpec T (T × F) G₁) (.inr m) next)) :
    restrictMain f (OracleComp.queryBind (spec := advSpec T (T × F) G₁) (.inr m) next) h =
      (query (spec := advSpec U (U × F) G₁) (.inr (Classical.choose
        (((allPathsSatisfy_query_bind (spec := advSpec T (T × F) G₁) (.inr m) next).mp h).1), m.2)) >>= fun r =>
        restrictMain f (next r)
          (((allPathsSatisfy_query_bind (spec := advSpec T (T × F) G₁) (.inr m) next).mp h).2 r (Set.mem_univ _))) := rfl

theorem mapMain_restrictMain (f : U → T) (oa : OracleComp (advSpec T (T × F) G₁) (Output F (Forgery F T))) (h : Liftable f oa) :
    mapMain f (restrictMain f oa h) = oa := by
  induction oa using OracleComp.recOn with
  | pure out =>
      change pure (mapOut f ⟨((Classical.choose _, out.mstar.1.2), out.mstar.2), out.β, out.γ, out.ξ⟩) =
        (pure out : OracleComp (advSpec T (T × F) G₁) (Output F (Forgery F T)))
      have he := Classical.choose_spec ((allPathsSatisfy_pure out).mp h)
      simp only [mapOut, forgery, message, Prod.map_apply, id_eq, he]
  | queryBind q next ih =>
      have hq := ((allPathsSatisfy_query_bind q next).mp h).1
      rcases q with ((n | i) | m) <;>
        simp only [restrictMain_random, restrictMain_hash, restrictMain_sign, mapMain_query_bind, queries]
      · exact congrArg (fun k => query (spec := advSpec T (T × F) G₁) (.inl (.inl n)) >>= k) (funext fun r => ih r _)
      · rw [Classical.choose_spec hq]
        exact congrArg (fun k => query (spec := advSpec T (T × F) G₁) (.inl (.inr i)) >>= k) (funext fun r => ih r _)
      · have hm : message f (Classical.choose hq, m.2) = m := Prod.ext (Classical.choose_spec hq) rfl
        rw [hm]
        exact congrArg (fun k => query (spec := advSpec T (T × F) G₁) (.inr m) >>= k) (funext fun r => ih r _)

/-- A view over the cover agreeing with `V` wherever `V` is liftable; a default elsewhere. -/
noncomputable def restrictView (f : U → T) (V : View F T G₁ G₂) (defaultKey : G₂ × G₂)
    (hdefault : Liftable f (V.main defaultKey)) : View F U G₁ G₂ := by
  classical
  exact ⟨fun pk => if h : Liftable f (V.main pk) then restrictMain f (V.main pk) h else restrictMain f (V.main defaultKey) hdefault⟩

theorem restrictView_map_at (f : U → T) (V : View F T G₁ G₂) (defaultKey : G₂ × G₂)
    (hdefault : Liftable f (V.main defaultKey)) (pk : G₂ × G₂) (hpk : Liftable f (V.main pk)) :
    (mapView f (restrictView f V defaultKey hdefault)).main pk = V.main pk := by
  simp only [mapView, restrictView, dite_eq_left hpk, mapMain_restrictMain]

/-- A finite cover of the periods a view touches at every generated key pair. -/
theorem exists_cover [Finite F] [Finite G₁] (g₂ : G₂) [SMul F G₂] (V : View F T G₁ G₂) :
    ∃ cover : Finset T, ∀ a b : F, Liftable (Subtype.val : {t // t ∈ cover} → T) (V.main (a • g₂, b • g₂)) := by
  classical
  let labels : (advSpec T (T × F) G₁).Domain → Finset T := fun q => match q with
    | .inl (.inl _) => ∅
    | .inl (.inr i) => {i}
    | .inr m => {m.1}
  have : ∀ q, Finite ((advSpec T (T × F) G₁).Range q) := by
    intro q
    rcases q with ((n | i) | m)
    · exact inferInstanceAs (Finite (Fin (n + 1)))
    · exact inferInstanceAs (Finite G₁)
    · exact inferInstanceAs (Finite G₁)
  obtain ⟨cover, hcover⟩ := Signatures.FiniteDomain.exists_family_cover (K := F × F) labels
    (fun out : Output F (Forgery F T) => {out.mstar.1.1}) (fun ab => V.main (ab.1 • g₂, ab.2 • g₂))
  refine ⟨cover, fun a b => ?_⟩
  apply Signatures.FiniteDomain.allPaths_mono _ _ _ (hcover (a, b))
  · intro q hq
    rcases q with ((n | i) | m)
    · trivial
    · exact ⟨⟨i, hq (Finset.mem_singleton_self _)⟩, rfl⟩
    · exact ⟨⟨m.1, hq (Finset.mem_singleton_self _)⟩, rfl⟩
  · intro out hout
    exact ⟨⟨out.mstar.1.1, hout (Finset.mem_singleton_self _)⟩, rfl⟩

/-! ## The lazy game is invariant under relabeling -/

section Game
variable [Field F] [SampleableType F] [DecidableEq F] [DecidableEq T] [DecidableEq U]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

omit [SampleableType F] [DecidableEq F] [DecidableEq T] [DecidableEq U] [SampleableType G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem mapIdx_map_snd {D D' : Type} (g : D → D') (φ : Nat → G₁ → G₁) :
    ∀ tr : List (D × G₁), (tr.map (Prod.map g id)).mapIdx (fun n p => φ n p.2) = tr.mapIdx (fun n p => φ n p.2)
  | [] => rfl
  | a :: tr => by
    simp only [List.map_cons, List.mapIdx_cons, Prod.map_snd, id_eq]
    exact congrArg _ (mapIdx_map_snd g (fun n => φ (n + 1)) tr)

omit [SampleableType F] [DecidableEq F] [DecidableEq T] [DecidableEq U] [SampleableType G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem weightedReplies_map {D D' : Type} (g : D → D') (coeff : List F) (tr : List (D × G₁)) :
    weightedReplies coeff (tr.map (Prod.map g id)) = weightedReplies coeff tr := by
  unfold weightedReplies
  rw [mapIdx_map_snd g (fun n p => tokenCoeff coeff n • p)]

omit [SampleableType F] [DecidableEq F] [DecidableEq T] [DecidableEq U] [SampleableType G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem aggregate_map (f : U → T) (g₁ : G₁) (out : Output F (Forgery F U)) (tr : Transcript U (U × F) G₁) :
    Proofs.aggregate g₁ (mapOut f out) (mapTranscript f (message f) tr) = Proofs.aggregate g₁ out tr := by
  simp only [Proofs.aggregate, mapOut, mapTranscript, weightedReplies_map]

omit [SampleableType F] [SampleableType G₁] in
theorem accepts_map (f : U → T) (hf : Function.Injective f) (g₂ : G₂) (x y : F) (data : Forgery F U) (aggregate : G₁)
    (signed : List (U × F)) (hash : G₁) :
    Proofs.accepts (Gₜ := Gₜ) g₂ x y (forgery f data) aggregate (signed.map (message f)) hash =
      Proofs.accepts (Gₜ := Gₜ) g₂ x y data aggregate signed hash := by
  have fresh : message (F := F) f data.1 ∈ signed.map (message f) ↔ data.1 ∈ signed :=
    List.mem_map_of_injective (message_injective f hf)
  have once : onePerPeriod (message f data.1) (signed.map (message f)) ↔ onePerPeriod data.1 signed := by
    simp only [onePerPeriod, List.pairwise_map, message, Prod.map_fst, hf.ne_iff]
  simp only [Proofs.accepts]
  rw [show (forgery f data).1 = message f data.1 from rfl, show (message (F := F) f data.1).2 = data.1.2 from rfl,
    show (forgery f data).2 = data.2 from rfl, decide_eq_decide.mpr (and_congr (not_congr fresh) once)]

theorem handler_random {N : Type → Type} [Monad N] (random : QueryImpl unifSpec N) (hash : T → N G₁) (sign : T × F → N G₁)
    (n : Nat) (tr : Transcript T (T × F) G₁) :
    (handler random hash sign (.inl (.inl n))).run tr = random n >>= fun u => pure (u, tr) := rfl
theorem handler_hash {N : Type → Type} [Monad N] (random : QueryImpl unifSpec N) (hash : T → N G₁) (sign : T × F → N G₁)
    (i : T) (tr : Transcript T (T × F) G₁) :
    (handler random hash sign (.inl (.inr i))).run tr = hash i >>= fun H => pure (H, (tr.1 ++ [(i, H)], tr.2)) := rfl
theorem handler_sign {N : Type → Type} [Monad N] (random : QueryImpl unifSpec N) (hash : T → N G₁) (sign : T × F → N G₁)
    (m : T × F) (tr : Transcript T (T × F) G₁) :
    (handler random hash sign (.inr m)).run tr = sign m >>= fun σ => pure (σ, (tr.1, tr.2 ++ [(m, σ)])) := rfl

omit [SampleableType F] [DecidableEq F] [DecidableEq T] [DecidableEq U] [SampleableType G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem handlerSim_map {α : Type} (f : U → T) (x y : F) (P : OracleComp (advSpec U (U × F) G₁) α) (tr : Transcript U (U × F) G₁) :
    (simulateQ (handler
        (fun n => (liftM ((baseSpec T G₁).query (.inl n)) : OracleComp (baseSpec T G₁) _))
        (fun i => (liftM ((baseSpec T G₁).query (.inr i)) : OracleComp (baseSpec T G₁) G₁))
        (Proofs.signing x y)) (simulateQ (queries f (message f)) P)).run (mapTranscript f (message f) tr) =
      Prod.map id (mapTranscript f (message f)) <$> simulateQ (baseQueries f)
        ((simulateQ (handler
          (fun n => (liftM ((baseSpec U G₁).query (.inl n)) : OracleComp (baseSpec U G₁) _))
          (fun i => (liftM ((baseSpec U G₁).query (.inr i)) : OracleComp (baseSpec U G₁) G₁))
          (Proofs.signing x y)) P).run tr) := by
  induction P using OracleComp.inductionOn generalizing tr with
  | pure a => simp
  | query_bind q next ih =>
    rcases q with ((n | i) | m) <;>
      simp only [simulateQ_bind, simulateQ_spec_query, queries, simulateQ_HasQuery_query, StateT.run_bind,
        handler_random, handler_hash, handler_sign, Proofs.signing, message_fst, message_snd, bind_assoc, pure_bind, baseQueries, map_bind]
    · exact bind_congr fun r => ih r tr
    · exact bind_congr fun r => by simpa only [mapTranscript_hash] using ih r (tr.1 ++ [(i, r)], tr.2)
    · exact bind_congr fun r => by
        simpa only [mapTranscript_sign] using ih ((x + y * m.2) • r) (tr.1, tr.2 ++ [(m, (x + y * m.2) • r)])

omit [SampleableType F] [DecidableEq F] [DecidableEq T] [DecidableEq U] [SampleableType G₁] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ] in
theorem lazyRun_map (f : U → T) (V : View F U G₁ G₂) (x y : F) (pk : G₂ × G₂) :
    Proofs.lazyRun (mapView f V) x y pk =
      Prod.map (mapOut f) (mapTranscript f (message f)) <$> simulateQ (baseQueries f) (Proofs.lazyRun V x y pk) := by
  unfold Proofs.lazyRun mapView mapMain
  simp only [simulateQ_map, StateT.run_map]
  rw [← mapTranscript_empty f (message f), handlerSim_map]
  simp only [Functor.map_map]
  rfl

theorem experiment_map (f : U → T) (hf : Function.Injective f) (g₁ : G₁) (g₂ : G₂) (V : View F U G₁ G₂) :
    Proofs.experiment (Gₜ := Gₜ) g₁ g₂ (mapView f V) = simulateQ (baseQueries f) (Proofs.experiment (Gₜ := Gₜ) g₁ g₂ V) := by
  unfold Proofs.experiment
  simp only [simulateQ_bind, baseQueries_lift, lazyRun_map, bind_map_left, simulateQ_pure]
  refine bind_congr fun x => bind_congr fun y => bind_congr fun z => bind_congr fun hash => ?_
  obtain ⟨out, tr⟩ := z
  simp only [Prod.map_apply]
  rw [aggregate_map]
  have hs : (mapTranscript f (message f) tr).2.map Prod.fst = (tr.2.map Prod.fst).map (message f) := by
    simp only [mapTranscript, List.map_map]
    congr 1
  rw [hs]
  exact congrArg pure (accepts_map f hf g₂ x y out.mstar _ _ hash)

theorem lazyGame_map (f : U → T) (hf : Function.Injective f) (g₁ : G₁) (g₂ : G₂) (V : View F U G₁ G₂) :
    Proofs.lazyGame (Gₜ := Gₜ) g₁ g₂ (mapView f V) = Proofs.lazyGame (Gₜ := Gₜ) g₁ g₂ V := by
  unfold Proofs.lazyGame
  rw [experiment_map f hf]
  exact lazyRun_rename f hf _

omit [DecidableEq U] in
theorem lazyGame_congr (g₁ : G₁) (g₂ : G₂) (V W : View F T G₁ G₂)
    (h : ∀ a b : F, V.main (a • g₂, b • g₂) = W.main (a • g₂, b • g₂)) :
    Proofs.lazyGame (Gₜ := Gₜ) g₁ g₂ V = Proofs.lazyGame (Gₜ := Gₜ) g₁ g₂ W := by
  unfold Proofs.lazyGame Proofs.experiment Proofs.lazyRun
  simp only [h]
end Game

/-! ## The wrapped solvers are invariant under relabeling -/

section Solvers
open SynchronizedPS.Wrapped
open BLS.LazyAGM.MessageTransport (mapOutput)

variable [Field F] [SampleableType F] [DecidableEq T] [DecidableEq U]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

def mapEvent (f : U → T) : Event F U → Event F T
  | .hash t => .hash (f t)
  | .sign m => .sign (message f m)

theorem remap_map (f : U → T) (c : T × F → F) (c' : U × F → F) (hc : ∀ m, c (message f m) = c' m) (γ ξ : List F) :
    ∀ (events : List (Event F U)) (i j : Nat), remap c γ ξ (events.map (mapEvent f)) i j = remap c' γ ξ events i j
  | [], _, _ => rfl
  | .hash _ :: rest, i, j => by simp only [List.map_cons, mapEvent, remap, remap_map f c c' hc γ ξ rest]
  | .sign m :: rest, i, j => by simp only [List.map_cons, mapEvent, remap, hc, remap_map f c c' hc γ ξ rest]

theorem translator_map {α : Type} (f : U → T) (c : T × F → F) (c' : U × F → F) (hc : ∀ m, c (message f m) = c' m)
    (P : OracleComp (advSpec U (U × F) G₁) α) (events : List (Event F U)) :
    (simulateQ (translator c) (simulateQ (queries f (message f)) P)).run (events.map (mapEvent f)) =
      Prod.map id (List.map (mapEvent f)) <$> simulateQ (queries f (message f)) ((simulateQ (translator c') P).run events) := by
  induction P using OracleComp.inductionOn generalizing events with
  | pure a => simp
  | query_bind q next ih =>
    rcases q with ((n | t) | m) <;>
      simp only [simulateQ_bind, simulateQ_spec_query, queries, simulateQ_HasQuery_query, StateT.run_bind, translator, StateT.run_mk,
        message_fst, hc, bind_assoc, pure_bind, map_bind]
    · exact bind_congr fun r => ih r events
    · refine bind_congr fun r => ?_
      have h := ih r (events ++ [.hash t])
      rw [List.map_append, List.map_singleton] at h
      exact h
    · refine bind_congr fun point => bind_congr fun σ => ?_
      have h := ih (σ + c' m • point) (events ++ [.sign m])
      rw [List.map_append, List.map_singleton] at h
      exact h

/-- Wrapping a relabeled view is relabeling the wrapped adversary. -/
theorem wrap_map (f : U → T) (c : T × F → F) (c' : U × F → F) (hc : ∀ m, c (message f m) = c' m)
    (fin : Forgery F T → F) (fin' : Forgery F U → F) (hfin : ∀ out, fin (forgery f out) = fin' out)
    (keys : G₂ → G₂ × G₂) (V : View F U G₁ G₂) :
    wrap c fin keys (mapView f V) = mapAdversary f (message f) (wrap c' fin' keys V) := by
  unfold wrap mapAdversary WeightedTransport.mapMain mapView mapMain
  congr 1
  funext pk
  simp only [simulateQ_map, StateT.run_map, simulateQ_bind, simulateQ_spec_query, queries, map_bind, bind_map_left]
  have h := translator_map f c c' hc (V.main (keys pk)) []
  simp only [List.map_nil] at h
  rw [h]
  simp only [bind_map_left]
  refine bind_congr fun z => ?_
  obtain ⟨out, events⟩ := z
  simp only [Prod.map_apply, id_eq, mapOut, remap_map f c c' hc, hfin]
  rfl

theorem terms₁_map (f : U → T) (m : U × F) : terms₁ (message f m) = (terms₁ m).map (Prod.map f id) := rfl
theorem terms₂_map (f : U → T) (m : U × F) : terms₂ (message f m) = (terms₂ m).map (Prod.map f id) := rfl

theorem wrap₁_map (f : U → T) (y : F) (g₂ : G₂) (V : View F U G₁ G₂) :
    wrap₁ y g₂ (mapView f V) = mapAdversary f (message f) (wrap₁ y g₂ V) :=
  wrap_map f (correction₁ y) (correction₁ y) (fun _ => rfl) (final₁ y) (final₁ y) (fun _ => rfl) _ V
theorem wrap₂_map (f : U → T) (x : F) (g₂ : G₂) (V : View F U G₁ G₂) :
    wrap₂ x g₂ (mapView f V) = mapAdversary f (message f) (wrap₂ x g₂ V) :=
  wrap_map f (correction₂ x) (correction₂ x) (fun _ => rfl) (final₂ x) (final₂ x) (fun _ => rfl) _ V

variable (f : U → T) (hf : Function.Injective f) (V : View F U G₁ G₂)

include hf in
theorem solverGood₁_map : solverGood₁ (mapView f V) = solverGood₁ V := by
  funext g X g₂ Z₂
  refine bind_congr fun y => ?_
  have h : goodReductionList terms₁ (wrap₁ y g₂ (mapView f V)) = goodReductionList terms₁ (wrap₁ y g₂ V) := by
    rw [wrap₁_map]
    exact goodReduction_map f hf (message f) terms₁ terms₁ (terms₁_map f) _
  exact congrFun (congrFun (congrFun (congrFun h g) X) g₂) Z₂
include hf in
theorem solverBad₁_map : solverBad₁ (mapView f V) = solverBad₁ V := by
  funext g X g₂ Z₂
  refine bind_congr fun y => ?_
  have h : badReductionList terms₁ (wrap₁ y g₂ (mapView f V)) = badReductionList terms₁ (wrap₁ y g₂ V) := by
    rw [wrap₁_map]
    exact badReduction_map f hf (message f) terms₁ terms₁ (terms₁_map f) _
  exact congrFun (congrFun (congrFun (congrFun h g) X) g₂) Z₂
include hf in
theorem solverGood₂_map : solverGood₂ (mapView f V) = solverGood₂ V := by
  funext g X g₂ Z₂
  refine bind_congr fun x => ?_
  have h : goodReductionList terms₂ (wrap₂ x g₂ (mapView f V)) = goodReductionList terms₂ (wrap₂ x g₂ V) := by
    rw [wrap₂_map]
    exact goodReduction_map f hf (message f) terms₂ terms₂ (terms₂_map f) _
  exact congrFun (congrFun (congrFun (congrFun h g) X) g₂) Z₂
include hf in
theorem solverBad₂_map : solverBad₂ (mapView f V) = solverBad₂ V := by
  funext g X g₂ Z₂
  refine bind_congr fun x => ?_
  have h : badReductionList terms₂ (wrap₂ x g₂ (mapView f V)) = badReductionList terms₂ (wrap₂ x g₂ V) := by
    rw [wrap₂_map]
    exact badReduction_map f hf (message f) terms₂ terms₂ (terms₂_map f) _
  exact congrFun (congrFun (congrFun (congrFun h g) X) g₂) Z₂

/-! ## Agreement at the generated keys suffices -/

theorem wrap_main_congr (c : T × F → F) (fin : Forgery F T → F) (keys : G₂ → G₂ × G₂) (V W : View F T G₁ G₂) (pk : G₂)
    (h : V.main (keys pk) = W.main (keys pk)) : (wrap c fin keys V).main pk = (wrap c fin keys W).main pk := by
  simp only [wrap, h]

theorem goodProgram_main_congr (terms : T × F → List (T × F)) (g X : G₁) (pk : G₂) (A B : Adversary F T (T × F) G₁ G₂)
    (h : A.main pk = B.main pk) : goodProgram terms g X pk A = goodProgram terms g X pk B := by
  unfold goodProgram privateRun
  rw [h]
theorem badProgram_main_congr (terms : T × F → List (T × F)) (g X : G₁) (pk : G₂) (kappa : F) (A B : Adversary F T (T × F) G₁ G₂)
    (h : A.main pk = B.main pk) : badProgram terms g X pk kappa A = badProgram terms g X pk kappa B := by
  unfold badProgram privateRun
  rw [h]

variable (g₁ : G₁) (g₂ : G₂) (V W : View F T G₁ G₂) (hVW : ∀ a b : F, V.main (a • g₂, b • g₂) = W.main (a • g₂, b • g₂))

include hVW in
theorem solverGood₁_congr : AlgebraicGroupModel.dlog11Exp g₁ g₂ (solverGood₁ V) = AlgebraicGroupModel.dlog11Exp g₁ g₂ (solverGood₁ W) := by
  unfold AlgebraicGroupModel.dlog11Exp
  refine bind_congr fun α => ?_
  congr 1
  unfold solverGood₁
  refine bind_congr fun y => ?_
  unfold goodReductionList
  rw [goodProgram_main_congr terms₁ g₁ (α • g₁) (α • g₂) (wrap₁ y g₂ V) (wrap₁ y g₂ W)
    (wrap_main_congr (correction₁ y) (final₁ y) (fun pk => (pk, y • g₂)) V W (α • g₂) (hVW α y))]
include hVW in
theorem solverBad₁_congr : AlgebraicGroupModel.dlog11Exp g₁ g₂ (solverBad₁ V) = AlgebraicGroupModel.dlog11Exp g₁ g₂ (solverBad₁ W) := by
  unfold AlgebraicGroupModel.dlog11Exp
  refine bind_congr fun α => ?_
  congr 1
  unfold solverBad₁ badReductionList
  refine bind_congr fun y => bind_congr fun kappa => ?_
  rw [badProgram_main_congr terms₁ g₁ (α • g₁) (kappa • g₂) kappa (wrap₁ y g₂ V) (wrap₁ y g₂ W)
    (wrap_main_congr (correction₁ y) (final₁ y) (fun pk => (pk, y • g₂)) V W (kappa • g₂) (hVW kappa y))]
include hVW in
theorem solverGood₂_congr : AlgebraicGroupModel.dlog11Exp g₁ g₂ (solverGood₂ V) = AlgebraicGroupModel.dlog11Exp g₁ g₂ (solverGood₂ W) := by
  unfold AlgebraicGroupModel.dlog11Exp
  refine bind_congr fun α => ?_
  congr 1
  unfold solverGood₂
  refine bind_congr fun x => ?_
  unfold goodReductionList
  rw [goodProgram_main_congr terms₂ g₁ (α • g₁) (α • g₂) (wrap₂ x g₂ V) (wrap₂ x g₂ W)
    (wrap_main_congr (correction₂ x) (final₂ x) (fun pk => (x • g₂, pk)) V W (α • g₂) (hVW x α))]
include hVW in
theorem solverBad₂_congr : AlgebraicGroupModel.dlog11Exp g₁ g₂ (solverBad₂ V) = AlgebraicGroupModel.dlog11Exp g₁ g₂ (solverBad₂ W) := by
  unfold AlgebraicGroupModel.dlog11Exp
  refine bind_congr fun α => ?_
  congr 1
  unfold solverBad₂ badReductionList
  refine bind_congr fun x => bind_congr fun kappa => ?_
  rw [badProgram_main_congr terms₂ g₁ (α • g₁) (kappa • g₂) kappa (wrap₂ x g₂ V) (wrap₂ x g₂ W)
    (wrap_main_congr (correction₂ x) (final₂ x) (fun pk => (x • g₂, pk)) V W (kappa • g₂) (hVW x kappa))]
end Solvers

/-! ## Security for an arbitrary period type -/

section Arbitrary
open SynchronizedPS.Wrapped BilinearGroup

variable [Field F] [SampleableType F] [Fintype F] [DecidableEq F] [DecidableEq T]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

/-- **Synchronized PS security from the four wrapped solvers, for any period type.** The finite
cover of the periods the view touches at the generated keys is used only inside the proof. -/
theorem security_wrapped (V : View F T G₁ G₂) (g₁ : G₁) (g₂ : G₂)
    (hgen : Function.Bijective (fun ρ : F => ρ • g₁))
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ))) :
    𝒟[Proofs.lazyGame (Gₜ := Gₜ) g₁ g₂ V] {true} ≤
      Model.dlog11Advantage g₁ g₂ (solverGood₁ V) + Model.dlog11Advantage g₁ g₂ (solverBad₁ V) +
      Model.dlog11Advantage g₁ g₂ (solverGood₂ V) + Model.dlog11Advantage g₁ g₂ (solverBad₂ V) +
      2 / (Fintype.card F : ENNReal) := by
  classical
  obtain ⟨cover, hcover⟩ := exists_cover g₂ V
  let W := restrictView (Subtype.val : {t // t ∈ cover} → T) V ((0 : F) • g₂, (0 : F) • g₂) (hcover 0 0)
  have hkey : ∀ a b : F, V.main (a • g₂, b • g₂) = (mapView Subtype.val W).main (a • g₂, b • g₂) := fun a b =>
    (restrictView_map_at _ V _ _ _ (hcover a b)).symm
  have hgame : Proofs.lazyGame (Gₜ := Gₜ) g₁ g₂ V = Proofs.lazyGame (Gₜ := Gₜ) g₁ g₂ W :=
    (lazyGame_congr g₁ g₂ V _ hkey).trans (lazyGame_map Subtype.val Subtype.val_injective g₁ g₂ W)
  rw [hgame, Model.dlog11Advantage, Model.dlog11Advantage, Model.dlog11Advantage, Model.dlog11Advantage,
    solverGood₁_congr g₁ g₂ V _ hkey, solverBad₁_congr g₁ g₂ V _ hkey, solverGood₂_congr g₁ g₂ V _ hkey, solverBad₂_congr g₁ g₂ V _ hkey,
    solverGood₁_map Subtype.val Subtype.val_injective W, solverBad₁_map Subtype.val Subtype.val_injective W,
    solverGood₂_map Subtype.val Subtype.val_injective W, solverBad₂_map Subtype.val Subtype.val_injective W]
  exact Wrapped.security_wrapped W g₁ g₂ hgen hpair
end Arbitrary

end SynchronizedPS.Transport
