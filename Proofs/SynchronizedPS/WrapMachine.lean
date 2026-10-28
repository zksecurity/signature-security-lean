import Proofs.SynchronizedPS.Wrapped
import Proofs.Model.MachineView

/-! # The wrapped attacker as an oracle machine

A machine implementing the inner attacker is turned into one implementing the wrapper of
`Wrapped.lean`: it forwards randomness and hash queries, answers a signing query by first
exposing the hash of its period, then the signing query, feeding the corrected reply to the
inner machine; when the inner machine returns it exposes one last hash and finishes. The
wrapper's own data (the known key) travels in the machine input and state, so the inner
machine stays fixed. Implementation is a view-level simulation, and the query budget grows by
one per signing query plus the final hash. -/

open OracleComp OracleSpec Model Model.LazyAGM
open PFunctor PFunctor.DynSystem PFunctor.DynSystem.DynComputation

namespace SynchronizedPS.Wrapped

set_option linter.unusedSectionVars false

variable {F Period G₁ G₂ : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

/-- Where the wrapper stands between two inner steps. The marks are the wrapper's record of
the attacker's events (one per hash query and per signing query, recorded when the request
appears); the inner state is kept while the wrapper waits for the period's hash before a
signing query. -/
inductive Core (S In E G₁ : Type)
  /-- The inner machine is at `inner`, whose pending request is already marked. -/
  | ready (inner : S) (marks : List E)
  /-- `inner` asked to sign; `point` is its period's hash and the signing query is pending. -/
  | gotHash (inner : S) (point : G₁) (marks : List E)
  /-- The inner machine returned `result`; the final hash is pending. -/
  | final (result : In) (marks : List E)
  /-- The final hash was answered. -/
  | done (result : In) (marks : List E)

variable {U D E α In Out : Type}
  (M : OracleMachine (advSpec Period (Period × F) G₁) α In)
  (split : U → α) (proj : U → D) (corr : D → Period × F → F) (mark : D → Event F Period → E)
  (finalIndex : In → Period) (fin : D → In → List E → Out)

/-- The attacker event an inner view is about to produce. -/
def pendingEvent : In ⊕ (advSpec Period (Period × F) G₁).toPFunctor.Obj M.State → List (Event F Period)
  | .inr ⟨.inl (.inr t), _⟩ => [.hash t]
  | .inr ⟨.inr m, _⟩ => [.sign m]
  | _ => []

/-- Enter an inner state: a returned result waits for the final hash, a pending request is marked. -/
def enter (d : D) (s : M.State) (marks : List E) : D × Core M.State In E G₁ :=
  match M.view s with
  | .inl result => (d, .final result marks)
  | .inr _ => (d, .ready s (marks ++ (pendingEvent M (M.view s)).map (mark d)))

/-- The step out of a ready state, in terms of the inner machine's view. -/
def readyStep (d : D) (s : M.State) (marks : List E) :
    Out ⊕ (advSpec Period (Period × F) G₁).toPFunctor.Obj (D × Core M.State In E G₁) :=
  match M.view s with
  | .inl result => .inr ⟨.inl (.inr (finalIndex result)), fun _ => (d, .done result marks)⟩
  | .inr ⟨.inl (.inl n), next⟩ => .inr ⟨.inl (.inl n), fun r => enter M mark d (next r) marks⟩
  | .inr ⟨.inl (.inr t), next⟩ => .inr ⟨.inl (.inr t), fun h => enter M mark d (next h) marks⟩
  | .inr ⟨.inr m, _⟩ => .inr ⟨.inl (.inr m.1), fun h => (d, .gotHash s h marks)⟩

/-- One step of the wrapper. -/
def step : D × Core M.State In E G₁ →
    Out ⊕ (advSpec Period (Period × F) G₁).toPFunctor.Obj (D × Core M.State In E G₁)
  | (d, .ready s marks) => readyStep M mark finalIndex d s marks
  | (d, .gotHash s h marks) =>
    match M.view s with
    | .inr ⟨.inr m, next⟩ => .inr ⟨.inr m, fun σ => enter M mark d (next (σ + corr d m • h)) marks⟩
    | _ => readyStep M mark finalIndex d s marks
  | (d, .final result marks) => .inr ⟨.inl (.inr (finalIndex result)), fun _ => (d, .done result marks)⟩
  | (d, .done result marks) => .inl (fin d result marks)

/-! ### Steps in terms of the inner view -/
section Views
variable {d : D} {s : M.State} {marks : List E}

theorem pendingEvent_inl (result : In) : pendingEvent M (.inl result) = [] := rfl
theorem pendingEvent_random (n : ℕ) (next : Fin (n + 1) → M.State) :
    pendingEvent M (.inr ⟨.inl (.inl n), next⟩) = [] := rfl
theorem pendingEvent_hash (t : Period) (next : G₁ → M.State) :
    pendingEvent M (.inr ⟨.inl (.inr t), next⟩) = [.hash t] := rfl
theorem pendingEvent_sign (m : Period × F) (next : G₁ → M.State) :
    pendingEvent M (.inr ⟨.inr m, next⟩) = [.sign m] := rfl

theorem enter_inl {result : In} (h : M.view s = .inl result) : enter M mark d s marks = (d, .final result marks) := by
  unfold enter; rw [h]
theorem enter_inr {a : (advSpec Period (Period × F) G₁).Domain} {next : _ → M.State} (h : M.view s = .inr ⟨a, next⟩) :
    enter M mark d s marks = (d, .ready s (marks ++ (pendingEvent M (.inr ⟨a, next⟩)).map (mark d))) := by
  unfold enter; rw [h]

theorem readyStep_inl {result : In} (h : M.view s = .inl result) :
    readyStep (Out := Out) M mark finalIndex d s marks = .inr ⟨.inl (.inr (finalIndex result)), fun _ => (d, .done result marks)⟩ := by
  unfold readyStep; rw [h]
theorem readyStep_random {n : ℕ} {next : Fin (n + 1) → M.State} (h : M.view s = .inr ⟨.inl (.inl n), next⟩) :
    readyStep (Out := Out) M mark finalIndex d s marks = .inr ⟨.inl (.inl n), fun r => enter M mark d (next r) marks⟩ := by
  unfold readyStep; rw [h]
theorem readyStep_hash {t : Period} {next : G₁ → M.State} (h : M.view s = .inr ⟨.inl (.inr t), next⟩) :
    readyStep (Out := Out) M mark finalIndex d s marks = .inr ⟨.inl (.inr t), fun point => enter M mark d (next point) marks⟩ := by
  unfold readyStep; rw [h]
theorem readyStep_sign {m : Period × F} {next : G₁ → M.State} (h : M.view s = .inr ⟨.inr m, next⟩) :
    readyStep (Out := Out) M mark finalIndex d s marks = .inr ⟨.inl (.inr m.1), fun point => (d, .gotHash s point marks)⟩ := by
  unfold readyStep; rw [h]

theorem step_ready : step M corr mark finalIndex fin (d, .ready s marks) = readyStep M mark finalIndex d s marks := rfl
theorem step_gotHash {m : Period × F} {next : G₁ → M.State} (h : M.view s = .inr ⟨.inr m, next⟩) (point : G₁) :
    step M corr mark finalIndex fin (d, .gotHash s point marks) =
      .inr ⟨.inr m, fun σ => enter M mark d (next (σ + corr d m • point)) marks⟩ := by
  dsimp only [step]; rw [h]
theorem step_final (result : In) :
    step M corr mark finalIndex fin (d, .final result marks) = .inr ⟨.inl (.inr (finalIndex result)), fun _ => (d, .done result marks)⟩ := rfl
theorem step_done (result : In) : step M corr mark finalIndex fin (d, .done result marks) = .inl (fin d result marks) := rfl
end Views

/-- The wrapped machine. Reducible, so its states are visibly pairs. -/
@[reducible] def machine : OracleMachine (advSpec Period (Period × F) G₁) U Out :=
  DynComputation.ofStep (step M corr mark finalIndex fin) fun u => enter M mark (proj u) (M.init (split u)) []

variable (correction : U → Period × F → F) (finish : U → In → List (Event F Period) → Out)

/-- The wrapper program around an inner residual program `P` with events `events` delivered. -/
def translate (u : U) (P : OracleComp (advSpec Period (Period × F) G₁) In)
    (events : List (Event F Period)) : OracleComp (advSpec Period (Period × F) G₁) Out := do
  let (result, events) ← (simulateQ (translator (correction u)) P).run events
  let _ ← (liftM ((advSpec Period (Period × F) G₁).query (.inl (.inr (finalIndex result)))) :
    OracleComp (advSpec Period (Period × F) G₁) G₁)
  pure (finish u result events)

theorem translate_pure (u : U) (result : In) (events : List (Event F Period)) :
    translate finalIndex correction finish u (pure result) events =
      OracleComp.queryBind (spec := advSpec Period (Period × F) G₁) (.inl (.inr (finalIndex result))) fun _ => pure (finish u result events) := rfl

theorem translate_random (u : U) (n : ℕ)
    (k : Fin (n + 1) → OracleComp (advSpec Period (Period × F) G₁) In) (events : List (Event F Period)) :
    translate finalIndex correction finish u (OracleComp.queryBind (spec := advSpec Period (Period × F) G₁) (.inl (.inl n)) k) events =
      OracleComp.queryBind (spec := advSpec Period (Period × F) G₁) (.inl (.inl n)) fun r => translate finalIndex correction finish u (k r) events := rfl

theorem translate_hash (u : U) (t : Period)
    (k : G₁ → OracleComp (advSpec Period (Period × F) G₁) In) (events : List (Event F Period)) :
    translate finalIndex correction finish u (OracleComp.queryBind (spec := advSpec Period (Period × F) G₁) (.inl (.inr t)) k) events =
      OracleComp.queryBind (spec := advSpec Period (Period × F) G₁) (.inl (.inr t)) fun h =>
        translate finalIndex correction finish u (k h) (events ++ [.hash t]) := rfl

theorem translate_sign (u : U) (m : Period × F)
    (k : G₁ → OracleComp (advSpec Period (Period × F) G₁) In) (events : List (Event F Period)) :
    translate finalIndex correction finish u (OracleComp.queryBind (spec := advSpec Period (Period × F) G₁) (.inr m) k) events =
      OracleComp.queryBind (spec := advSpec Period (Period × F) G₁) (.inl (.inr m.1)) fun h => OracleComp.queryBind (spec := advSpec Period (Period × F) G₁) (.inr m) fun σ =>
        translate finalIndex correction finish u (k (σ + correction u m • h)) (events ++ [.sign m]) := rfl

/-- The synchronized PS wrapper is `translate` around the attacker's proof view. -/
theorem wrap_main (correction : Period × F → F) (final : Forgery F Period → F) (keys : G₂ → G₂ × G₂)
    (V : Proofs.View F Period G₁ G₂) (publicKey : G₂) :
    (wrap correction final keys V).main publicKey =
      translate (fun result => result.mstar.1.1) (fun _ => correction)
        (fun _ result events => ⟨result.mstar.1, result.β, remap correction result.γ result.ξ events 0 0 ++ [-(final result.mstar)], result.ξ⟩)
        publicKey (V.main (keys publicKey)) [] := rfl

/-! ### Translating mapped programs and comparing translations -/
section Congruence
variable {In' Out' U' : Type}

/-- Mapping the wrapper's result is finishing with the mapped value. -/
theorem translate_map_out (h : Out → Out') (u : U) (P : OracleComp (advSpec Period (Period × F) G₁) In) (events : List (Event F Period)) :
    h <$> translate finalIndex correction finish u P events =
      translate finalIndex correction (fun u result events => h (finish u result events)) u P events := by
  induction P generalizing events with
  | pure result => rfl
  | queryBind t k ih =>
    rcases t with (n | t) | m
    · rw [translate_random, translate_random]
      exact congrArg (OracleComp.queryBind _) (funext fun r => ih r events)
    · rw [translate_hash, translate_hash]
      exact congrArg (OracleComp.queryBind _) (funext fun h => ih h _)
    · rw [translate_sign, translate_sign]
      exact congrArg (OracleComp.queryBind _) (funext fun h => congrArg (OracleComp.queryBind _) (funext fun σ => ih _ _))

/-- Translating a mapped inner program is translating the program with the map folded into
the finishing steps. -/
theorem translate_map_in (g : In' → In) (finalIndex' : In' → Period) (fiLaw : ∀ r, finalIndex (g r) = finalIndex' r)
    (u : U) (P : OracleComp (advSpec Period (Period × F) G₁) In') (events : List (Event F Period)) :
    translate finalIndex correction finish u (g <$> P) events =
      translate finalIndex' correction (fun u result events => finish u (g result) events) u P events := by
  induction P generalizing events with
  | pure result =>
    show translate finalIndex correction finish u (pure (g result)) events =
      translate finalIndex' correction (fun u result events => finish u (g result) events) u (pure result) events
    rw [translate_pure, translate_pure, fiLaw]
  | queryBind t k ih =>
    rcases t with (n | t) | m
    · change translate finalIndex correction finish u (OracleComp.queryBind (spec := advSpec Period (Period × F) G₁) (.inl (.inl n)) fun r => g <$> k r) events = _
      rw [translate_random, translate_random]
      exact congrArg (OracleComp.queryBind _) (funext fun r => ih r events)
    · change translate finalIndex correction finish u (OracleComp.queryBind (spec := advSpec Period (Period × F) G₁) (.inl (.inr t)) fun h => g <$> k h) events = _
      rw [translate_hash, translate_hash]
      exact congrArg (OracleComp.queryBind _) (funext fun h => ih h _)
    · change translate finalIndex correction finish u (OracleComp.queryBind (spec := advSpec Period (Period × F) G₁) (.inr m) fun h => g <$> k h) events = _
      rw [translate_sign, translate_sign]
      exact congrArg (OracleComp.queryBind _) (funext fun h => congrArg (OracleComp.queryBind _) (funext fun σ => ih _ _))

/-- Two translations agree when their corrections agree and their finishes agree on every
event list the bounded program can produce. -/
theorem translate_congr (correction' : U' → Period × F → F) (finish' : U' → In → List (Event F Period) → Out) (u : U) (u' : U')
    (corrAgree : ∀ m, correction u m = correction' u' m) (cap : ℕ)
    (finAgree : ∀ result (events : List (Event F Period)), events.length ≤ cap → finish u result events = finish' u' result events)
    (P : OracleComp (advSpec Period (Period × F) G₁) In) (events : List (Event F Period)) (n : ℕ)
    (bound : P.IsTotalRollBound n) (room : events.length + n ≤ cap) :
    translate finalIndex correction finish u P events = translate finalIndex correction' finish' u' P events := by
  induction P generalizing events n with
  | pure result =>
    show translate finalIndex correction finish u (pure result) events = translate finalIndex correction' finish' u' (pure result) events
    rw [translate_pure, translate_pure, finAgree result events (by omega)]
  | queryBind t k ih =>
    rw [FreeM.isTotalRollBound_liftBind_iff] at bound
    rcases t with (n' | t) | m
    · rw [translate_random, translate_random]
      exact congrArg (OracleComp.queryBind _) (funext fun r => ih r events (n - 1) (bound.2 r) (by omega))
    · rw [translate_hash, translate_hash]
      exact congrArg (OracleComp.queryBind _) (funext fun h => ih h _ (n - 1) (bound.2 h) (by simp; omega))
    · rw [translate_sign, translate_sign, corrAgree]
      exact congrArg (OracleComp.queryBind _) (funext fun h => congrArg (OracleComp.queryBind _) (funext fun σ =>
        ih _ _ (n - 1) (bound.2 _) (by simp; omega)))
end Congruence

/-! ## Implementation -/

variable (cap : ℕ) (corrLaw : ∀ u m, correction u m = corr (proj u) m)
  (finLaw : ∀ u result (events : List (Event F Period)), events.length ≤ cap →
    finish u result events = fin (proj u) result (events.map (mark (proj u))))

/-- Machine states against residual wrapper programs. The inner program's query bound keeps
the event count within `cap`. -/
def Rel : D × Core M.State In E G₁ → OracleComp (advSpec Period (Period × F) G₁) Out → Prop
  | (d, .ready s marks), Q => ∃ (u : U) (P : OracleComp (advSpec Period (Period × F) G₁) In) (events : List (Event F Period)) (n : ℕ),
      proj u = d ∧ M.toDynSystem.behavior s = FreeM.toResumption P ∧ P.IsTotalRollBound n ∧ events.length + n ≤ cap ∧
      marks = (events ++ pendingEvent M (M.view s)).map (mark d) ∧ Q = translate finalIndex correction finish u P events
  | (d, .gotHash s h marks), Q => ∃ (u : U) (m : Period × F) (k : G₁ → OracleComp (advSpec Period (Period × F) G₁) In)
      (events : List (Event F Period)) (n : ℕ),
      proj u = d ∧ M.toDynSystem.behavior s = FreeM.toResumption (OracleComp.queryBind (spec := advSpec Period (Period × F) G₁) (.inr m) k) ∧
      (OracleComp.queryBind (spec := advSpec Period (Period × F) G₁) (.inr m) k).IsTotalRollBound n ∧ events.length + n ≤ cap ∧
      marks = (events ++ [Event.sign m]).map (mark d) ∧
      Q = OracleComp.queryBind (spec := advSpec Period (Period × F) G₁) (.inr m) fun σ =>
        translate finalIndex correction finish u (k (σ + correction u m • h)) (events ++ [Event.sign m])
  | (d, .final result marks), Q => ∃ (u : U) (events : List (Event F Period)), proj u = d ∧ events.length ≤ cap ∧
      marks = events.map (mark d) ∧ Q = translate finalIndex correction finish u (pure result) events
  | (d, .done result marks), Q => ∃ (u : U) (events : List (Event F Period)), proj u = d ∧ events.length ≤ cap ∧
      marks = events.map (mark d) ∧ Q = pure (finish u result events)

/-- Entering an inner state whose behavior is a bounded program lands in the relation. -/
theorem rel_enter (u : U) (s : M.State) (P : OracleComp (advSpec Period (Period × F) G₁) In)
    (events : List (Event F Period)) (n : ℕ) (hb : M.toDynSystem.behavior s = FreeM.toResumption P)
    (hn : P.IsTotalRollBound n) (room : events.length + n ≤ cap) :
    Rel M proj mark finalIndex correction finish cap (enter M mark (proj u) s (events.map (mark (proj u))))
      (translate finalIndex correction finish u P events) := by
  unfold enter
  rcases hv : M.view s with result | q
  · exact ⟨u, events, rfl, by omega, rfl, by rw [Machine.eq_pure_of_view_inl M hb hv]⟩
  · exact ⟨u, P, events, n, rfl, hb, hn, room, by rw [hv, List.map_append], rfl⟩

include corrLaw finLaw in
theorem steps : Machine.Steps (machine M split proj corr mark finalIndex fin)
    (Rel M proj mark finalIndex correction finish cap) := by
  rintro ⟨d, core⟩ Q hR
  cases core with
  | ready s marks =>
    obtain ⟨u, P, events, n, rfl, hb, hn, room, rfl, rfl⟩ := hR
    rcases hv : M.view s with result | ⟨(n' | t) | m, next⟩
    · obtain rfl := Machine.eq_pure_of_view_inl M hb hv
      refine Or.inr ⟨.inl (.inr (finalIndex result)),
        fun _ => (proj u, .done result ((events ++ pendingEvent M (M.view s)).map (mark (proj u)))), _, ?_,
        translate_pure _ _ _ _ _ _, fun _ => ⟨u, events, rfl, by omega, by simp [hv, pendingEvent], rfl⟩⟩
      simp [machine, step, readyStep, hv]
    · obtain ⟨k, rfl, hk⟩ := Machine.exists_liftBind_of_view_inr M hb hv
      rw [FreeM.isTotalRollBound_liftBind_iff] at hn
      refine Or.inr ⟨.inl (.inl n'), fun r => enter M mark (proj u) (next r) ((events ++ pendingEvent M (M.view s)).map (mark (proj u))), _, ?_,
        translate_random _ _ _ _ _ _ _, fun r => ?_⟩
      · simp [machine, step, readyStep, hv]
      · have := rel_enter M proj mark finalIndex correction finish cap u (next r) (k r) events (n - 1) (hk r) (hn.2 r) (by omega)
        simpa [hv, pendingEvent] using this
    · obtain ⟨k, rfl, hk⟩ := Machine.exists_liftBind_of_view_inr M hb hv
      rw [FreeM.isTotalRollBound_liftBind_iff] at hn
      refine Or.inr ⟨.inl (.inr t), fun h => enter M mark (proj u) (next h) ((events ++ pendingEvent M (M.view s)).map (mark (proj u))), _, ?_,
        translate_hash _ _ _ _ _ _ _, fun h => ?_⟩
      · simp [machine, step, readyStep, hv]
      · have := rel_enter M proj mark finalIndex correction finish cap u (next h) (k h) (events ++ [Event.hash t]) (n - 1) (hk h) (hn.2 h)
          (by simp; omega)
        simpa [hv, pendingEvent] using this
    · obtain ⟨k, rfl, hk⟩ := Machine.exists_liftBind_of_view_inr M hb hv
      refine Or.inr ⟨.inl (.inr m.1), fun h => (proj u, .gotHash s h ((events ++ pendingEvent M (M.view s)).map (mark (proj u)))), _, ?_,
        translate_sign _ _ _ _ _ _ _,
        fun h => ⟨u, m, k, events, n, rfl, hb, hn, room, by simp [hv, pendingEvent], rfl⟩⟩
      simp [machine, step, readyStep, hv]
  | gotHash s h marks =>
    obtain ⟨u, m, k, events, n, rfl, hb, hn, room, rfl, rfl⟩ := hR
    obtain ⟨next, hv, hk⟩ := Model.Machine.view_of_behavior_liftBind M hb
    rw [FreeM.isTotalRollBound_liftBind_iff] at hn
    refine Or.inr ⟨.inr m, fun σ => enter M mark (proj u) (next (σ + corr (proj u) m • h)) ((events ++ [Event.sign m]).map (mark (proj u))), _, ?_,
      rfl, fun σ => ?_⟩
    · simp [machine, step, hv]
    · rw [corrLaw]
      exact rel_enter M proj mark finalIndex correction finish cap u _ _ (events ++ [Event.sign m]) (n - 1) (hk _) (hn.2 _) (by simp; omega)
  | final result marks =>
    obtain ⟨u, events, rfl, room, rfl, rfl⟩ := hR
    refine Or.inr ⟨.inl (.inr (finalIndex result)), fun _ => (proj u, .done result (events.map (mark (proj u)))), _, ?_,
      translate_pure _ _ _ _ _ _, fun _ => ⟨u, events, rfl, room, rfl, rfl⟩⟩
    simp [machine, step]
  | done result marks =>
    obtain ⟨u, events, rfl, room, rfl, rfl⟩ := hR
    exact Or.inl ⟨fin (proj u) result (events.map (mark (proj u))), by simp [machine, step], by rw [finLaw u result events room]⟩

include corrLaw finLaw in
theorem implements (inner : α → OracleComp (advSpec Period (Period × F) G₁) In) (n : ℕ) (hM : M.Implements inner)
    (bound : ∀ a, (inner a).IsTotalRollBound n) (room : n ≤ cap) :
    (machine M split proj corr mark finalIndex fin).Implements
      fun u => translate finalIndex correction finish u (inner (split u)) [] :=
  Machine.implements_of_steps _ (steps M split proj corr mark finalIndex fin correction finish cap corrLaw finLaw) _ fun u =>
    rel_enter M proj mark finalIndex correction finish cap u _ _ [] n (hM (split u)) (bound _) (by simpa using room)

/-! ## Query budget -/

/-- Signing requests. -/
abbrev isSign (request : (ℕ ⊕ Period) ⊕ (Period × F)) : Prop := request.isRight = true

theorem isQueryBoundP_queryBind_iff {ι : Type} {spec : OracleSpec ι} {β : Type} (p : ι → Prop) [DecidablePred p]
    (t : ι) (k : spec.Range t → OracleComp spec β) (n : ℕ) :
    IsQueryBoundP (OracleComp.queryBind t k) p n ↔
      (¬ p t ∨ 0 < n) ∧ ∀ u, IsQueryBoundP (k u) p (if p t then n - 1 else n) := Iff.rfl

/-- The wrapper's depth: the inner depth, one extra hash per signing query, the final hash. -/
theorem translate_isTotalRollBound (u : U) (P : OracleComp (advSpec Period (Period × F) G₁) In)
    (events : List (Event F Period)) (n signs : ℕ) (hn : P.IsTotalRollBound n)
    (hs : IsQueryBoundP P isSign signs) :
    (translate finalIndex correction finish u P events).IsTotalRollBound (n + signs + 1) := by
  induction P generalizing events n signs with
  | pure result =>
    change FreeM.IsTotalRollBound (translate finalIndex correction finish u (pure result) events) _
    rw [translate_pure, FreeM.isTotalRollBound_liftBind_iff]
    exact ⟨by omega, fun _ => FreeM.isTotalRollBound_pure _ _⟩
  | queryBind t k ih =>
    rw [FreeM.isTotalRollBound_liftBind_iff] at hn
    rw [isQueryBoundP_queryBind_iff] at hs
    rcases t with (r | t) | m
    · rw [translate_random, FreeM.isTotalRollBound_liftBind_iff]
      refine ⟨by omega, fun r => (ih r events (n - 1) signs (hn.2 r) (by simpa [isSign] using hs.2 r)).mono (by omega)⟩
    · rw [translate_hash, FreeM.isTotalRollBound_liftBind_iff]
      refine ⟨by omega, fun h => (ih h _ (n - 1) signs (hn.2 h) (by simpa [isSign] using hs.2 h)).mono (by omega)⟩
    · have hsigns : 0 < signs := by simpa [isSign] using hs.1
      rw [translate_sign, FreeM.isTotalRollBound_liftBind_iff]
      refine ⟨by omega, fun h => ?_⟩
      rw [FreeM.isTotalRollBound_liftBind_iff]
      refine ⟨by omega, fun σ => (ih _ _ (n - 1) (signs - 1) (hn.2 _) (by simpa [isSign] using hs.2 _)).mono (by omega)⟩

include corrLaw finLaw in
/-- Bounded implementation of the wrapper from bounded implementation of the inner attacker
and a bound on its signing queries. -/
theorem implementsWithin (inner : α → OracleComp (advSpec Period (Period × F) G₁) In) (n signs : ℕ)
    (hM : M.ImplementsWithin inner n) (hs : ∀ a, IsQueryBoundP (inner a) isSign signs) (room : n ≤ cap) :
    (machine M split proj corr mark finalIndex fin).ImplementsWithin
      (fun u => translate finalIndex correction finish u (inner (split u)) []) (n + signs + 1) := by
  rw [implementsWithin_iff_implements_and_bound] at hM ⊢
  exact ⟨implements M split proj corr mark finalIndex fin correction finish cap corrLaw finLaw inner n hM.1 hM.2 room,
    fun u => translate_isTotalRollBound finalIndex correction finish u _ [] n signs (hM.2 _) (hs _)⟩

end SynchronizedPS.Wrapped
