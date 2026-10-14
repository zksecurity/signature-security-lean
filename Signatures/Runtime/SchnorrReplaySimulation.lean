import Signatures.Runtime.SchnorrReplayMachine

/-! Source-derived bounds for simulation with a real replay tape. These bounds apply
to adaptive programs and include the compiled product-store accessors. -/

open OracleComp

namespace Signatures.Runtime.Schnorr

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

def replayEvents (s : replayStore.Value (cryptoBase F G₁ G₂ K M)) : Nat := s.2.2.2.2.length

def replayFrame (cache : cacheStore.Value (cryptoBase F G₁ G₂ K M))
    (limit : Nat) (tape : List (Nat × F × Nat))
    (s : replayStore.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  s.1 = cache ∧ s.2.2.1 = limit ∧ s.2.2.2.1 = tape

theorem replayScalar_frame (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (tag : Bool) (cache : cacheStore.Value (cryptoBase F G₁ G₂ K M))
    (limit : Nat) (tape : List (Nat × F × Nat))
    (s : replayStore.Value (cryptoBase F G₁ G₂ K M)) (hs : replayFrame cache limit tape s)
    (out : Run F × replayStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support ((replayHandler cost sampling (.scalar tag) ()).run s)) :
    replayFrame cache limit tape out.2 ∧ replayEvents out.2 ≤ replayEvents s + 1 ∧
      out.1.steps ≤ scalarReplayPrice cost sampling tape.length := by
  rcases s with ⟨cache', cursor, limit', tape', events⟩
  rcases hs with ⟨rfl, rfl, rfl⟩
  have h := replayHandler_scalar_bound cost sampling tag cache' cursor limit' tape' events out hout
  exact ⟨by rw [h.2]; exact ⟨rfl, rfl, rfl⟩, by rw [h.2]; rfl, h.1⟩

theorem replayedHash_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (k : M × G₁) (g pk : G₁) (managed live : List ((M × G₁) × F))
    (tape : Replay.Mixed.store.Value (cryptoBase F G₁ G₂ K M)) :
    ((taggedHash.run (arithmetic F G₁ G₂ K M cost) (replayHandler cost sampling) (k, ())).run
      (((g, pk), managed, live), tape)) =
      (fun r => (⟨r.1.value.1, r.1.steps + cost.field + 57⟩,
        (((g, pk), r.1.value.2), r.2.2))) <$>
        (((managedGet (TaggedEffect.scalar true)).run (arithmetic F G₁ G₂ K M cost)
          (replayHandler cost sampling) (k, 0, managed, live, ())).run
            (((g, pk), managed, live), tape)) := by
  unfold taggedHash
  rw [hashProgram_run]
  simp only [StateT.run_bind, StateT.run_map,
    replayHandler_read (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    replayHandler_write (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    map_pure, pure_bind, bind_pure_comp]
  congr 1
  funext r
  congr 2
  omega

theorem replayedFinalHash_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (k : M × G₁) (g pk : G₁) (managed live : List ((M × G₁) × F))
    (tape : Replay.Mixed.store.Value (cryptoBase F G₁ G₂ K M)) :
    ((taggedFinalHash.run (arithmetic F G₁ G₂ K M cost) (replayHandler cost sampling) (k, ())).run
      (((g, pk), managed, live), tape)) =
      (fun r => (⟨r.1.value.1, r.1.steps + cost.field + 58⟩,
        (((g, pk), managed, r.1.value.2), r.2.2))) <$>
        (((cacheGetExpr hashEq (TaggedEffect.scalar true)).run (arithmetic F G₁ G₂ K M cost)
          (replayHandler cost sampling) (k, 0, live, ())).run
            (((g, pk), managed, live), tape)) := by
  unfold taggedFinalHash
  rw [finalHashProgram_run]
  simp only [StateT.run_bind, StateT.run_map,
    replayHandler_read (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    replayHandler_write (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    map_pure, pure_bind, bind_pure_comp]
  congr 1
  funext r
  congr 2
  omega

theorem replayedSign_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (msg : M) (g pk : G₁) (managed live : List ((M × G₁) × F))
    (tape : Replay.Mixed.store.Value (cryptoBase F G₁ G₂ K M)) :
    ((taggedSign.run (arithmetic F G₁ G₂ K M cost) (replayHandler cost sampling) (msg, ())).run
      (((g, pk), managed, live), tape)) =
      (fun r => (⟨r.1.value.1, r.1.steps + 63⟩,
        (((g, pk), r.1.value.2, live), r.2.2))) <$>
        (((signCached (TaggedEffect.scalar false)).run (arithmetic F G₁ G₂ K M cost)
          (replayHandler cost sampling) (msg, g, pk, managed, ())).run
            (((g, pk), managed, live), tape)) := by
  unfold taggedSign
  rw [signProgram_run]
  simp only [StateT.run_bind, StateT.run_map,
    replayHandler_read (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    replayHandler_write (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    map_pure, pure_bind, bind_pure_comp]
  congr 1
  funext r
  congr 2
  omega

theorem replayedHash_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (k : M × G₁) (g pk : G₁) (managed live : List ((M × G₁) × F))
    (cursor limit : Nat) (tape events : List (Nat × F × Nat))
    (out : Run F × replayStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support ((taggedHash.run (arithmetic F G₁ G₂ K M cost)
      (replayHandler cost sampling) (k, ())).run (((g, pk), managed, live), cursor, limit, tape, events))) :
    out.1.steps ≤ (managed.length + live.length) * (cost.messageEq + cost.point₁Eq + 37) +
      scalarReplayPrice cost sampling tape.length + cost.field + 150 ∧
      out.2.1.1 = (g, pk) ∧ out.2.1.2.1.length ≤ managed.length + 1 ∧
      out.2.1.2.2.length ≤ live.length + 1 ∧ out.2.2.2.1 = limit ∧
      out.2.2.2.2.1 = tape ∧ replayEvents out.2 ≤ events.length + 1 := by
  rw [replayedHash_run] at hout
  simp only [support_map, Set.mem_image] at hout
  obtain ⟨r, hr, rfl⟩ := hout
  have hd := replayScalar_frame (G₂ := G₂) (K := K) cost sampling true ((g, pk), managed, live) limit tape
    (((g, pk), managed, live), cursor, limit, tape, events) ⟨rfl, rfl, rfl⟩
  have hb := managedGet_bound cost (replayHandler cost sampling) (.scalar true)
    (scalarReplayPrice cost sampling tape.length) k 0 managed live
    (((g, pk), managed, live), cursor, limit, tape, events) (fun z hz => (hd z hz).2.2) r hr
  have hs := managedGet_state cost (replayHandler cost sampling) (.scalar true)
    (replayFrame ((g, pk), managed, live) limit tape) replayEvents k 0 managed live
    (((g, pk), managed, live), cursor, limit, tape, events) ⟨rfl, rfl, rfl⟩
    (fun z hz => ⟨(hd z hz).1, (hd z hz).2.1⟩) r hr
  exact ⟨by dsimp; omega, rfl, hb.2.1, hb.2.2, hs.1.2.1, hs.1.2.2, hs.2⟩

theorem replayedSign_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (msg : M) (g pk : G₁) (managed live : List ((M × G₁) × F))
    (cursor limit : Nat) (tape events : List (Nat × F × Nat))
    (out : Run (G₁ × F) × replayStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support ((taggedSign.run (arithmetic F G₁ G₂ K M cost)
      (replayHandler cost sampling) (msg, ())).run (((g, pk), managed, live), cursor, limit, tape, events))) :
    out.1.steps ≤ managed.length * (cost.messageEq + cost.point₁Eq + 37) +
      2 * scalarReplayPrice cost sampling tape.length + 2 * cost.scalar₁ + cost.group + 163 ∧
      out.2.1.1 = (g, pk) ∧ out.2.1.2.1.length ≤ managed.length + 1 ∧
      out.2.1.2.2 = live ∧ out.2.2.2.1 = limit ∧ out.2.2.2.2.1 = tape ∧
      replayEvents out.2 ≤ events.length + 2 := by
  rw [replayedSign_run] at hout
  simp only [support_map, Set.mem_image] at hout
  obtain ⟨r, hr, rfl⟩ := hout
  have hb := signCached_bound_of_invariant cost (replayHandler cost sampling) (.scalar false)
    (scalarReplayPrice cost sampling tape.length)
    (replayFrame ((g, pk), managed, live) limit tape) replayEvents
    (replayScalar_frame cost sampling false ((g, pk), managed, live) limit tape)
    msg g pk managed (((g, pk), managed, live), cursor, limit, tape, events)
    ⟨rfl, rfl, rfl⟩ r hr
  exact ⟨by dsimp; omega, rfl, hb.2.1, rfl, hb.2.2.1.2.1, hb.2.2.1.2.2, hb.2.2.2⟩

theorem replayedFinalHash_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (k : M × G₁) (g pk : G₁) (managed live : List ((M × G₁) × F))
    (cursor limit : Nat) (tape events : List (Nat × F × Nat))
    (out : Run F × replayStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support ((taggedFinalHash.run (arithmetic F G₁ G₂ K M cost)
      (replayHandler cost sampling) (k, ())).run (((g, pk), managed, live), cursor, limit, tape, events))) :
    out.1.steps ≤ live.length * (cost.messageEq + cost.point₁Eq + 37) +
      scalarReplayPrice cost sampling tape.length + cost.field + 89 ∧
      out.2.1.1 = (g, pk) ∧ out.2.1.2.1 = managed ∧
      out.2.1.2.2.length ≤ live.length + 1 ∧ out.2.2.2.1 = limit ∧
      out.2.2.2.2.1 = tape ∧ replayEvents out.2 ≤ events.length + 1 := by
  rw [replayedFinalHash_run] at hout
  simp only [support_map, Set.mem_image] at hout
  obtain ⟨r, hr, rfl⟩ := hout
  have hd := replayScalar_frame (G₂ := G₂) (K := K) cost sampling true
    ((g, pk), managed, live) limit tape (((g, pk), managed, live), cursor, limit, tape, events)
    ⟨rfl, rfl, rfl⟩
  have hb := cacheGetExpr_bound (arithmetic F G₁ G₂ K M cost)
    (replayHandler cost sampling) hashEq (.scalar true) (cost.messageEq + cost.point₁Eq + 15)
    (scalarReplayPrice cost sampling tape.length)
    (hashEq_steps_le (F := F) (G₂ := G₂) (K := K) cost) k 0 live
    (((g, pk), managed, live), cursor, limit, tape, events) (fun z hz => (hd z hz).2.2) r hr
  have hs := cacheGetExpr_state (arithmetic F G₁ G₂ K M cost)
    (replayHandler cost sampling) hashEq (.scalar true)
    (replayFrame ((g, pk), managed, live) limit tape) replayEvents k 0 live
    (((g, pk), managed, live), cursor, limit, tape, events) ⟨rfl, rfl, rfl⟩
    (fun z hz => ⟨(hd z hz).1, (hd z hz).2.1⟩) r hr
  refine ⟨?_, rfl, rfl, hb.2, hs.1.2.1, hs.1.2.2, hs.2⟩
  dsimp
  simp only [Nat.add_assoc, Nat.reduceAdd] at *
  omega

noncomputable def replaySourceHandler (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound : Nat) : HandlerM (cryptoBase F G₁ G₂ K M) (Command randomBound)
      (StateT (replayStore.Value (cryptoBase F G₁ G₂ K M)) ProbComp) :=
  routineHandler (arithmetic F G₁ G₂ K M cost) (replayHandler cost sampling)
    (taggedRoutines randomBound)

def replayPrices (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound length : Nat) (k : Fin 3) : Nat :=
  if k = 0 then
    (Finset.univ.sup fun n : Fin (randomBound + 1) => uniformReplayPrice cost sampling length n.val) + 5
  else if k = 1 then scalarReplayPrice cost sampling length + cost.field + 153
  else 2 * scalarReplayPrice cost sampling length + 2 * cost.scalar₁ + cost.group + 166

def eventAllowance (k : Fin 3) : Nat := if k = 2 then 2 else 1

set_option maxHeartbeats 400000 in
theorem replaySourceHandler_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound : Nat) {a b} (cmd : Command randomBound a b)
    (arg : a.Value (cryptoBase F G₁ G₂ K M))
    (s : replayStore.Value (cryptoBase F G₁ G₂ K M))
    (out : Run (b.Value (cryptoBase F G₁ G₂ K M)) × replayStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support ((replaySourceHandler cost sampling randomBound cmd arg).run s)) :
    out.2.1.1 = s.1.1 ∧ out.2.2.2.1 = s.2.2.1 ∧ out.2.2.2.2.1 = s.2.2.2.1 ∧
      cacheSize out.2.1 ≤ cacheSize s.1 + 1 ∧
      replayEvents out.2 ≤ replayEvents s + eventAllowance (kind cmd) ∧
      out.1.steps ≤ replayPrices cost sampling randomBound s.2.2.2.1.length (kind cmd) +
        2 * (cost.messageEq + cost.point₁Eq + 37) * cacheSize s.1 := by
  simp only [replaySourceHandler, routineHandler, bind_pure_comp, StateT.run_map,
    support_map, Set.mem_image] at hout
  obtain ⟨r, hr, rfl⟩ := hout
  rcases s with ⟨⟨⟨g, pk⟩, managed, live⟩, cursor, limit, tape, events⟩
  have hm : managed.length ≤ max managed.length live.length := Nat.le_max_left _ _
  have hl : live.length ≤ max managed.length live.length := Nat.le_max_right _ _
  cases cmd with
  | random n =>
    cases arg
    simp only [taggedRoutines, Program.run, Expr.run, bind_pure_comp, StateT.run_map,
      support_map, Set.mem_image] at hr
    obtain ⟨u, hu, rfl⟩ := hr
    have h := replayHandler_uniform_bound cost sampling n.val ((g, pk), managed, live)
      cursor limit tape events u hu
    have hn : uniformReplayPrice cost sampling tape.length n.val ≤
        Finset.univ.sup (fun n : Fin (randomBound + 1) =>
          uniformReplayPrice cost sampling tape.length n.val) :=
      Finset.le_sup (f := fun n : Fin (randomBound + 1) =>
        uniformReplayPrice cost sampling tape.length n.val) (Finset.mem_univ n)
    simp only [h.2, replayEvents, cacheSize, kind, eventAllowance, replayPrices,
      Fin.isValue, Fin.reduceEq, ite_false, ite_true, List.length_cons]
    refine ⟨trivial, trivial, trivial, Nat.le_succ _, le_rfl, ?_⟩
    omega
  | hash =>
    change r ∈ support ((taggedHash.run (arithmetic F G₁ G₂ K M cost)
      (replayHandler cost sampling) (arg, ())).run
        (((g, pk), managed, live), cursor, limit, tape, events)) at hr
    have h := replayedHash_bound (G₂ := G₂) (K := K) cost sampling arg g pk managed live
      cursor limit tape events r hr
    simp only [kind, eventAllowance, replayPrices, Fin.isValue, Fin.reduceEq, ite_false, ite_true]
    refine ⟨h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, ?_, h.2.2.2.2.2.2, ?_⟩
    · dsimp [cacheSize]
      omega
    · dsimp [cacheSize]
      nlinarith [h.1]
  | sign =>
    change r ∈ support ((taggedSign.run (arithmetic F G₁ G₂ K M cost)
      (replayHandler cost sampling) (arg, ())).run
        (((g, pk), managed, live), cursor, limit, tape, events)) at hr
    have h := replayedSign_bound (G₂ := G₂) (K := K) cost sampling arg g pk managed live
      cursor limit tape events r hr
    simp only [kind, eventAllowance, replayPrices, Fin.isValue, Fin.reduceEq, ite_false, ite_true]
    refine ⟨h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, ?_, h.2.2.2.2.2.2, ?_⟩
    · dsimp [cacheSize]
      rw [h.2.2.2.1]
      omega
    · dsimp [cacheSize]
      nlinarith [h.1]

/-- Both fresh and prefix-replaying passes use the same original source certificate.
Tape length is a fixed input to the bound, not a hidden runtime premise about the solver. -/
theorem replaySimulation_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound : Nat) (g pk : G₁) {Γ a} (source : Program CryptoOp (Command randomBound) Γ a)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      source env localTime queries)
    (cursor limit : Nat) (tape : List (Nat × F × Nat))
    (out : Run (a.Value (cryptoBase F G₁ G₂ K M)) × replayStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support ((((source.inline (taggedRoutines randomBound)).inline replayRoutines).run
      (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling replayStore) env).run
      (((g, pk), [], []), cursor, limit, tape, []))) :
    out.2.1.1 = (g, pk) ∧ out.2.2.2.1 = limit ∧ out.2.2.2.2.1 = tape ∧
      cacheSize out.2.1 ≤ ∑ k, queries k ∧
      replayEvents out.2 ≤ ∑ k, queries k * eventAllowance k ∧
      out.1.steps ≤ localTime +
        (∑ k, queries k * replayPrices cost sampling randomBound tape.length k) +
        2 * (cost.messageEq + cost.point₁Eq + 37) * (∑ k, queries k) ^ 2 := by
  rw [Program.inline_run, Program.inline_run] at hout
  let inv := fun s : replayStore.Value (cryptoBase F G₁ G₂ K M) =>
    s.1.1 = (g, pk) ∧ s.2.2.1 = limit ∧ s.2.2.2.1 = tape
  have hb := SourceBudget.linear_state_bound (arithmetic F G₁ G₂ K M cost)
    (replies randomBound) kind source env localTime queries hsource
    (replaySourceHandler cost sampling randomBound) (replayPrices cost sampling randomBound tape.length)
    (2 * (cost.messageEq + cost.point₁Eq + 37)) inv (fun s => cacheSize s.1) (by
      intro a b cmd arg s hs out hout
      have h := replaySourceHandler_bound (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
        cost sampling randomBound cmd arg s out hout
      exact ⟨⟨h.1.trans hs.1, h.2.1.trans hs.2.1, h.2.2.1.trans hs.2.2⟩,
        trivial, h.2.2.2.1, by simpa only [hs.2.2] using h.2.2.2.2.2⟩)
    (((g, pk), [], []), cursor, limit, tape, []) ⟨rfl, rfl, rfl⟩ rfl out hout
  have he := SourceBudget.state_growth (arithmetic F G₁ G₂ K M cost)
    (replies randomBound) kind source env localTime queries hsource
    (replaySourceHandler cost sampling randomBound) eventAllowance inv replayEvents (by
      intro a b cmd arg s hs out hout
      have h := replaySourceHandler_bound (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
        cost sampling randomBound cmd arg s out hout
      exact ⟨⟨h.1.trans hs.1, h.2.1.trans hs.2.1, h.2.2.1.trans hs.2.2⟩,
        trivial, h.2.2.2.2.1⟩)
    (((g, pk), [], []), cursor, limit, tape, []) ⟨rfl, rfl, rfl⟩ out hout
  exact ⟨hb.1.1, hb.1.2.1, hb.1.2.2, hb.2.1, by simpa [replayEvents] using he.2, hb.2.2⟩

end Signatures.Runtime.Schnorr
