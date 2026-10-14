import Signatures.Runtime.SeedTapeMachine

/-! Source-derived execution budgets for the family-indexed seed machine.
The tape only shrinks; cache growth is charged from the source query budget. -/

open OracleComp

namespace Signatures.Runtime.Schnorr.SeedTape

theorem scalarPrice_mono (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {a b : Nat} (h : a ≤ b) : scalarPrice cost sampling a ≤ scalarPrice cost sampling b := by
  have hm := Nat.mul_le_mul_right (cost.natOp + 70) h
  dsimp [scalarPrice, drawBound]
  omega

theorem uniformPrice_mono (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (n : Nat) {a b : Nat} (h : a ≤ b) :
    uniformPrice cost sampling a n ≤ uniformPrice cost sampling b n := by
  have hm := Nat.mul_le_mul_right (cost.natOp + 70) h
  dsimp [uniformPrice, drawBound]
  omega

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

def frame (cache : cacheStore.Value (cryptoBase F G₁ G₂ K M)) (length : Nat)
    (s : machineStore.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  s.1 = cache ∧ s.2.length ≤ length

theorem scalar_frame (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (live : Bool) (cache : cacheStore.Value (cryptoBase F G₁ G₂ K M)) (length : Nat)
    (s : machineStore.Value (cryptoBase F G₁ G₂ K M)) (hs : frame cache length s)
    (out : Run F × machineStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support ((handler cost sampling (.scalar live) ()).run s)) :
    frame cache length out.2 ∧ (0 : Nat) ≤ 0 + 1 ∧
      out.1.steps ≤ scalarPrice cost sampling length := by
  have h := handler_scalar_bound cost sampling live s.1 s.2 out hout
  exact ⟨⟨h.2.1.trans hs.1, h.2.2.trans hs.2⟩, by omega,
    h.1.trans (scalarPrice_mono cost sampling hs.2)⟩

theorem hash_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (k : M × G₁) (g pk : G₁) (managed live : List ((M × G₁) × F)) (tape : List (TapeCell F)) :
    ((taggedHash.run (arithmetic F G₁ G₂ K M cost) (handler cost sampling) (k, ())).run
      (((g, pk), managed, live), tape)) =
      (fun r => (⟨r.1.value.1, r.1.steps + cost.field + 57⟩,
        (((g, pk), r.1.value.2), r.2.2))) <$>
        (((managedGet (TaggedEffect.scalar true)).run (arithmetic F G₁ G₂ K M cost)
          (handler cost sampling) (k, 0, managed, live, ())).run (((g, pk), managed, live), tape)) := by
  unfold taggedHash
  rw [hashProgram_run]
  simp only [StateT.run_bind, StateT.run_map,
    handler_read (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    handler_write (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    map_pure, pure_bind, bind_pure_comp]
  congr 1
  funext r
  congr 2
  omega

theorem finalHash_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (k : M × G₁) (g pk : G₁) (managed live : List ((M × G₁) × F)) (tape : List (TapeCell F)) :
    ((taggedFinalHash.run (arithmetic F G₁ G₂ K M cost) (handler cost sampling) (k, ())).run
      (((g, pk), managed, live), tape)) =
      (fun r => (⟨r.1.value.1, r.1.steps + cost.field + 58⟩,
        (((g, pk), managed, r.1.value.2), r.2.2))) <$>
        (((cacheGetExpr hashEq (TaggedEffect.scalar true)).run (arithmetic F G₁ G₂ K M cost)
          (handler cost sampling) (k, 0, live, ())).run (((g, pk), managed, live), tape)) := by
  unfold taggedFinalHash
  rw [finalHashProgram_run]
  simp only [StateT.run_bind, StateT.run_map,
    handler_read (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    handler_write (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    map_pure, pure_bind, bind_pure_comp]
  congr 1
  funext r
  congr 2
  omega

theorem sign_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (msg : M) (g pk : G₁) (managed live : List ((M × G₁) × F)) (tape : List (TapeCell F)) :
    ((taggedSign.run (arithmetic F G₁ G₂ K M cost) (handler cost sampling) (msg, ())).run
      (((g, pk), managed, live), tape)) =
      (fun r => (⟨r.1.value.1, r.1.steps + 63⟩,
        (((g, pk), r.1.value.2, live), r.2.2))) <$>
        (((signCached (TaggedEffect.scalar false)).run (arithmetic F G₁ G₂ K M cost)
          (handler cost sampling) (msg, g, pk, managed, ())).run (((g, pk), managed, live), tape)) := by
  unfold taggedSign
  rw [signProgram_run]
  simp only [StateT.run_bind, StateT.run_map,
    handler_read (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    handler_write (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    map_pure, pure_bind, bind_pure_comp]
  congr 1
  funext r
  congr 2
  omega

theorem hash_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (k : M × G₁) (g pk : G₁) (managed live : List ((M × G₁) × F))
    (tape : List (TapeCell F)) (length : Nat) (htape : tape.length ≤ length)
    (out : Run F × machineStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support ((taggedHash.run (arithmetic F G₁ G₂ K M cost)
      (handler cost sampling) (k, ())).run (((g, pk), managed, live), tape))) :
    out.1.steps ≤ (managed.length + live.length) * (cost.messageEq + cost.point₁Eq + 37) +
      scalarPrice cost sampling length + cost.field + 150 ∧
      out.2.1.1 = (g, pk) ∧ out.2.1.2.1.length ≤ managed.length + 1 ∧
      out.2.1.2.2.length ≤ live.length + 1 ∧ out.2.2.length ≤ length := by
  rw [hash_run] at hout
  simp only [support_map, Set.mem_image] at hout
  obtain ⟨r, hr, rfl⟩ := hout
  have hd := scalar_frame (G₂ := G₂) (K := K) cost sampling true ((g, pk), managed, live) length
    (((g, pk), managed, live), tape) ⟨rfl, htape⟩
  have hb := managedGet_bound cost (handler cost sampling) (.scalar true)
    (scalarPrice cost sampling length) k 0 managed live (((g, pk), managed, live), tape)
    (fun z hz => (hd z hz).2.2) r hr
  have hs := managedGet_state cost (handler cost sampling) (.scalar true)
    (frame ((g, pk), managed, live) length) (fun _ => 0) k 0 managed live
    (((g, pk), managed, live), tape) ⟨rfl, htape⟩ (fun z hz => ⟨(hd z hz).1, (hd z hz).2.1⟩) r hr
  exact ⟨by dsimp; omega, rfl, hb.2.1, hb.2.2, hs.1.2⟩

theorem sign_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (msg : M) (g pk : G₁) (managed live : List ((M × G₁) × F))
    (tape : List (TapeCell F)) (length : Nat) (htape : tape.length ≤ length)
    (out : Run (G₁ × F) × machineStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support ((taggedSign.run (arithmetic F G₁ G₂ K M cost)
      (handler cost sampling) (msg, ())).run (((g, pk), managed, live), tape))) :
    out.1.steps ≤ managed.length * (cost.messageEq + cost.point₁Eq + 37) +
      2 * scalarPrice cost sampling length + 2 * cost.scalar₁ + cost.group + 163 ∧
      out.2.1.1 = (g, pk) ∧ out.2.1.2.1.length ≤ managed.length + 1 ∧
      out.2.1.2.2 = live ∧ out.2.2.length ≤ length := by
  rw [sign_run] at hout
  simp only [support_map, Set.mem_image] at hout
  obtain ⟨r, hr, rfl⟩ := hout
  have hb := signCached_bound_of_invariant cost (handler cost sampling) (.scalar false)
    (scalarPrice cost sampling length) (frame ((g, pk), managed, live) length) (fun _ => 0)
    (scalar_frame cost sampling false ((g, pk), managed, live) length)
    msg g pk managed (((g, pk), managed, live), tape) ⟨rfl, htape⟩ r hr
  exact ⟨by dsimp; omega, rfl, hb.2.1, rfl, hb.2.2.1.2⟩

theorem finalHash_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (k : M × G₁) (g pk : G₁) (managed live : List ((M × G₁) × F))
    (tape : List (TapeCell F)) (length : Nat) (htape : tape.length ≤ length)
    (out : Run F × machineStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support ((taggedFinalHash.run (arithmetic F G₁ G₂ K M cost)
      (handler cost sampling) (k, ())).run (((g, pk), managed, live), tape))) :
    out.1.steps ≤ live.length * (cost.messageEq + cost.point₁Eq + 37) +
      scalarPrice cost sampling length + cost.field + 89 ∧
      out.2.1.1 = (g, pk) ∧ out.2.1.2.1 = managed ∧
      out.2.1.2.2.length ≤ live.length + 1 ∧ out.2.2.length ≤ length := by
  rw [finalHash_run] at hout
  simp only [support_map, Set.mem_image] at hout
  obtain ⟨r, hr, rfl⟩ := hout
  have hd := scalar_frame (G₂ := G₂) (K := K) cost sampling true ((g, pk), managed, live) length
    (((g, pk), managed, live), tape) ⟨rfl, htape⟩
  have hb := cacheGetExpr_bound (arithmetic F G₁ G₂ K M cost)
    (handler cost sampling) hashEq (.scalar true) (cost.messageEq + cost.point₁Eq + 15)
    (scalarPrice cost sampling length) (hashEq_steps_le (F := F) (G₂ := G₂) (K := K) cost)
    k 0 live (((g, pk), managed, live), tape) (fun z hz => (hd z hz).2.2) r hr
  have hs := cacheGetExpr_state (arithmetic F G₁ G₂ K M cost) (handler cost sampling)
    hashEq (.scalar true) (frame ((g, pk), managed, live) length) (fun _ => 0) k 0 live
    (((g, pk), managed, live), tape) ⟨rfl, htape⟩ (fun z hz => ⟨(hd z hz).1, (hd z hz).2.1⟩) r hr
  refine ⟨?_, rfl, rfl, hb.2, hs.1.2⟩
  dsimp
  simp only [Nat.add_assoc, Nat.reduceAdd] at *
  omega

noncomputable def sourceHandler (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound : Nat) : HandlerM (cryptoBase F G₁ G₂ K M) (Command randomBound)
      (StateT (machineStore.Value (cryptoBase F G₁ G₂ K M)) ProbComp) :=
  routineHandler (arithmetic F G₁ G₂ K M cost) (handler cost sampling) (taggedRoutines randomBound)

def sourcePrices (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound length : Nat) (k : Fin 3) : Nat :=
  if k = 0 then
    (Finset.univ.sup fun n : Fin (randomBound + 1) => uniformPrice cost sampling length n.val) + 5
  else if k = 1 then scalarPrice cost sampling length + cost.field + 153
  else 2 * scalarPrice cost sampling length + 2 * cost.scalar₁ + cost.group + 166

set_option maxHeartbeats 400000 in
theorem sourceHandler_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound length : Nat) {a b} (cmd : Command randomBound a b)
    (arg : a.Value (cryptoBase F G₁ G₂ K M))
    (s : machineStore.Value (cryptoBase F G₁ G₂ K M)) (htape : s.2.length ≤ length)
    (out : Run (b.Value (cryptoBase F G₁ G₂ K M)) × machineStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support ((sourceHandler cost sampling randomBound cmd arg).run s)) :
    out.2.1.1 = s.1.1 ∧ out.2.2.length ≤ length ∧
      cacheSize out.2.1 ≤ cacheSize s.1 + 1 ∧
      out.1.steps ≤ sourcePrices cost sampling randomBound length (kind cmd) +
        2 * (cost.messageEq + cost.point₁Eq + 37) * cacheSize s.1 := by
  simp only [sourceHandler, routineHandler, bind_pure_comp, StateT.run_map,
    support_map, Set.mem_image] at hout
  obtain ⟨r, hr, rfl⟩ := hout
  rcases s with ⟨⟨⟨g, pk⟩, managed, live⟩, tape⟩
  have hm : managed.length ≤ max managed.length live.length := Nat.le_max_left _ _
  have hl : live.length ≤ max managed.length live.length := Nat.le_max_right _ _
  cases cmd with
  | random n =>
      cases arg
      simp only [taggedRoutines, Program.run, Expr.run, bind_pure_comp, StateT.run_map,
        support_map, Set.mem_image] at hr
      obtain ⟨u, hu, rfl⟩ := hr
      have h := handler_uniform_bound cost sampling n.val ((g, pk), managed, live) tape u hu
      have hn : uniformPrice cost sampling length n.val ≤ Finset.univ.sup
          (fun n : Fin (randomBound + 1) => uniformPrice cost sampling length n.val) :=
        Finset.le_sup (f := fun n : Fin (randomBound + 1) => uniformPrice cost sampling length n.val)
          (Finset.mem_univ n)
      have hc := h.1.trans (uniformPrice_mono cost sampling n.val htape)
      simp only [kind, sourcePrices, Fin.isValue, Fin.reduceEq, ite_true]
      refine ⟨congrArg Prod.fst h.2.1, h.2.2.trans htape, ?_, ?_⟩
      · rw [h.2.1]; exact Nat.le_succ _
      · omega
  | hash =>
      change r ∈ support ((taggedHash.run (arithmetic F G₁ G₂ K M cost)
        (handler cost sampling) (arg, ())).run (((g, pk), managed, live), tape)) at hr
      have h := hash_bound (G₂ := G₂) (K := K) cost sampling arg g pk managed live tape length htape r hr
      simp only [kind, sourcePrices, Fin.isValue, Fin.reduceEq, ite_false, ite_true]
      refine ⟨h.2.1, h.2.2.2.2, ?_, ?_⟩
      · dsimp [cacheSize]; omega
      · dsimp [cacheSize]; nlinarith [h.1]
  | sign =>
      change r ∈ support ((taggedSign.run (arithmetic F G₁ G₂ K M cost)
        (handler cost sampling) (arg, ())).run (((g, pk), managed, live), tape)) at hr
      have h := sign_bound (G₂ := G₂) (K := K) cost sampling arg g pk managed live tape length htape r hr
      simp only [kind, sourcePrices, Fin.isValue, Fin.reduceEq, ite_false]
      refine ⟨h.2.1, h.2.2.2.2, ?_, ?_⟩
      · dsimp [cacheSize]; rw [h.2.2.2.1]; omega
      · dsimp [cacheSize]; nlinarith [h.1]

/-- The original all-reply source budget bounds the compiled execution. The
initial seed length is an explicit input; no finished-reduction runtime is assumed. -/
theorem simulation_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound : Nat) (g pk : G₁) {Γ a} (source : Program CryptoOp (Command randomBound) Γ a)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      source env localTime queries) (tape : List (TapeCell F))
    (out : Run (a.Value (cryptoBase F G₁ G₂ K M)) × machineStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support ((((source.inline (taggedRoutines randomBound)).inline routines).run
      (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling machineStore) env).run
      (((g, pk), [], []), tape))) :
    out.2.1.1 = (g, pk) ∧ out.2.2.length ≤ tape.length ∧
      cacheSize out.2.1 ≤ ∑ k, queries k ∧
      out.1.steps ≤ localTime + (∑ k, queries k * sourcePrices cost sampling randomBound tape.length k) +
        2 * (cost.messageEq + cost.point₁Eq + 37) * (∑ k, queries k) ^ 2 := by
  rw [Program.inline_run, Program.inline_run] at hout
  let inv := fun s : machineStore.Value (cryptoBase F G₁ G₂ K M) =>
    s.1.1 = (g, pk) ∧ s.2.length ≤ tape.length
  have hb := SourceBudget.linear_state_bound (arithmetic F G₁ G₂ K M cost)
    (replies randomBound) kind source env localTime queries hsource
    (sourceHandler cost sampling randomBound) (sourcePrices cost sampling randomBound tape.length)
    (2 * (cost.messageEq + cost.point₁Eq + 37)) inv (fun s => cacheSize s.1) (by
      intro a b cmd arg s hs out hout
      have h := sourceHandler_bound (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
        cost sampling randomBound tape.length cmd arg s hs.2 out hout
      exact ⟨⟨h.1.trans hs.1, h.2.1⟩, trivial, h.2.2.1, h.2.2.2⟩)
    (((g, pk), [], []), tape) ⟨rfl, le_rfl⟩ rfl out hout
  exact ⟨hb.1.1, hb.1.2, hb.2.1, hb.2.2⟩

end Signatures.Runtime.Schnorr.SeedTape
