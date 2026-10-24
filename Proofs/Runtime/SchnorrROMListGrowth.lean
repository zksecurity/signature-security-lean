import Proofs.Runtime.SchnorrROMListPass

/-! Encountered-cache capacities for arbitrary adaptive Schnorr ROM callers.
Private random queries do not grow either cache. Hash queries add at most one
entry to each cache; signing adds at most one managed entry. The final live
verification query adds at most one live entry. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.ListROM

def managedCharge {G M : Type} : (Nat ⊕ (M × G)) ⊕ M → Nat
  | .inl (.inl _) => 0
  | .inl (.inr _) | .inr _ => 1

def liveCharge {G M : Type} : (Nat ⊕ (M × G)) ⊕ M → Nat
  | .inl (.inr _) => 1
  | _ => 0

def Growth {F G M : Type}
    (before after : (G × G) × List ((M × G) × F) × List ((M × G) × F))
    (managedAdded liveAdded : Nat) : Prop :=
  after.1 = before.1 ∧ after.2.1.length ≤ before.2.1.length + managedAdded ∧
    after.2.2.length ≤ before.2.2.length + liveAdded

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem handler_growth (i : (Nat ⊕ (M × G₁)) ⊕ M)
    (state : cacheStore.Value (cryptoBase F G₁ G₂ K M))
    (out : (FiatShamir.cmaOracleSpec M G₁ F F).Range i × cacheStore.Value (cryptoBase F G₁ G₂ K M))
    (h : out ∈ support ((handler i).run state)) :
    Growth state out.2 (managedCharge i) (liveCharge i) := by
  rcases state with ⟨⟨g, pk⟩, managed, live⟩
  rcases i with (n | k) | msg
  · simp only [handler, StateT.run, support_map] at h
    obtain ⟨r, _, rfl⟩ := h
    exact ⟨rfl, le_rfl, le_rfl⟩
  · change out ∈ support (simulateQ (Replay.expandPrivate privateImpl)
      ((taggedHash.denote (arithmetic F G₁ G₂ K M PrimitiveCosts.unit) taggedSemantics (k, ())).run
        ((g, pk), managed, live))) at h
    rw [support_expandPrivate, taggedHash_denote] at h
    cases hm : cacheMap managed k with
    | some c =>
        simp only [hm, support_pure, Set.mem_singleton_iff] at h
        subst out
        exact ⟨rfl, by dsimp only [List.length_cons, managedCharge, liveCharge]; omega, by dsimp only [List.length_cons, managedCharge, liveCharge]; omega⟩
    | none =>
        simp only [hm] at h
        cases hl : cacheMap live k with
        | some c =>
            simp only [hl, map_pure, support_pure, Set.mem_singleton_iff] at h
            subst out
            exact ⟨rfl, by dsimp only [List.length_cons, managedCharge, liveCharge]; omega, by dsimp only [List.length_cons, managedCharge, liveCharge]; omega⟩
        | none =>
            simp only [hl, support_map] at h
            obtain ⟨p, ⟨c, _, rfl⟩, rfl⟩ := h
            exact ⟨rfl, by dsimp only [List.length_cons, managedCharge, liveCharge]; omega, by dsimp only [List.length_cons, managedCharge, liveCharge]; omega⟩
  · change out ∈ support (simulateQ (Replay.expandPrivate privateImpl)
      ((taggedSign.denote (arithmetic F G₁ G₂ K M PrimitiveCosts.unit) taggedSemantics (msg, ())).run
        ((g, pk), managed, live))) at h
    rw [support_expandPrivate, taggedSign_denote] at h
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨c, _, z, _, rfl⟩ := h
    refine ⟨rfl, ?_, le_rfl⟩
    exact cacheProgram_length (val := scalar) (arithmetic F G₁ G₂ K M PrimitiveCosts.unit) hashEq
      (hashEq_value (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) PrimitiveCosts.unit) (msg, z • g - c • pk) c managed

theorem final_growth (k : M × G₁)
    (state : cacheStore.Value (cryptoBase F G₁ G₂ K M))
    (out : F × cacheStore.Value (cryptoBase F G₁ G₂ K M))
    (h : out ∈ support ((finalHash k).run state)) : Growth state out.2 0 1 := by
  rcases state with ⟨⟨g, pk⟩, managed, live⟩
  change out ∈ support (simulateQ (Replay.expandPrivate privateImpl)
    ((taggedFinalHash.denote (arithmetic F G₁ G₂ K M PrimitiveCosts.unit) taggedSemantics (k, ())).run
      ((g, pk), managed, live))) at h
  rw [support_expandPrivate, taggedFinalHash_denote] at h
  cases hl : cacheMap live k with
  | some c =>
      simp only [hl, map_pure, support_pure, Set.mem_singleton_iff] at h
      subst out
      exact ⟨rfl, le_rfl, by dsimp only [List.length_cons, managedCharge, liveCharge]; omega⟩
  | none =>
      simp only [hl, support_map] at h
      obtain ⟨p, ⟨c, _, rfl⟩, rfl⟩ := h
      exact ⟨rfl, le_rfl, by dsimp only [List.length_cons, managedCharge, liveCharge]; omega⟩

theorem simulate_growth {A : Type}
    (main : OracleComp (FiatShamir.cmaOracleSpec M G₁ F F) A) (qS qH : Nat)
    (queries : FiatShamir.signHashQueryBound (M := M) (oa := main) qS qH)
    (state : cacheStore.Value (cryptoBase F G₁ G₂ K M))
    (out : A × cacheStore.Value (cryptoBase F G₁ G₂ K M))
    (h : out ∈ support ((simulateQ handler main).run state)) :
    Growth state out.2 (qS + qH) qH := by
  induction main using OracleComp.inductionOn generalizing qS qH state out with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h
      subst out
      exact ⟨rfl, by dsimp only; omega, by dsimp only; omega⟩
  | query_bind i next ih =>
      simp only [FiatShamir.signHashQueryBound, isQueryBoundP_query_bind_iff] at queries
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at h
      obtain ⟨step, hs, hrest⟩ := h
      have hg := handler_growth (G₂ := G₂) (K := K) i state step hs
      rcases i with (n | k) | msg
      all_goals dsimp only [Growth, managedCharge, liveCharge] at hg
      · have ht := ih step.1 qS qH ⟨queries.1.2 _, queries.2.2 _⟩ step.2 out hrest
        exact ⟨ht.1.trans hg.1, by have := ht.2.1; have := hg.2.1; omega,
          by have := ht.2.2; have := hg.2.2; omega⟩
      · have hpos : 0 < qH := by simpa using queries.2.1
        have ht := ih step.1 qS (qH - 1) ⟨queries.1.2 _, queries.2.2 _⟩ step.2 out hrest
        exact ⟨ht.1.trans hg.1, by have := ht.2.1; have := hg.2.1; omega,
          by have := ht.2.2; have := hg.2.2; omega⟩
      · have hpos : 0 < qS := by simpa using queries.1.1
        have ht := ih step.1 (qS - 1) qH ⟨queries.1.2 _, queries.2.2 _⟩ step.2 out hrest
        exact ⟨ht.1.trans hg.1, by have := ht.2.1; have := hg.2.1; omega,
          by have := ht.2.2; have := hg.2.2; omega⟩

theorem pass_growth (main : OracleComp (FiatShamir.cmaOracleSpec M G₁ F F) (M × G₁ × F))
    (qS qH : Nat) (queries : FiatShamir.signHashQueryBound (M := M) (oa := main) qS qH)
    (state : cacheStore.Value (cryptoBase F G₁ G₂ K M))
    (out : cachePassOutput.Value (cryptoBase F G₁ G₂ K M))
    (h : out ∈ support ((pass main).run state)) : Growth state out.2 (qS + qH) (qH + 1) := by
  simp only [pass, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at h
  obtain ⟨first, hf, last, hl, rfl⟩ := h
  have a := simulate_growth main qS qH queries state first hf
  have b := final_growth (first.1.1, first.1.2.1) first.2 last hl
  exact ⟨b.1.trans a.1, by have := a.2.1; have := b.2.1; dsimp only; omega,
    by have := a.2.2; have := b.2.2; dsimp only; omega⟩

/-- The concrete capacities used when either fork pass starts with empty
managed and live caches. No message/group-domain finiteness is required. -/
theorem pass_capacities (main : OracleComp (FiatShamir.cmaOracleSpec M G₁ F F) (M × G₁ × F))
    (qS qH : Nat) (queries : FiatShamir.signHashQueryBound (M := M) (oa := main) qS qH)
    (g pk : G₁) (out : cachePassOutput.Value (cryptoBase F G₁ G₂ K M))
    (h : out ∈ support ((pass main).run ((g, pk), [], []))) :
    out.2.1 = (g, pk) ∧ out.2.2.1.length ≤ qS + qH ∧ out.2.2.2.length ≤ qH + 1 := by
  simpa only [Growth, List.length_nil, Nat.zero_add] using
    pass_growth main qS qH queries ((g, pk), [], []) out h

end Signatures.Runtime.Schnorr.ListROM
