import Signatures.Schnorr.Proofs.AGMRunSound

/-! Finite cache support and the collision probability of an honest signing nonce. -/

open OracleComp OracleSpec AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Schnorr.AGM.Reduction

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]

/-- A finite support bound for the functional cache, without assuming finite messages. -/
def CacheBound (s : State F G M) (k : Nat) : Prop :=
  ∃ keys : Finset (M × G), keys.card ≤ k ∧
    ∀ key e, s.cache key = some e → key ∈ keys

theorem cacheBound_empty : CacheBound ({} : State F G M) 0 :=
  ⟨∅, by simp, fun _ _ h => by cases h⟩

theorem CacheBound.mono {s : State F G M} {k l : Nat}
    (h : CacheBound s k) (hkl : k ≤ l) : CacheBound s l := by
  obtain ⟨keys, hk, hs⟩ := h
  exact ⟨keys, hk.trans hkl, hs⟩

theorem CacheBound.rejected {s : State F G M} {k : Nat}
    (h : CacheBound s k) : CacheBound (rejected s) k := h

variable [DecidableEq F] [DecidableEq G] [DecidableEq M]

theorem CacheBound.record {s : State F G M} {k : Nat} (h : CacheBound s k)
    (key : M × G) (a : Affine F) (c : F) : CacheBound (record s key a c) (k + 1) := by
  obtain ⟨keys, hk, hs⟩ := h
  refine ⟨insert key keys, (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hk 1), ?_⟩
  intro key' e he
  by_cases hh : key' = key
  · subst key'; exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (hs key' e (by simpa [Reduction.record, hh] using he))

omit [DecidableEq F] in
theorem CacheBound.signedState {s : State F G M} {k : Nat} (h : CacheBound s k)
    (g pk : G) (m : M) (c z : F) : CacheBound (signedState s g pk m c z) (k + 1) := by
  obtain ⟨keys, hk, hs⟩ := h
  refine ⟨insert (m, z • g - c • pk) keys,
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hk 1), ?_⟩
  intro key e he
  by_cases hh : key = (m, z • g - c • pk)
  · subst key; exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    apply hs key e
    cases hc : s.cache (m, z • g - c • pk) <;>
      simpa [Reduction.signedState, hc, hh] using he

variable [SampleableType F]

theorem CacheBound.read {s : State F G M} {k : Nat} (h : CacheBound s k)
    (key : M × G) (a : Affine F) (c : F) (t : State F G M)
    (ht : (c, t) ∈ support ((read key a).run s)) : CacheBound t (k + 1) := by
  cases hc : s.cache key with
  | some e =>
      simp only [Reduction.read, StateT.run, hc, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at ht
      rcases ht with ⟨rfl, rfl⟩
      exact h.mono (Nat.le_succ _)
  | none =>
      simp only [Reduction.read, StateT.run, hc, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at ht
      obtain ⟨c', _, rfl, rfl⟩ := ht
      exact h.record key a c

omit [DecidableEq F] [DecidableEq G] [DecidableEq M] in
/-- An injective scalar action gives at most one colliding nonce per cached key. -/
theorem nonce_collision [Fintype F] (g : G)
    (hg : Function.Injective (fun x : F => x • g))
    (s : State F G M) (k : Nat) (hk : CacheBound s k) (m : M) :
    Pr[fun r => s.cache (m, r • g) ≠ none | $ᵗ F] ≤
      (k : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  classical
  obtain ⟨keys, hkeys, hs⟩ := hk
  rw [probEvent_uniformSample, div_eq_mul_inv]
  gcongr
  apply le_trans _ hkeys
  apply Finset.card_le_card_of_injOn (fun r : F => (m, r • g))
  · intro r hr
    have hr' := (Finset.mem_filter.mp hr).2
    obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hr'
    exact hs _ e he
  · intro r hr t ht hrt
    exact hg (Prod.mk.inj hrt).2

end Schnorr.AGM.Reduction
