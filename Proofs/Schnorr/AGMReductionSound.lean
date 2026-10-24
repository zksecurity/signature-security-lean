import Proofs.Schnorr.AGMReduction

/-! Support invariants for the AGM reduction's recorded representations. -/

open OracleComp OracleSpec AlgebraicGroupModel.Interaction

namespace Schnorr.AGM.Reduction

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]

/-- Every read preserves the received basis and signing history and returns the
challenge of the retained cache entry. Its representation is fixed on a miss. -/
theorem read_spec (g pk : G) (s : State F G M) (hs : s.Valid g pk)
    (key : M × G) (a : Affine F) (ha : a.eval g pk = key.2)
    (c : F) (s' : State F G M) (h : (c, s') ∈ support ((read key a).run s)) :
    s'.Valid g pk ∧ s'.representations = s.representations ∧
      s'.signed = s.signed ∧ s'.malformed = s.malformed ∧
      ∃ e, s'.cache key = some e ∧ e.challenge = c := by
  cases hc : s.cache key with
  | some e =>
      simp only [read, StateT.run, hc, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨hs, rfl, rfl, rfl, e, hc, rfl⟩
  | none =>
      simp only [read, StateT.run, hc] at h
      change (c, s') ∈ support (do let d ← $ᵗ F; pure (d, record s key a d)) at h
      rw [mem_support_bind_iff] at h
      obtain ⟨d, _, hd⟩ := h
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hd
      rcases hd with ⟨rfl, rfl⟩
      exact ⟨record_valid g pk s hs key a ha c, rfl, rfl, rfl,
        ⟨c, some a⟩, by simp [record], rfl⟩

omit [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F] in
/-- Freshness excludes simulator-programmed entries. A valid accepting signature
therefore extracts from the first live hash representation whenever bad is false. -/
theorem cached_extract (g : G) (hg : Function.Injective (fun x : F => x • g))
    (x : F) (s : State F G M) (hs : s.Valid g (x • g))
    (m : M) (R : G) (c z : F) (e : Entry F)
    (he : s.cache (m, R) = some e) (hc : e.challenge = c)
    (hfresh : m ∉ s.signed) (hv : z • g = R + c • (x • g)) (hb : s.bad = false) :
    (match e.representation with
      | some a => (z - a.constant) / (a.secret + c)
      | none => 0) = x := by
  have h := hs (m, R) e he
  cases hr : e.representation with
  | none => exact (hfresh (by simpa only [hr] using h)).elim
  | some a =>
      simp only [hr] at h ⊢
      apply Schnorr.AGM.extract g hg x c z a
      · simpa only [h.1] using hv
      · simpa only [hc] using h.2 hb

/-- The final hash query participates in the same first-representation rule. -/
theorem finish_sound (g : G) (hg : Function.Injective (fun x : F => x • g))
    (x : F) (s : State F G M) (hs : s.Valid g (x • g))
    (out : Explained F (M × F) (Group G))
    (hout : out.Valid (representedBasis g (x • g) s.representations))
    (answer : Bool × F) (s' : State F G M)
    (h : (answer, s') ∈ support ((finish g (x • g) out).run s))
    (hwin : answer.1 = true) (hbad : s'.bad = false) : answer.2 = x := by
  cases hgroups : out.value.groups () with
  | nil =>
      simp [finish, hgroups, StateT.run_pure] at h
      rw [h.1] at hwin
      cases hwin
  | cons R rest =>
      cases rest with
      | cons R' rest =>
          simp [finish, hgroups, StateT.run_pure] at h
          rw [h.1] at hwin
          cases hwin
      | nil =>
          obtain ⟨coeff, hcoeff, _, heval⟩ :=
            valid_singleton g (x • g) R s.representations out hout hgroups
          simp only [finish, hgroups, hcoeff, StateT.run_bind, StateT.run_get,
            pure_bind, StateT.run_pure] at h
          rw [mem_support_bind_iff] at h
          obtain ⟨⟨c, t⟩, ht, hresult⟩ := h
          simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hresult
          rcases hresult with ⟨ha, rfl⟩
          subst answer
          have hread := read_spec g (x • g) s hs
            (out.value.data.1, R) (flatten coeff s.representations) heval c s' ht
          obtain ⟨e, he, hc⟩ := hread.2.2.2.2
          have hw : out.value.data.1 ∉ s'.signed ∧
              out.value.data.2 • g = R + c • (x • g) := by
            simpa using (Bool.and_eq_true_iff.mp hwin).2
          simp only [he]
          have hsol := cached_extract g hg x s' hread.1 out.value.data.1 R c out.value.data.2
            e he hc hw.1 hw.2 hbad
          cases e with
          | mk ec er => cases er <;> exact hsol

end Schnorr.AGM.Reduction
