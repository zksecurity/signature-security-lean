import Signatures.Runtime.SchnorrRawTapeValid

/-! Capacity reservations for the raw finite-list replay implementation. Bounds
follow the draws actually requested, with no enumeration of possible arities.
These are cell/query bounds; encoded sizes and native execution costs are separate. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.RawTape

variable {F : Type} [Zero F]

theorem oracle_growth (i : (Spec F).Domain) (state : State F)
    (out : (Spec F).Range i × State F) (supported : out ∈ support ((oracle i).run state)) :
    out.2.saved.length ≤ state.saved.length + 1 ∧
      out.2.remaining.length ≤ state.remaining.length := by
  cases found : (SeedTape.pop (tag i) (0, (0 : F), 0) state.remaining).1 with
  | false =>
      simp only [oracle, found, Bool.false_eq_true, ite_false, StateT.run,
        support_map, Set.mem_image] at supported
      obtain ⟨answer, _, rfl⟩ := supported
      simp
  | true =>
      simp only [oracle, found, ite_true, StateT.run, support_pure,
        Set.mem_singleton_iff] at supported
      subst out
      exact ⟨Nat.le_succ _, SeedTape.pop_length _ _ _⟩

/-- Every live draw is appended chronologically; replay never discards a
previously saved private suffix. -/
theorem oracle_saved_extends (i : (Spec F).Domain) (state : State F)
    (out : (Spec F).Range i × State F) (supported : out ∈ support ((oracle i).run state)) :
    ∃ fresh, out.2.saved = state.saved ++ fresh ∧ fresh.length ≤ 1 := by
  cases found : (SeedTape.pop (tag i) (0, (0 : F), 0) state.remaining).1 with
  | false =>
      simp only [oracle, found, Bool.false_eq_true, ite_false, StateT.run,
        support_map, Set.mem_image] at supported
      obtain ⟨answer, _, rfl⟩ := supported
      exact ⟨[encode i answer], rfl, by simp⟩
  | true =>
      simp only [oracle, found, ite_true, StateT.run, support_pure,
        Set.mem_singleton_iff] at supported
      subst out
      exact ⟨[], by simp, by simp⟩

theorem simulate_growth {A : Type} (main : OracleComp (Spec F) A)
    (q : Nat) (queries : IsTotalQueryBound main q) (state : State F) (out : A × State F)
    (supported : out ∈ support ((simulateQ oracle main).run state)) :
    out.2.saved.length ≤ state.saved.length + q ∧
      out.2.remaining.length ≤ state.remaining.length := by
  induction main using OracleComp.inductionOn generalizing q state with
  | pure value =>
      have same : out = (value, state) := by simpa using supported
      subst out
      exact ⟨by dsimp only; omega, Nat.le_refl _⟩
  | query_bind i next ih =>
      rw [isTotalQueryBound_query_bind_iff] at queries
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at supported
      obtain ⟨middle, hmiddle, supported⟩ := supported
      obtain ⟨hs, hr⟩ := oracle_growth i state middle hmiddle
      obtain ⟨hs', hr'⟩ := ih middle.1 (q - 1) (queries.2 middle.1) middle.2 supported
      exact ⟨by omega, hr'.trans hr⟩

theorem oracle_queryBound (i : (Spec F).Domain) (state : State F) :
    IsTotalQueryBound ((oracle i).run state) 1 := by
  cases found : (SeedTape.pop (tag i) (0, (0 : F), 0) state.remaining).1 <;>
    simp [oracle, found, StateT.run, map_eq_bind_pure_comp, IsTotalQueryBound]

/-- A replay hit makes no live sampling call; a miss makes exactly one. -/
theorem simulate_queryBound {A : Type} (main : OracleComp (Spec F) A)
    (q : Nat) (queries : IsTotalQueryBound main q) (state : State F) :
    IsTotalQueryBound ((simulateQ oracle main).run state) q :=
  queries.simulateQ_run_of_step oracle_queryBound state

theorem firstPass_growth {A : Type} (main : OracleComp (Spec F) A)
    (q : Nat) (queries : IsTotalQueryBound main q) (out : A × State F)
    (supported : out ∈ support ((simulateQ oracle main).run {})) :
    out.2.saved.length ≤ q ∧ out.2.remaining = [] := by
  obtain ⟨hs, hr⟩ := simulate_growth main q queries {} out supported
  exact ⟨by simpa using hs, List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hr)⟩

omit [Zero F] in
theorem restart_length (slot : Nat) (answer : F) (state : State F) :
    (restart slot answer state).saved.length ≤ state.saved.length + 1 ∧
      (restart slot answer state).remaining = (restart slot answer state).saved :=
  ⟨SeedTape.reset_length _ _ _ _, rfl⟩

/-- A second execution reserves its new draws in addition to the retained
first tape and replacement challenge. Both stored lists are counted. -/
theorem replay_growth {A B : Type} (main : OracleComp (Spec F) A)
    (replay : A → OracleComp (Spec F) B) (q₁ q₂ : Nat)
    (firstQueries : IsTotalQueryBound main q₁)
    (replayQueries : ∀ value, IsTotalQueryBound (replay value) q₂)
    (first : A × State F) (firstSupported : first ∈ support ((simulateQ oracle main).run {}))
    (slot : Nat) (answer : F) (second : B × State F)
    (secondSupported : second ∈ support
      ((simulateQ oracle (replay first.1)).run (restart slot answer first.2))) :
    second.2.saved.length ≤ q₁ + q₂ + 1 ∧ second.2.remaining.length ≤ q₁ + 1 := by
  obtain ⟨hs, _⟩ := firstPass_growth main q₁ firstQueries first firstSupported
  obtain ⟨hreset, hsame⟩ := restart_length slot answer first.2
  obtain ⟨hs', hr'⟩ := simulate_growth (replay first.1) q₂ (replayQueries first.1)
    (restart slot answer first.2) second secondSupported
  rw [hsame] at hr'
  exact ⟨by omega, by omega⟩

end Signatures.Runtime.Schnorr.RawTape
