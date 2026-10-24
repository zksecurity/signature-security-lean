import Proofs.Runtime.SchnorrLazySeed

/-! Query-dependent bounds for lazy retained randomness. These count stored
cells and ambient sampling calls, not encoded bit sizes or execution time. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.LazySeed

open SeedTape

variable {F : Type} [Zero F]

theorem oracle_growth (i : (replaySpec F).Domain) (s : State F)
    (p : (replaySpec F).Range i × State F) (hp : p ∈ support ((oracle i).run s)) :
    p.2.saved.length ≤ s.saved.length + 1 ∧ p.2.remaining.length ≤ s.remaining.length := by
  cases h : (pop (familyTag i) (0, (0 : F), 0) s.remaining).1 with
  | false =>
      simp only [oracle, h, Bool.false_eq_true, ite_false, StateT.run, support_map,
        Set.mem_image] at hp
      obtain ⟨answer, _, rfl⟩ := hp
      simp
  | true =>
      simp only [oracle, h, ite_true, StateT.run, support_pure, Set.mem_singleton_iff] at hp
      subst p
      exact ⟨Nat.le_succ _, pop_length _ _ _⟩

/-- A fresh draw appends one cell, while a replay hit leaves the saved tape
unchanged. Consequently, no saved private suffix is lost during either run. -/
theorem oracle_saved_extends (i : (replaySpec F).Domain) (s : State F)
    (p : (replaySpec F).Range i × State F) (hp : p ∈ support ((oracle i).run s)) :
    ∃ fresh, p.2.saved = s.saved ++ fresh ∧ fresh.length ≤ 1 := by
  cases h : (pop (familyTag i) (0, (0 : F), 0) s.remaining).1 with
  | false =>
      simp only [oracle, h, Bool.false_eq_true, ite_false, StateT.run, support_map,
        Set.mem_image] at hp
      obtain ⟨answer, _, rfl⟩ := hp
      exact ⟨[encodeReply i answer], rfl, by simp⟩
  | true =>
      simp only [oracle, h, ite_true, StateT.run, support_pure, Set.mem_singleton_iff] at hp
      subst p
      exact ⟨[], by simp, by simp⟩

/-- The bound follows all adaptive paths, without a finite list or a numeric
maximum of possible random arities. -/
theorem simulate_growth {A : Type} (main : OracleComp (replaySpec F) A)
    (q : Nat) (hq : IsTotalQueryBound main q) (s : State F) (p : A × State F)
    (hp : p ∈ support ((simulateQ oracle main).run s)) :
    p.2.saved.length ≤ s.saved.length + q ∧ p.2.remaining.length ≤ s.remaining.length := by
  induction main using OracleComp.inductionOn generalizing q s with
  | pure a =>
      have he : p = (a, s) := by simpa using hp
      subst p
      dsimp only
      exact ⟨by omega, Nat.le_refl _⟩
  | query_bind i next ih =>
      rw [isTotalQueryBound_query_bind_iff] at hq
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hp
      obtain ⟨mid, hmid, hp⟩ := hp
      obtain ⟨hs, hr⟩ := oracle_growth i s mid hmid
      obtain ⟨hs', hr'⟩ := ih mid.1 (q - 1) (hq.2 mid.1) mid.2 hp
      exact ⟨by omega, hr'.trans hr⟩

theorem oracle_queryBound (i : (replaySpec F).Domain) (s : State F) :
    IsTotalQueryBound ((oracle i).run s) 1 := by
  cases h : (pop (familyTag i) (0, (0 : F), 0) s.remaining).1 <;>
    simp [oracle, h, StateT.run, map_eq_bind_pure_comp, IsTotalQueryBound]

/-- Each requested draw makes at most one live oracle call. -/
theorem simulate_queryBound {A : Type} (main : OracleComp (replaySpec F) A)
    (q : Nat) (hq : IsTotalQueryBound main q) (s : State F) :
    IsTotalQueryBound ((simulateQ oracle main).run s) q :=
  hq.simulateQ_run_of_step oracle_queryBound s

theorem firstPass_growth {A : Type} (main : OracleComp (replaySpec F) A)
    (q : Nat) (hq : IsTotalQueryBound main q) (p : A × State F)
    (hp : p ∈ support ((simulateQ oracle main).run {})) :
    p.2.saved.length ≤ q ∧ p.2.remaining = [] := by
  obtain ⟨hs, hr⟩ := simulate_growth main q hq {} p hp
  exact ⟨by simpa using hs, List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hr)⟩

/-- Run a second computation after changing one family at the chosen slot.
This is a semantic building block; it does not yet select a valid fork or
assert equality with the pregenerated fork's joint distribution. -/
def twoPass {A B : Type} (main : OracleComp (replaySpec F) A)
    (replay : A → OracleComp (replaySpec F) B) (i : (replaySpec F).Domain)
    (slot : A → Nat) (answer : A → (replaySpec F).Range i) :
    OracleComp (replaySpec F) ((A × B) × State F) := do
  let first ← (simulateQ oracle main).run {}
  let second ← (simulateQ oracle (replay first.1)).run
    (restart i (slot first.1) (answer first.1) first.2)
  pure ((first.1, second.1), second.2)

/-- Storage depends on encountered draws in the two executions. The one extra
cell is the replacement challenge; sampling that challenge is outside `twoPass`. -/
theorem twoPass_growth {A B : Type} (main : OracleComp (replaySpec F) A)
    (replay : A → OracleComp (replaySpec F) B) (i : (replaySpec F).Domain)
    (slot : A → Nat) (answer : A → (replaySpec F).Range i)
    (q₁ q₂ : Nat) (h₁ : IsTotalQueryBound main q₁)
    (h₂ : ∀ a, IsTotalQueryBound (replay a) q₂)
    (p : (A × B) × State F) (hp : p ∈ support (twoPass main replay i slot answer)) :
    p.2.saved.length ≤ q₁ + q₂ + 1 ∧ p.2.remaining.length ≤ q₁ + 1 := by
  simp only [twoPass, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
  obtain ⟨first, hfirst, second, hsecond, rfl⟩ := hp
  obtain ⟨hs, _⟩ := firstPass_growth main q₁ h₁ first hfirst
  obtain ⟨hreset, hsame⟩ := restart_length i (slot first.1) (answer first.1) first.2
  obtain ⟨hs', hr'⟩ := simulate_growth (replay first.1) q₂ (h₂ first.1)
    (restart i (slot first.1) (answer first.1) first.2) second hsecond
  rw [hsame] at hr'
  dsimp only
  exact ⟨by omega, by omega⟩

theorem twoPass_queryBound {A B : Type} (main : OracleComp (replaySpec F) A)
    (replay : A → OracleComp (replaySpec F) B) (i : (replaySpec F).Domain)
    (slot : A → Nat) (answer : A → (replaySpec F).Range i)
    (q₁ q₂ : Nat) (h₁ : IsTotalQueryBound main q₁)
    (h₂ : ∀ a, IsTotalQueryBound (replay a) q₂) :
    IsTotalQueryBound (twoPass main replay i slot answer) (q₁ + q₂) := by
  apply isTotalQueryBound_bind (simulate_queryBound main q₁ h₁ {})
  intro first
  have hret : ∀ second : B × State F,
      IsTotalQueryBound (pure ((first.1, second.1), second.2) : OracleComp (replaySpec F) _) 0 :=
    fun _ => trivial
  simpa only [Nat.add_zero] using isTotalQueryBound_bind
    (simulate_queryBound (replay first.1) q₂ (h₂ first.1)
      (restart i (slot first.1) (answer first.1) first.2)) hret

end Signatures.Runtime.Schnorr.LazySeed
