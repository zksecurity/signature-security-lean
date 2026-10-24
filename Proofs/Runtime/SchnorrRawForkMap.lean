import Proofs.Runtime.SchnorrRawFork

/-! Output representation changes commute with the complete raw-tape fork.
These are proof-side maps; neither cache functions nor a message universe are
materialized by the finite controller. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.RawTape

variable {F A B : Type} [Zero F] [SampleableType F] [DecidableEq F]

theorem fork_map (main : OracleComp (Spec F) A) (f : A → B) (qH : Nat)
    (select : B → Option (Fin (qH + 1))) :
    fork (f <$> main) qH select =
      Option.map (Prod.map f f) <$> fork main qH (select ∘ f) := by
  unfold fork
  simp only [simulateQ_map, StateT.run_map, StateT.run'_map',
    bind_map_left, map_bind, Function.comp_def]
  apply bind_congr
  intro first
  cases selected : select (f first.1) with
  | none => simp
  | some slot =>
      simp only [map_bind]
      apply bind_congr
      intro fresh
      split
      · simp
      · simp only [map_bind]
        apply bind_congr
        intro second
        split <;> simp

/-- Both successful fork outputs are possible outputs of the original pass,
including replay from a retained tape. -/
theorem fork_outputs (main : OracleComp (Spec F) A) (qH : Nat)
    (select : A → Option (Fin (qH + 1))) (first second : A)
    (h : some (first, second) ∈ support (fork main qH select)) :
    first ∈ support main ∧ second ∈ support main := by
  unfold fork at h
  simp only [mem_support_bind_iff] at h
  obtain ⟨initial, hi, h⟩ := h
  have hin : initial.1 ∈ support main := support_simulateQ_run'_subset oracle main {} (by
    rw [StateT.run', support_map]
    exact ⟨initial, hi, rfl⟩)
  cases hs : select initial.1 with
  | none => simp only [hs, support_pure, Set.mem_singleton_iff, reduceCtorEq] at h
  | some slot =>
      simp only [hs, mem_support_bind_iff] at h
      obtain ⟨fresh, _, h⟩ := h
      split at h
      · simp at h
      · simp only [mem_support_bind_iff] at h
        obtain ⟨next, hn, h⟩ := h
        split at h
        · simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hin, support_simulateQ_run'_subset oracle main _ hn⟩
        · simp at h

end Signatures.Runtime.Schnorr.RawTape
