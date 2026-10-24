import Proofs.Runtime.SchnorrRawTapeBounds

/-! Private sampling replays each original uniform request on the shared raw
tape. A scalar sampler may make any finite adaptive sequence of such requests;
its challenge-sampling implementation is never used by this interpreter. -/

namespace Signatures.Runtime.Schnorr.RawTape.Private
open OracleComp OracleSpec
variable {F : Type} [Zero F]

def oracle : QueryImpl unifSpec (StateT (State F) ProbComp) := fun n state =>
  let scan := SeedTape.pop (n + 2) (0, 0, 0) state.remaining
  if scan.1 then pure (decode (.inl n) scan.2.1, { state with remaining := scan.2.2 })
  else (fun answer => (answer, { state with saved := state.saved ++ [encode (.inl n) answer] })) <$>
    unifSpec.query n

theorem oracle_eq (sample : QueryImpl (Spec F) ProbComp)
    (forwards : ∀ n, sample (.inl n) = unifSpec.query n) (n : Nat) (state : State F) :
    (oracle n).run state = simulateQ sample ((RawTape.oracle (.inl n)).run state) := by
  cases found : (SeedTape.pop (n + 2) (0, (0 : F), 0) state.remaining).1 <;>
    simp [oracle, RawTape.oracle, tag, family, SeedTape.familyTag, found,
      StateT.run, forwards]

/-- Exact tree equality preserves the order of queries, their adaptive ranges,
the returned value and both tapes. No single-query sampler assumption is used. -/
theorem simulate_source {A : Type} (sample : QueryImpl (Spec F) ProbComp)
    (forwards : ∀ n, sample (.inl n) = unifSpec.query n) (main : ProbComp A) (state : State F) :
    (simulateQ oracle main).run state =
      simulateQ sample ((simulateQ RawTape.oracle (liftRandom main)).run state) := by
  induction main using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind n next ih =>
      simp only [liftRandom, simulateQ_bind, simulateQ_spec_query]
      change ((oracle n).run state >>= fun p => (simulateQ oracle (next p.1)).run p.2) =
        simulateQ sample (((RawTape.oracle (.inl n)).run state) >>= fun p =>
          (simulateQ RawTape.oracle (liftRandom (next p.1))).run p.2)
      rw [oracle_eq sample forwards]
      simp only [simulateQ_bind]
      congr 1
      funext p
      exact ih p.1 p.2

theorem oracle_growth (n : Nat) (state : State F) (out : Fin (n + 1) × State F)
    (supported : out ∈ support ((oracle n).run state)) :
    out.2.saved.length ≤ state.saved.length + 1 ∧
      out.2.remaining.length ≤ state.remaining.length := by
  cases found : (SeedTape.pop (n + 2) (0, (0 : F), 0) state.remaining).1 with
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

theorem scalar_source [SampleableType F] (state : State F) :
    (simulateQ oracle ($ᵗ F)).run state =
      simulateQ _root_.Schnorr.LazyROM.sample
        ((simulateQ RawTape.oracle (privateImpl (.inr ()))).run state) :=
  simulate_source _root_.Schnorr.LazyROM.sample (fun _ => rfl) ($ᵗ F) state

end Signatures.Runtime.Schnorr.RawTape.Private
