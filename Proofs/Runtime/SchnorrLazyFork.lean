import Proofs.Runtime.SchnorrLazySeedLog
import Proofs.Runtime.SeededLazyFork

/-! A complete Schnorr fork over the finite retained tape. Both private
families keep their entire first-run tapes, including draws after the fork.
Only encountered cells are stored; new replay families sample on demand. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.LazySeed

variable {F A : Type} [Zero F]

theorem toSeed_encode (log : QueryLog (replaySpec F)) :
    SeedTape.toSeed (encodeTape log) = SeededTrace.restore log ∅ := by
  induction log with
  | nil => rfl
  | cons entry log ih =>
      rcases entry with ⟨i, answer⟩
      change SeedTape.toSeed (encodeReply i answer :: encodeTape log) =
        (SeededTrace.restore log ∅).prependValues [answer]
      rw [← ih]
      funext j
      change SeedTape.values j (encodeReply i answer :: encodeTape log) = _
      rw [SeedTape.values_encode_cons]
      by_cases h : j = i
      · subst j; simp [SeedTape.toSeed]
      · simp [h, SeedTape.toSeed]

variable [SampleableType F] [DecidableEq F] [unifSpec ⊂ₒ replaySpec F]

/-- Complete controller: first execution, selected-slot check, fresh challenge,
unchanged-answer rejection, retained-tape restart, and second selector check. -/
def fork (main : OracleComp (replaySpec F) A) (target : (replaySpec F).Domain)
    {q : Nat} (select : A → Option (Fin q)) : OracleComp (replaySpec F) (Option (A × A)) := do
  let first ← (simulateQ oracle main).run {}
  match select first.1 with
  | none => pure none
  | some slot =>
      let answer ← liftComp ($ᵗ (replaySpec F).Range target) (replaySpec F)
      if (SeedTape.values target first.2.saved)[slot.val]? = some answer then pure none
      else
        let second ← (simulateQ oracle main).run' (restart target slot.val answer first.2)
        if select second = some slot then pure (some (first.1, second)) else pure none

/-- The finite-list implementation is exactly the transcript-based controller,
before taking any output distribution. No resource or finiteness premise on the
attacker's sampling-family universe is used here. -/
theorem fork_eq_recorded (main : OracleComp (replaySpec F) A)
    (target : (replaySpec F).Domain) {q : Nat} (select : A → Option (Fin q)) :
    fork main target select = SeededLazyFork.recordedFork main target select := by
  simp only [fork, run_log main [], List.nil_append, bind_map_left,
    SeededLazyFork.recordedFork]
  apply bind_congr
  intro first
  cases selected : select first.1 with
  | none => simp [SeededLazyFork.afterFirst, selected]
  | some slot =>
      simp only [SeededLazyFork.afterFirst, selected]
      apply bind_congr
      intro answer
      have encoded := congrFun (toSeed_encode first.2) target
      change SeedTape.values target (encodeTape first.2) = _ at encoded
      rw [encoded]
      split
      · rfl
      · rw [run'_seeded, restart_seed, toSeed_encode]

variable [IsUniformSpec (replaySpec F)]
  [∀ i, MeasurableSpace ((replaySpec F).Range i)]
  [∀ i, DiscreteMeasurableSpace ((replaySpec F).Range i)]
  [unifSpec ˡ⊂ₒ replaySpec F] [MeasurableSpace A]

/-- The complete finite-list fork has exactly the reference seeded fork's joint
output distribution. The family list is used only to describe that reference;
the implementation never enumerates or allocates it. -/
theorem fork_eq_seeded (main : OracleComp (replaySpec F) A)
    (budget : (replaySpec F).Domain → Nat) (bound : IsPerIndexQueryBound main budget)
    (families : List (replaySpec F).Domain) (unique : families.Nodup)
    (cover : SeedListCovers budget families) (target : (replaySpec F).Domain)
    (select : A → Option (Fin (budget target + 1)))
    (within : ∀ result ∈ support main.withQueryLog, ∀ slot, select result.1 = some slot →
      slot.val < (SeededTrace.restore result.2 ∅ target).length) :
    𝒟[fork main target select] = 𝒟[seededFork main budget families target select] := by
  rw [fork_eq_recorded]
  exact (SeededLazyFork.seededFork_eq_recordedFork main budget bound families unique cover
    target select within).symm

end Signatures.Runtime.Schnorr.LazySeed
