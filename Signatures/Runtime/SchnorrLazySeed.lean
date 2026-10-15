import Signatures.Runtime.SeedTapeReset

/-! Lazy retained randomness for an arbitrary Schnorr replay computation. Each
family consumes its saved replies in order; a miss samples and records exactly
one new reply. No sampling-family enumeration or source-language syntax is used.

The projection to the existing seeded oracle is exact for one execution. Reset
preserves every other family's entire saved tape, including private draws made
after the selected challenge. These identities alone do not prove the joint
distribution of a lazy fork equal to the fully pregenerated fork. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.LazySeed

open SeedTape

variable {F : Type}

/-- `saved` retains all known replies. `remaining` is the unconsumed tape for
this execution. A newly sampled reply is saved but has already been consumed. -/
structure State (F : Type) where
  saved : List (TapeCell F) := []
  remaining : List (TapeCell F) := []

def State.fromTape (xs : List (TapeCell F)) : State F := ⟨xs, xs⟩

def oracle [Zero F] :
    QueryImpl (replaySpec F) (StateT (State F) (OracleComp (replaySpec F))) :=
  fun i s =>
    let r := pop (familyTag i) (0, 0, 0) s.remaining
    if r.1 then pure (decodeReply i r.2.1, { s with remaining := r.2.2 })
    else (fun answer => (answer, { s with saved := s.saved ++ [encodeReply i answer] })) <$>
      ((replaySpec F).query i : OracleComp (replaySpec F) _)

variable [Zero F]

theorem oracle_refines (i : (replaySpec F).Domain) :
    StateRefines State.remaining (oracle i) (SeedTape.oracle i) := by
  intro s
  cases h : (pop (familyTag i) (0, (0 : F), 0) s.remaining).1 <;>
    simp [oracle, SeedTape.oracle, h, StateT.run, Functor.map_map]

theorem simulate_refines {A : Type} (main : OracleComp (replaySpec F) A) :
    StateRefines State.remaining (simulateQ oracle main) (simulateQ SeedTape.oracle main) := by
  induction main using OracleComp.inductionOn with
  | pure a => exact StateRefines.pure State.remaining a
  | query_bind i next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact StateRefines.bind State.remaining (oracle_refines i) ih

/-- Saving fresh replies does not change the current run's seeded semantics. -/
theorem simulate_seeded {A : Type} (main : OracleComp (replaySpec F) A) :
    StateRefines (fun s : State F => toSeed s.remaining)
      (simulateQ oracle main) (simulateQ seededOracle main) := by
  intro s
  have h := congrArg (Functor.map (fun p => (p.1, toSeed p.2))) (simulate_refines main s)
  simpa only [Functor.map_map] using h.trans (SeedTape.simulate_refines main s.remaining)

theorem run'_seeded {A : Type} (main : OracleComp (replaySpec F) A) (s : State F) :
    (simulateQ oracle main).run' s = (simulateQ seededOracle main).run' (toSeed s.remaining) := by
  have h := congrArg (Functor.map Prod.fst) (simulate_seeded main s)
  simpa only [Functor.map_map, StateT.run', StateT.run] using h

private theorem tape_empty {A : Type} (main : OracleComp (replaySpec F) A) :
    (simulateQ SeedTape.oracle main).run [] = (fun a => (a, [])) <$> main := by
  induction main using OracleComp.inductionOn with
  | pure a => simp
  | query_bind i next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      change ((fun answer => (answer, [])) <$> (liftM ((replaySpec F).query i) : OracleComp (replaySpec F) _) >>=
        fun p => (simulateQ SeedTape.oracle (next p.1)).run p.2) = _
      simp only [bind_map_left, ih, map_bind]

/-- The first pass has exactly the original computation's output distribution;
recording requires no advance list of possible sampling families. -/
theorem run'_empty {A : Type} (main : OracleComp (replaySpec F) A)
    (saved : List (TapeCell F)) :
    (simulateQ oracle main).run' ⟨saved, []⟩ = main := by
  have h := congrArg (Functor.map Prod.fst)
    ((simulate_refines main ⟨saved, []⟩).trans (tape_empty main))
  simpa [Functor.map_map, StateT.run', StateT.run] using h

/-- Restart every family at its beginning, retaining only the selected family's
prefix and replacement. Other families keep their complete saved replies. -/
def restart (i : (replaySpec F).Domain) (slot : Nat) (answer : (replaySpec F).Range i)
    (s : State F) : State F :=
  State.fromTape (reset (familyTag i) slot (encodeReply i answer) s.saved)

theorem restart_seed (i : (replaySpec F).Domain) (slot : Nat)
    (answer : (replaySpec F).Range i) (s : State F) :
    toSeed (restart i slot answer s).remaining =
      ((toSeed s.saved).takeAtIndex i slot).addValue i answer :=
  toSeed_reset i slot answer s.saved

/-- In particular, a hash fork preserves both attacker and simulator private
randomness, even entries sampled after that hash in the first execution. -/
theorem restart_other (i j : (replaySpec F).Domain) (hji : j ≠ i) (slot : Nat)
    (answer : (replaySpec F).Range i) (s : State F) :
    values j (restart i slot answer s).remaining = values j s.saved := by
  have ht : familyTag i ≠ familyTag j := fun h => hji (familyTag_injective h).symm
  simp [restart, State.fromTape, reset, values_append, values_trim_other i j hji,
    values, familyTag_encode, ht]

theorem restart_length (i : (replaySpec F).Domain) (slot : Nat)
    (answer : (replaySpec F).Range i) (s : State F) :
    (restart i slot answer s).saved.length ≤ s.saved.length + 1 ∧
      (restart i slot answer s).remaining = (restart i slot answer s).saved :=
  ⟨reset_length _ _ _ _, rfl⟩

end Signatures.Runtime.Schnorr.LazySeed
