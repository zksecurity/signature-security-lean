import Proofs.Runtime.ReplayExpansion
import VCVio.OracleComp.Constructions.SampleableType

/-! Primitive randomness for the executable Schnorr fork. A private scalar draw is
one machine operation with a sampling-cost contract, not necessarily one raw uniform
query. Expansion preserves the joint fork law, including its shared random prefix. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr

variable {F A : Type}

abbrev privateSpec (F : Type) := unifSpec + (Unit →ₒ F)
abbrev replaySpec (F : Type) := privateSpec F + (Unit →ₒ F)
abbrev expandedSpec (F : Type) := unifSpec + (Unit →ₒ F)

def liftRandom (main : ProbComp A) : OracleComp (expandedSpec F) A :=
  simulateQ (fun n => liftM ((expandedSpec F).query (.inl n))) main

theorem liftRandom_noChallenge (main : ProbComp A) :
    IsQueryBoundP (liftRandom (F := F) main) (fun i => i = Sum.inr ()) 0 := by
  induction main using OracleComp.inductionOn with
  | pure value => simp [liftRandom]
  | query_bind n next ih =>
    simp only [liftRandom, simulateQ_bind, simulateQ_spec_query]
    rw [isQueryBoundP_query_bind_iff]
    simpa [liftRandom] using ih

def privateImpl [SampleableType F] :
    QueryImpl (privateSpec F) (OracleComp (expandedSpec F))
  | .inl n => liftM ((expandedSpec F).query (.inl n))
  | .inr () => liftRandom ($ᵗ F)

theorem support_liftRandom (main : ProbComp A) :
    support (liftRandom (F := F) main) = support main := by
  induction main using OracleComp.inductionOn with
  | pure value => simp [liftRandom]
  | query_bind n next ih =>
      simp only [liftRandom] at ih ⊢
      simp [ih]

/-- Expanding private scalar samplers preserves every possible output, since
their sampling contract has full support. -/
theorem support_expandPrivate [SampleableType F] (main : OracleComp (replaySpec F) A) :
    support (simulateQ (Replay.expandPrivate privateImpl) main) = support main := by
  induction main using OracleComp.inductionOn with
  | pure value => simp
  | query_bind i next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, support_bind, ih]
      cases i with
      | inl i => cases i <;> simp [Replay.expandPrivate, privateImpl, support_liftRandom]
      | inr u => cases u; simp [Replay.expandPrivate]

theorem privateImpl_noChallenge [SampleableType F] (i : (privateSpec F).Domain) :
    IsQueryBoundP (privateImpl i) (fun j => j = Sum.inr ()) 0 := by
  cases i with
  | inl n => simp [privateImpl]
  | inr u => cases u; exact liftRandom_noChallenge _

/-- Replacing each private scalar instruction with its actual sampler leaves the
entire accepted fork unchanged, even when that sampler makes many raw queries. -/
theorem expand_contextFork [SampleableType F] [DecidableEq F]
    (main : OracleComp (replaySpec F) A) (qH : Nat)
    (select : A → Option (Fin (qH + 1))) :
    simulateQ (Replay.expandPrivate privateImpl)
        (contextFork main (fun _ => qH) (.inr ()) select) =
      contextFork (simulateQ (Replay.expandPrivate privateImpl) main)
        (fun _ => qH) (.inr ()) select :=
  Replay.contextFork_expand privateImpl privateImpl_noChallenge main qH select

/-- The recorded-prefix driver at primitive boundaries realizes VCVio's raw-query
fork exactly. Internal queries of a private scalar sampler need no machine tape cells. -/
theorem expand_loggedFork [SampleableType F] [DecidableEq F]
    (main : OracleComp (replaySpec F) A) (qH : Nat)
    (select : A → Option (Fin (qH + 1))) :
    simulateQ (Replay.expandPrivate privateImpl)
        (Replay.loggedFork main (fun _ => qH) (.inr ()) select) =
      contextFork (simulateQ (Replay.expandPrivate privateImpl) main)
        (fun _ => qH) (.inr ()) select := by
  rw [Replay.loggedFork_eq_contextFork]
  exact expand_contextFork main qH select

end Signatures.Runtime.Schnorr
