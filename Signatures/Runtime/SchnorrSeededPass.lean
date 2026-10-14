import Signatures.Runtime.SeedTapeRefinement
import Signatures.Runtime.SchnorrSeededReduction

/-! One executable fully seeded Schnorr pass: the source adversary, simulated
signing and hash handlers, and the final verification hash query. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.SeedTape

/-- Primitive sampling agrees with the source reduction's expansion, even when
one private scalar sample performs several underlying uniform draws. -/
theorem samples_expand {F A : Type} [SampleableType F]
    (main : OracleComp (replaySpec F) A) :
    simulateQ samples main = simulateQ Seeded.sampleChallenges
      (simulateQ (Replay.expandPrivate privateImpl) main) := by
  have hs : (samples : QueryImpl (replaySpec F) ProbComp) = sampleReplay := rfl
  have he : (Seeded.sampleChallenges : QueryImpl (expandedSpec F) ProbComp) = sampleExpanded := by
    funext i
    cases i with
    | inl n => rfl
    | inr u => cases u; rfl
  rw [he, sampleExpanded_expand, hs]

def taggedPass {Γ} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) Γ forgery) :
    Program CryptoOp TaggedEffect Γ observedForgery :=
  .bind (source.inline (taggedRoutines randomBound))
    (.bind (.call taggedFinalHash
      (.cons (.pair (.fst (.var .here)) (.fst (.snd (.var .here)))) .nil))
      (.ret (.pair (.var (.there .here)) (.var .here))))

def passCode {Γ} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) Γ forgery) :=
  (taggedPass randomBound source).inline routines

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

omit [SampleableType F] in
theorem taggedPass_denote (cost : PrimitiveCosts) {Γ} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    (taggedPass randomBound source).denote (arithmetic F G₁ G₂ K M cost) taggedSemantics env =
      macroPass cost randomBound source env := by
  simp only [taggedPass, Program.denote, Args.denote, Expr.denote, Var.get, macroPass]

/-- Exact seeded semantics for the compiled pass, retaining the cache needed
to choose a fork point. The theorem applies to every initial encoded tape. -/
theorem passCode_seeded (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ} (randomBound : Nat) (source : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (cache : cacheStore.Value (cryptoBase F G₁ G₂ K M)) (tape : List (TapeCell F)) :
    (fun p => (p.1.value, p.2.1)) <$>
        ((passCode randomBound source).run (arithmetic F G₁ G₂ K M cost)
          (Machine.effects sampling machineStore) env).run (cache, tape) =
      simulateQ samples ((simulateQ seededOracle
        ((macroPass cost randomBound source env).run cache)).run' (toSeed tape)) := by
  simpa only [passCode, taggedPass_denote] using
    program_seeded cost sampling (taggedPass randomBound source) env cache tape

theorem passCode_trace (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ} (randomBound : Nat) (source : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (g pk : G₁) (tape : List (TapeCell F)) :
    (fun p => cacheTrace (p.1.value, p.2.1)) <$>
        ((passCode randomBound source).run (arithmetic F G₁ G₂ K M cost)
          (Machine.effects sampling machineStore) env).run (((g, pk), [], []), tape) =
      simulateQ samples ((simulateQ seededOracle
        (Seeded.main cost randomBound source env g pk)).run' (toSeed tape)) := by
  have h := congrArg (Functor.map cacheTrace)
    (passCode_seeded cost sampling randomBound source env ((g, pk), [], []) tape)
  have state_map {S A B : Type} (f : A → B) (x : StateT S (OracleComp (replaySpec F)) A) (s : S) :
      (f <$> x) s = (fun p => (f p.1, p.2)) <$> x s := StateT.run_map _ _ _
  simpa only [Functor.map_map, Seeded.main, simulateQ_map, StateT.run',
    state_map] using h

end Signatures.Runtime.Schnorr.SeedTape
