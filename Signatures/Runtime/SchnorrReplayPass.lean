import Signatures.Runtime.SchnorrReplaySimulation
import Signatures.Runtime.SchnorrReplayRefinement

/-! The callable replaying simulation pass, including the final live-oracle query
and returning the full state needed by the fork controller. -/

open OracleComp

namespace Signatures.Runtime.Schnorr

abbrev forgery : Ty CryptoAtom := .pair message (.pair point₁ scalar)
abbrev observedForgery : Ty CryptoAtom := .pair forgery scalar
abbrev passOutput : Ty CryptoAtom := .pair observedForgery replayStore

def replayPassProgram {Γ} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) Γ forgery) :
    Program CryptoOp (Machine.Effect replayStore) Γ passOutput :=
  .bind ((source.inline (taggedRoutines randomBound)).inline replayRoutines)
    (.bind (.call (taggedFinalHash.inline replayRoutines)
      (.cons (.pair (.fst (.var .here)) (.fst (.snd (.var .here)))) .nil))
      (.bind (.query .read .unit)
        (.ret (.pair (.pair (.var (.there (.there .here))) (.var (.there .here))) (.var .here)))))

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem replayPassProgram_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ} (randomBound : Nat) (source : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (s : replayStore.Value (cryptoBase F G₁ G₂ K M)) :
    ((replayPassProgram randomBound source).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling replayStore) env).run s = (do
      let first ← (((source.inline (taggedRoutines randomBound)).inline replayRoutines).run
        (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling replayStore) env).run s
      let last ← ((taggedFinalHash.inline replayRoutines).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling replayStore) ((first.1.value.1, first.1.value.2.1), ())).run first.2
      pure (⟨((first.1.value, last.1.value), last.2), first.1.steps + last.1.steps + 25⟩, last.2)) := by
  unfold replayPassProgram
  generalize (source.inline (taggedRoutines randomBound)).inline replayRoutines = body
  generalize taggedFinalHash.inline replayRoutines = finalQuery
  dsimp [Program.run, Args.run, Expr.run, Var.get, Var.depth,
    StateT.run, StateT.bind, StateT.pure, Machine.effects]
  simp only [pure_bind, bind_assoc]
  congr 1
  funext first
  congr 1
  funext last
  apply congrArg pure
  apply congrArg (fun r => (r, last.2))
  apply congrArg (Run.mk _)
  omega

def passPrice (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound length localTime : Nat) (queries : Fin 3 → Nat) : Nat :=
  localTime + (∑ k, queries k * replayPrices cost sampling randomBound length k) +
    2 * (cost.messageEq + cost.point₁Eq + 37) * (∑ k, queries k) ^ 2 +
    (∑ k, queries k) * (cost.messageEq + cost.point₁Eq + 37) +
    scalarReplayPrice cost sampling length + cost.field + 116

/-- The callable pass returns its actual final store; the final query and all tape
accesses are charged in its source-derived budget. -/
theorem replayPassProgram_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ} (randomBound : Nat) (source : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      source env localTime queries)
    (g pk : G₁) (cursor limit : Nat) (tape : List (Nat × F × Nat))
    (out : Run (passOutput.Value (cryptoBase F G₁ G₂ K M)) × replayStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support (((replayPassProgram randomBound source).run
      (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling replayStore) env).run
        (((g, pk), [], []), cursor, limit, tape, []))) :
    out.1.steps ≤ passPrice cost sampling randomBound tape.length localTime queries ∧
      out.1.value.2 = out.2 ∧ out.2.1.1 = (g, pk) ∧
      cacheSize out.2.1 ≤ (∑ k, queries k) + 1 ∧
      replayEvents out.2 ≤ (∑ k, queries k * eventAllowance k) + 1 := by
  rw [replayPassProgram_run] at hout
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
  obtain ⟨first, hf, last, hl, rfl⟩ := hout
  have hf' := replaySimulation_bound cost sampling randomBound g pk source env localTime queries hsource
    cursor limit tape first hf
  rw [Program.inline_run] at hl
  have hl' := replayedFinalHash_bound cost sampling (first.1.value.1, first.1.value.2.1)
    first.2.1.1.1 first.2.1.1.2 first.2.1.2.1 first.2.1.2.2 first.2.2.1 first.2.2.2.1
    first.2.2.2.2.1 first.2.2.2.2.2 last hl
  have hc : first.2.1.2.2.length ≤ ∑ k, queries k :=
    (Nat.le_max_right _ _).trans hf'.2.2.2.1
  refine ⟨?_, rfl, hl'.2.1.trans hf'.1, ?_, ?_⟩
  · have hcost := hl'.1
    rw [hf'.2.2.1] at hcost
    have hmul := Nat.mul_le_mul_right (cost.messageEq + cost.point₁Eq + 37) hc
    dsimp [passPrice]
    omega
  · dsimp [cacheSize]
    rw [hl'.2.2.1]
    have hm : first.2.1.2.1.length ≤ ∑ k, queries k :=
      (Nat.le_max_left _ _).trans hf'.2.2.2.1
    omega
  · have he := hl'.2.2.2.2.2.2
    change replayEvents last.2 ≤ replayEvents first.2 + 1 at he
    exact he.trans (Nat.add_le_add_right hf'.2.2.2.2.1 1)

end Signatures.Runtime.Schnorr
