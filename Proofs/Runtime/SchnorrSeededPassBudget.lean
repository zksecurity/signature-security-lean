import Proofs.Runtime.SchnorrSeededPass
import Proofs.Runtime.SeedTapeSimulation
import Proofs.Runtime.SeedTapeGenerate

/-! The executable pass's complete arithmetic budget comes from the original
source certificate. Seed setup is actual code with its own proved budget. -/

open OracleComp

namespace Signatures.Runtime.Schnorr.SeedTape

def passPrice (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound length localTime : Nat) (queries : Fin 3 → Nat) : Nat :=
  localTime + (∑ k, queries k * sourcePrices cost sampling randomBound length k) +
    2 * (cost.messageEq + cost.point₁Eq + 37) * (∑ k, queries k) ^ 2 +
    (∑ k, queries k) * (cost.messageEq + cost.point₁Eq + 37) +
    scalarPrice cost sampling length + cost.field + 106

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem passCode_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ} (randomBound : Nat) (source : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (s : machineStore.Value (cryptoBase F G₁ G₂ K M)) :
    ((passCode randomBound source).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling machineStore) env).run s = (do
      let first ← (((source.inline (taggedRoutines randomBound)).inline routines).run
        (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling machineStore) env).run s
      let last ← ((taggedFinalHash.inline routines).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling machineStore) ((first.1.value.1, first.1.value.2.1), ())).run first.2
      pure (⟨(first.1.value, last.1.value), first.1.steps + last.1.steps + 17⟩, last.2)) := by
  unfold passCode taggedPass
  simp only [Program.inline]
  generalize (source.inline (taggedRoutines randomBound)).inline routines = body
  generalize taggedFinalHash.inline routines = finalQuery
  simp only [Program.run, Args.run, Expr.run, Var.get, Var.depth,
    StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc]
  congr 1
  funext first
  congr 1
  funext last
  apply congrArg pure
  apply Prod.ext
  · apply congrArg (Run.mk _)
    omega
  · rfl

theorem passCode_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ} (randomBound : Nat) (source : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      source env localTime queries) (g pk : G₁) (tape : List (TapeCell F))
    (out : Run (observedForgery.Value (cryptoBase F G₁ G₂ K M)) ×
      machineStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support (((passCode randomBound source).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling machineStore) env).run (((g, pk), [], []), tape))) :
    out.1.steps ≤ passPrice cost sampling randomBound tape.length localTime queries ∧
      out.2.1.1 = (g, pk) ∧ cacheSize out.2.1 ≤ (∑ k, queries k) + 1 ∧
      out.2.2.length ≤ tape.length := by
  rw [passCode_run] at hout
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
  obtain ⟨first, hf, last, hl, rfl⟩ := hout
  have hs := simulation_bound cost sampling randomBound g pk source env localTime queries hsource tape first hf
  rw [Program.inline_run] at hl
  have he := finalHash_bound cost sampling (first.1.value.1, first.1.value.2.1)
    first.2.1.1.1 first.2.1.1.2 first.2.1.2.1 first.2.1.2.2 first.2.2
    tape.length hs.2.1 last hl
  have hc : first.2.1.2.2.length ≤ ∑ k, queries k :=
    (Nat.le_max_right _ _).trans hs.2.2.1
  refine ⟨?_, he.2.1.trans hs.1, ?_, he.2.2.2.2⟩
  · have hm := Nat.mul_le_mul_right (cost.messageEq + cost.point₁Eq + 37) hc
    dsimp [passPrice]
    omega
  · dsimp [cacheSize] at hs ⊢
    rw [he.2.2.1]
    omega

end Signatures.Runtime.Schnorr.SeedTape
