import Proofs.Runtime.CoronSimulation

/-! The final verification hash and extraction are executed and charged explicitly. The
adversary's input environment is supplied to this evaluator; constructing it from a public
key is a separate obligation of the public implementation certificate. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Coron

variable {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]

/-- The fixed finish frame costs 12: input projections, two expression frames, one bind,
and result packing. The cache scan and algebra are separate executed instructions. -/
noncomputable def finish (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (g X h : G₁) (qS : Nat) (out : M × G₁) (state : CacheState F M qS) : ProbComp (Run G₁) := do
  let p ← (reply (G₂ := G₂) cost sampling g X h qS false out.1).run state
  let zero := (Expr.op CryptoOp.zero .unit : Expr CryptoOp [] scalar).run
    (arithmetic F G₁ G₂ M M cost) ()
  let rho := (lookup (val := scalar) CryptoOp.messageEq).run (arithmetic F G₁ G₂ M M cost)
    (out.1, zero.value, p.2.scalars, ())
  let result := extract.run (arithmetic F G₁ G₂ M M cost) (out.2, rho.value.2, X, ())
  pure ⟨result.value, p.1.steps + zero.steps + rho.steps + result.steps + 12⟩

def finishBound (cost : PrimitiveCosts) (sampling : SamplingCosts) (queries : Nat) : Nat :=
  replyBase cost sampling false + cost.field + cost.scalar₁ + cost.group + 33 +
    (cost.messageEq + 19) * (3 * queries + 1)

theorem finish_bound (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (g X h : G₁) (qS : Nat) (out : M × G₁) (state : CacheState F M qS)
    (z : Run G₁) (hz : z ∈ support (finish (G₂ := G₂) cost sampling g X h qS out state)) :
    z.steps ≤ finishBound cost sampling state.size := by
  simp only [finish, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  have hb := reply_bound (G₂ := G₂) cost sampling g X h qS false out.1 state p hp
  have hl := lookup_steps_le (arithmetic F G₁ G₂ M M cost) (val := scalar)
    CryptoOp.messageEq cost.messageEq (fun _ _ => le_rfl) out.1 0 p.2.scalars
  have he := extract_steps (G₂ := G₂) (M := M) cost out.2
    ((lookup (val := scalar) CryptoOp.messageEq).run (arithmetic F G₁ G₂ M M cost)
      (out.1, 0, p.2.scalars, ())).value.2 X
  have hs : p.2.scalars.length ≤ state.size + 1 := (Nat.le_max_left _ _).trans hb.1
  have hm := Nat.mul_le_mul_right (cost.messageEq + 19) hs
  have hzv : ((Expr.op CryptoOp.zero .unit : Expr CryptoOp [] scalar).run
      (arithmetic F G₁ G₂ M M cost) ()).value = 0 := rfl
  have hzt : ((Expr.op CryptoOp.zero .unit : Expr CryptoOp [] scalar).run
      (arithmetic F G₁ G₂ M M cost) ()).steps = cost.field + 2 := by
    simp [Expr.run, arithmetic, CryptoOp.price]
    omega
  simp only [hzv, hzt, he, finishBound]
  nlinarith [hb.2]

/-- Sixteen fixed setup/return steps include the empty cache record and list constructors,
the two procedure frames, result projections, and return packing. -/
noncomputable def reduction (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (g X h : G₁) (qS randomBound : Nat) {Γ}
    (code : Program CryptoOp (Command randomBound) Γ (.pair message point₁))
    (env : Env (cryptoBase F G₁ G₂ M M) Γ) : ProbComp (Run G₁) := do
  let p ← (code.run (arithmetic F G₁ G₂ M M cost)
    (handler cost sampling g X h qS randomBound) env).run .empty
  let z ← finish (G₂ := G₂) cost sampling g X h qS p.1.value p.2
  pure ⟨z.value, p.1.steps + z.steps + 16⟩

def reductionBound (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (localTime : Nat) (queries : Fin 3 → Nat) : Nat :=
  localTime + (∑ k, queries k * prices cost sampling k) +
    2 * (cost.messageEq + 19) * (∑ k, queries k) ^ 2 +
    finishBound cost sampling (∑ k, queries k) + 16

/-- The bound is derived from a source budget and the fixed implemented handlers. It does
not assume a runtime certificate for the finished solver. The appended hash is additional
to the source's hash-query budget, even when the source made no oracle queries. -/
theorem reduction_bound (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (g X h : G₁) (qS randomBound : Nat) {Γ}
    (code : Program CryptoOp (Command randomBound) Γ (.pair message point₁))
    (env : Env (cryptoBase F G₁ G₂ M M) Γ) (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ M M cost) (replies randomBound) kind
      code env localTime queries)
    (z : Run G₁)
    (hz : z ∈ support (reduction cost sampling g X h qS randomBound code env)) :
    z.steps ≤ reductionBound cost sampling localTime queries := by
  simp only [reduction, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨p, hp, z, hz, rfl⟩ := hz
  have hs := simulation_bound cost sampling g X h qS randomBound code env localTime queries hsource p hp
  have hf := finish_bound (G₂ := G₂) cost sampling g X h qS p.1.value p.2 z hz
  have hm := Nat.mul_le_mul_left (cost.messageEq + 19) (Nat.mul_le_mul_left 3 hs.1)
  dsimp [reductionBound, finishBound] at hf ⊢
  nlinarith [hs.2]

end Signatures.Runtime.Coron
