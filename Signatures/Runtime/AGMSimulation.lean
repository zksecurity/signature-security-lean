import Signatures.Runtime.AGMReplies
import Signatures.Runtime.AGMOracleRefinement

/-! Concrete good/bad adaptive simulator bounds. The local expression premises concern
only compiled equality and weight programs, not whole hash/sign routines or whole solvers.
Table initialization and final algebraic extraction are additional, separately charged work. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.AGM

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  {indexTy messageTy : Ty CryptoAtom}

/-- Every actual simulator output occurs on an allowed source reply path. This transports
source output-size certificates without assuming that only honest replies were checked. -/
theorem machineSimulation_supported {configTy : Ty CryptoAtom}
    (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (hash : Expr CryptoOp [indexTy, configTy] point₁)
    (sign : Expr CryptoOp [messageTy, configTy] point₁) (randomBound cHash cSign : Nat)
    (cfg : configTy.Value (cryptoBase F G₁ G₂ K M))
    (hHash : ∀ i, (hash.run (arithmetic F G₁ G₂ K M cost) (i, cfg, ())).steps ≤ cHash)
    (hSign : ∀ m, (sign.run (arithmetic F G₁ G₂ K M cost) (m, cfg, ())).steps ≤ cSign)
    {Γ a} (code : Program CryptoOp (Command indexTy messageTy randomBound) Γ a)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (tr : (transcriptTy indexTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (z : Run (a.Value (cryptoBase F G₁ G₂ K M)) ×
      (oracleStore indexTy messageTy configTy).Value (cryptoBase F G₁ G₂ K M))
    (hz : z ∈ support (((code.inline (machineRoutines hash sign randomBound)).run
      (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling (oracleStore indexTy messageTy configTy))
      env).run (cfg, tr))) :
    ∃ r ∈ support (code.run (arithmetic F G₁ G₂ K M cost)
      (pricedRequests (replies randomBound)
        (fun cmd => machinePrices sampling randomBound cHash cSign (kind cmd))) env),
      r.value = z.1.value := by
  rw [Program.inline_run] at hz
  have hd := fun {a b} (cmd : Command indexTy messageTy randomBound a b)
      (arg : a.Value (cryptoBase F G₁ G₂ K M)) => pricedRequests_dominates (replies randomBound)
    (machineHandler cost sampling hash sign randomBound)
    (fun cmd => machinePrices sampling randomBound cHash cSign (kind cmd))
    (fun state => state.1 = cfg) (fun _ => 0) (by
      intro a b cmd arg state hs r hr
      rcases state with ⟨cfg', tr'⟩
      dsimp at hs
      subst cfg'
      have h := machineHandler_bound cost sampling hash sign randomBound cHash cSign cfg
        hHash hSign cmd arg tr' r hr
      refine ⟨h.1, trivial, ?_⟩
      simpa using (show (r.1.steps : Int) ≤ machinePrices sampling randomBound cHash cSign (kind cmd) by
        exact_mod_cast h.2.2)) cmd arg
  obtain ⟨_, r, hr, hv, _⟩ := code.run_dominated (arithmetic F G₁ G₂ K M cost)
    (fun state => state.1 = cfg) (fun _ => 0) _ _ hd env (cfg, tr) rfl z hz
  exact ⟨r, hr, hv⟩

theorem goodSimulation_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) (randomBound cEq cWeight : Nat)
    (heq : ∀ x y, (eq.run (arithmetic F G₁ G₂ K M cost) (x, y, ())).steps ≤ cEq)
    (hw : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).steps ≤ cWeight)
    (g X : G₁) (rho : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F))
    {Γ a} (code : Program CryptoOp (Command indexTy messageTy randomBound) Γ a)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      code env localTime queries)
    (z : Run (a.Value (cryptoBase F G₁ G₂ K M)) ×
      (oracleStore indexTy messageTy (goodConfig indexTy)).Value (cryptoBase F G₁ G₂ K M))
    (hz : z ∈ support (((code.inline (machineRoutines (goodHash eq) (goodSign weight) randomBound)).run
      (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling (oracleStore indexTy messageTy (goodConfig indexTy)))
      env).run ((g, X, rho), [], []))) :
    z.2.1 = (g, X, rho) ∧ transcriptSize z.2 ≤ ∑ k, queries k ∧
      z.1.steps ≤ localTime + ∑ k, queries k * machinePrices sampling randomBound
        (goodHashBound cost rho.length cEq) (goodSignBound cost rho.length cWeight) k := by
  exact machineSimulation_bound cost sampling (goodHash eq) (goodSign weight) randomBound
    (goodHashBound cost rho.length cEq) (goodSignBound cost rho.length cWeight) (g, X, rho)
    (fun i => goodHash_steps_le cost eq cEq heq i g X rho)
    (fun m => goodSign_steps_le cost weight cWeight m (fun i => hw i m) g X rho)
    code env localTime queries hsource z hz

theorem badSimulation_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) (randomBound cEq cWeight : Nat)
    (heq : ∀ x y, (eq.run (arithmetic F G₁ G₂ K M cost) (x, y, ())).steps ≤ cEq)
    (hw : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).steps ≤ cWeight)
    (kappa : F) (H : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × G₁))
    {Γ a} (code : Program CryptoOp (Command indexTy messageTy randomBound) Γ a)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      code env localTime queries)
    (z : Run (a.Value (cryptoBase F G₁ G₂ K M)) ×
      (oracleStore indexTy messageTy (badConfig indexTy)).Value (cryptoBase F G₁ G₂ K M))
    (hz : z ∈ support (((code.inline (machineRoutines (badHash eq) (badSign weight) randomBound)).run
      (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling (oracleStore indexTy messageTy (badConfig indexTy)))
      env).run ((kappa, H), [], []))) :
    z.2.1 = (kappa, H) ∧ transcriptSize z.2 ≤ ∑ k, queries k ∧
      z.1.steps ≤ localTime + ∑ k, queries k * machinePrices sampling randomBound
        (badHashBound cost H.length cEq) (badSignBound cost H.length cWeight) k := by
  exact machineSimulation_bound cost sampling (badHash eq) (badSign weight) randomBound
    (badHashBound cost H.length cEq) (badSignBound cost H.length cWeight) (kappa, H)
    (fun i => badHash_steps_le cost eq cEq heq i kappa H)
    (fun m => badSign_steps_le cost weight cWeight m (fun i => hw i m) kappa H)
    code env localTime queries hsource z hz

end Signatures.Runtime.AGM
