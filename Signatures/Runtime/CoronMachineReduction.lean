import Signatures.Runtime.CoronMachine
import Signatures.Runtime.CoronErasure

/-! Closed-machine final verification hash and co-CDH extraction. All list access,
argument construction, store reads, and arithmetic are ordinary target instructions. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Coron

def machineFinish (qS : Nat) :
    Program CryptoOp (Machine.Effect (machineStore qS)) [.pair message point₁] point₁ :=
  .bind (.call (machineReply qS false) (.cons (.fst (.var .here)) .nil))
    (.bind (.query .read .unit)
      (.bind (.call (.ret (lookup (val := scalar) CryptoOp.messageEq))
        (.cons (.fst (.var (.there (.there .here))))
          (.cons (.op .zero .unit) (.cons (.fst (.snd (.var .here))) .nil))))
        (.call (.ret extract)
          (.cons (.snd (.var (.there (.there (.there .here)))))
            (.cons (.snd (.var .here))
              (.cons (.fst (.snd (.fst (.var (.there .here))))) .nil))))))

variable {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]

/-- The additional overhead is derived from target instructions, not an assumed price
for the final reduction. The final store is unobserved by this solver. -/
theorem machineFinish_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (qS : Nat) (out : M × G₁) (state : CacheState F M qS) :
    Prod.fst <$> ((machineFinish qS).run (arithmetic F G₁ G₂ M M cost)
      (Machine.effects sampling (machineStore qS)) (out, ())).run (machineState g X h state) =
      (fun r => ⟨r.value, r.steps + cost.natOp + 80⟩) <$>
        finish (G₂ := G₂) cost (machineSampling sampling qS) g X h qS out state := by
  have hr := machineReply_run (G₂ := G₂) cost sampling g X h qS false out.1 state
  simp only [StateT.run] at hr
  dsimp [machineFinish, Program.run, Args.run, Expr.run, Var.get, Var.depth,
    StateT.run, StateT.bind, StateT.pure]
  rw [hr]
  simp only [Machine.effects, machineState, map_pure, finish, StateT.run,
    bind_pure_comp, Functor.map_map]
  congr 1
  funext p
  congr 1
  dsimp [Expr.run, arithmetic, CryptoOp.price]
  omega

theorem machineFinish_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (qS : Nat) (out : M × G₁) (state : CacheState F M qS)
    (z : Run G₁ × (machineStore qS).Value (cryptoBase F G₁ G₂ M M))
    (hz : z ∈ support (((machineFinish qS).run (arithmetic F G₁ G₂ M M cost)
      (Machine.effects sampling (machineStore qS)) (out, ())).run (machineState g X h state))) :
    z.1.steps ≤ finishBound cost (machineSampling sampling qS) state.size + cost.natOp + 80 := by
  have hp : z.1 ∈ support (Prod.fst <$> ((machineFinish qS).run
      (arithmetic F G₁ G₂ M M cost) (Machine.effects sampling (machineStore qS))
      (out, ())).run (machineState g X h state)) := by
    rw [support_map]
    exact ⟨z, hz, rfl⟩
  rw [machineFinish_run] at hp
  simp only [support_map, Set.mem_image] at hp
  obtain ⟨r, hr, he⟩ := hp
  have hb := finish_bound (G₂ := G₂) cost (machineSampling sampling qS) g X h qS out state r hr
  rw [← he]
  dsimp
  omega

theorem machineFinish_erase (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (qS : Nat) (out : M × G₁) (state : CacheState F M qS) :
    (fun p => p.1.value) <$> ((machineFinish qS).run (arithmetic F G₁ G₂ M M cost)
      (Machine.effects sampling (machineStore qS)) (out, ())).run (machineState g X h state) =
      Run.value <$> finish (G₂ := G₂) cost (machineSampling sampling qS) g X h qS out state := by
  have he := congrArg (Functor.map Run.value)
    (machineFinish_run (G₂ := G₂) cost sampling g X h qS out state)
  simpa only [Functor.map_map] using he

/-- Public fields are constructed by an expression over the actual inputs. Empty caches
and the signing log are allocated in the initializer; the source runs in the same context. -/
def machineReductionCode (qS randomBound : Nat) {Γ}
    (setup : Expr CryptoOp Γ (.pair point₁ (.pair point₁ point₁)))
    (code : Program CryptoOp (Command randomBound) Γ (.pair message point₁)) :
    Machine.Code Γ point₁ where
  store := machineStore qS
  init := .pair setup (.pair .nil (.pair .nil .nil))
  body := .bind (code.inline (machineRoutines qS randomBound))
    (.call (machineFinish qS) (.cons (.var .here) .nil))

theorem machineReductionCode_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (qS randomBound : Nat) {Γ}
    (setup : Expr CryptoOp Γ (.pair point₁ (.pair point₁ point₁)))
    (code : Program CryptoOp (Command randomBound) Γ (.pair message point₁))
    (env : Env (cryptoBase F G₁ G₂ M M) Γ) (publicSteps : Nat)
    (hpublic : setup.run (arithmetic F G₁ G₂ M M cost) env = ⟨(g, X, h), publicSteps⟩) :
    (machineReductionCode qS randomBound setup code).run cost sampling env = (do
      let p ← ((code.inline (machineRoutines qS randomBound)).run
        (arithmetic F G₁ G₂ M M cost) (Machine.effects sampling (machineStore qS)) env).run
          (machineState g X h .empty)
      let r ← ((machineFinish qS).run (arithmetic F G₁ G₂ M M cost)
        (Machine.effects sampling (machineStore qS)) (p.1.value, ())).run p.2
      pure ⟨r.1.value, p.1.steps + r.1.steps + publicSteps + 14⟩) := by
  dsimp [Machine.Code.run, machineReductionCode, Program.run, Args.run, Expr.run,
    Var.get, Var.depth, StateT.run, StateT.bind, StateT.pure]
  rw [hpublic]
  simp only [machineState, CacheState.empty, bind_assoc]
  congr 1
  funext p
  simp only [map_pure, bind_pure_comp]
  congr 1
  funext r
  congr 1
  omega

def machineReductionBound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    -- queries 1 is qH; indices 0 and 2 bound source randomness and signing calls.
    (qS randomBound localTime publicSteps : Nat) (queries : Fin 3 → Nat) : Nat :=
  -- Charge source local work and each oracle handler at its per-kind price.
  localTime + (∑ k, queries k * machinePrices cost sampling qS randomBound k) +
    -- Conservatively bound the repeated cache scans over all source calls.
    2 * (cost.messageEq + 19) * (∑ k, queries k) ^ 2 +
    -- Charge final hashing and extraction separately, including a previously unhashed forgery.
    finishBound cost (machineSampling sampling qS) (∑ k, queries k) +
    -- Account for public setup and the remaining compiled control instructions.
    cost.natOp + publicSteps + 94

/-- Complete target-program bound, derived from the source and initializer certificates.
No bound for the finished reduction is assumed. -/
theorem machineReductionCode_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (qS randomBound : Nat) {Γ}
    (setup : Expr CryptoOp Γ (.pair point₁ (.pair point₁ point₁)))
    (code : Program CryptoOp (Command randomBound) Γ (.pair message point₁))
    (env : Env (cryptoBase F G₁ G₂ M M) Γ) (publicSteps localTime : Nat) (queries : Fin 3 → Nat)
    (hpublic : setup.run (arithmetic F G₁ G₂ M M cost) env = ⟨(g, X, h), publicSteps⟩)
    (hsource : SourceBudget (arithmetic F G₁ G₂ M M cost) (replies randomBound) kind
      code env localTime queries)
    (z : Run G₁)
    (hz : z ∈ support ((machineReductionCode qS randomBound setup code).run cost sampling env)) :
    z.steps ≤ machineReductionBound cost sampling qS randomBound localTime publicSteps queries := by
  rw [machineReductionCode_run cost sampling g X h qS randomBound setup code env publicSteps hpublic] at hz
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨p, hp, r, hr, rfl⟩ := hz
  have hs := machineSimulation_bound cost sampling g X h qS randomBound code env
    localTime queries hsource p hp
  rcases p with ⟨out, ⟨⟨g', X', h'⟩, scalars, coins, signed⟩⟩
  have hf := machineFinish_bound cost sampling g' X' h' qS out.value
    ⟨scalars, coins, signed⟩ r hr
  have hm := Nat.mul_le_mul_left (cost.messageEq + 19) (Nat.mul_le_mul_left 3 hs.1)
  dsimp [machineCaches, machineReductionBound, finishBound] at hs hf hm ⊢
  nlinarith [hs.2]

set_option maxHeartbeats 800000 in
theorem machineReductionCode_erase (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (qS randomBound : Nat) {Γ}
    (setup : Expr CryptoOp Γ (.pair point₁ (.pair point₁ point₁)))
    (code : Program CryptoOp (Command randomBound) Γ (.pair message point₁))
    (env : Env (cryptoBase F G₁ G₂ M M) Γ) (publicSteps : Nat)
    (hpublic : setup.run (arithmetic F G₁ G₂ M M cost) env = ⟨(g, X, h), publicSteps⟩) :
    Run.value <$> (machineReductionCode qS randomBound setup code).run cost sampling env =
      Run.value <$> reduction cost (machineSampling sampling qS) g X h qS randomBound code env := by
  have hs := machineSimulation_refines cost sampling g X h qS randomBound code env .empty
  have hl := StateT.run_map (m := ProbComp) Run.value
    (code.run (arithmetic F G₁ G₂ M M cost)
      (handler cost (machineSampling sampling qS) g X h qS randomBound) env) CacheState.empty
  have hr := StateT.run_map (m := ProbComp) Run.value
    ((code.inline (machineRoutines qS randomBound)).run (arithmetic F G₁ G₂ M M cost)
      (Machine.effects sampling (machineStore qS)) env) (machineState g X h .empty)
  simp only [StateT.run] at hs hl hr
  rw [hl, hr] at hs
  simp only [Functor.map_map] at hs
  have he := congrArg (fun c : ProbComp ((M × G₁) ×
      (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) => c >>= fun p =>
        (fun z => z.1.value) <$> ((machineFinish qS).run (arithmetic F G₁ G₂ M M cost)
          (Machine.effects sampling (machineStore qS)) (p.1, ())).run p.2) hs
  simp only [bind_map_left, machineFinish_erase (G₂ := G₂) cost sampling g X h qS] at he
  rw [machineReductionCode_run cost sampling g X h qS randomBound setup code env publicSteps hpublic]
  simpa only [reduction, map_bind, map_pure, StateT.run, bind_pure_comp, Functor.map_map] using he.symm

end Signatures.Runtime.Coron
