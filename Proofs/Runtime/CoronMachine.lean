import Proofs.Runtime.CoronSimulation
import Proofs.Runtime.Machine

/-! First-order implementations of Coron's adaptive replies in the closed machine.
The public challenge and the three persistent lists are explicit store fields. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Coron

abbrev machineStore (qS : Nat) : Ty CryptoAtom :=
  .pair (.pair point₁ (.pair point₁ point₁))
    (.pair (.list (.pair message scalar))
      (.pair (.list (.pair message (boundedNat qS))) (.list message)))

private def v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private def v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private def v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))
private def v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d :=
  .var (.there (.there (.there .here)))

def machineReply (qS : Nat) (signing : Bool) :
    Program CryptoOp (Machine.Effect (machineStore qS)) [message] point₁ :=
  .bind (.query .read .unit)
    (.bind (.call (cacheGet .messageEq .scalar)
      (.cons v1 (.cons (.op .zero .unit) (.cons (.fst (.snd v0)) .nil))))
      (.bind (.call (cacheGet .messageEq (.uniform qS))
        (.cons v2 (.cons (.op (.finZero qS) .unit)
          (.cons (.fst (.snd (.snd v1))) .nil))))
        (.bind (.query .write
          (.pair (.fst v2) (.pair (.snd v1) (.pair (.snd v0)
            (if signing then .cons v3 (.snd (.snd (.snd v2)))
              else .snd (.snd (.snd v2)))))))
          (if signing then
            .call (.ret signReply)
              (.cons (.fst v2) (.cons (.fst (.snd (.fst v3)))
                (.cons (.op (.finVal qS) (.fst v1)) .nil)))
          else
            .call (.ret hashReply)
              (.cons (.fst v2) (.cons (.fst (.fst v3))
                (.cons (.snd (.snd (.fst v3)))
                  (.cons (.op (.finVal qS) (.fst v1)) .nil))))))))

variable {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]

def machineState {qS : Nat} (g X h : G₁) (s : CacheState F M qS) :
    (machineStore qS).Value (cryptoBase F G₁ G₂ M M) :=
  ((g, X, h), s.scalars, s.coins, s.signed)

def machineSampling (sampling : Machine.SamplingCosts) (qS : Nat) : SamplingCosts :=
  ⟨sampling.scalar, sampling.uniform qS, 0⟩

theorem machineScalarCache_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (qS : Nat) (m : M) (xs : List (M × F))
    (s : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) :
    ((cacheGet CryptoOp.messageEq (Machine.Effect.scalar (store := machineStore qS))).run
      (arithmetic F G₁ G₂ M M cost) (Machine.effects sampling (machineStore qS))
      (m, 0, xs, ())).run s =
      (fun r => (r, s)) <$> (cacheGet CryptoOp.messageEq (Draw.scalar (qS := qS))).run
        (arithmetic F G₁ G₂ M M cost) (draws qS (machineSampling sampling qS)) (m, 0, xs, ()) := by
  apply cacheGet_run_state
  intro state
  simp [Machine.effects, draws, machineSampling, StateT.run]

theorem machineCoinCache_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (qS : Nat) (m : M) (xs : List (M × Fin (qS + 1)))
    (s : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) :
    ((cacheGet CryptoOp.messageEq (Machine.Effect.uniform (store := machineStore qS) qS)).run
      (arithmetic F G₁ G₂ M M cost) (Machine.effects sampling (machineStore qS))
      (m, 0, xs, ())).run s =
      (fun r => (r, s)) <$> (cacheGet CryptoOp.messageEq (Draw.coin (qS := qS))).run
        (arithmetic F G₁ G₂ M M cost) (draws qS (machineSampling sampling qS)) (m, 0, xs, ()) := by
  apply cacheGet_run_state
  intro state
  simp [Machine.effects, draws, machineSampling, StateT.run]

set_option maxHeartbeats 800000 in
/-- Exact overhead of compiling the adapter into instructions, including the bounded-zero
literal, all call arguments, store projections, and persistent-list updates. -/
theorem machineReply_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (qS : Nat) (signing : Bool) (m : M) (state : CacheState F M qS) :
    ((machineReply qS signing).run (arithmetic F G₁ G₂ M M cost)
      (Machine.effects sampling (machineStore qS)) (m, ())).run (machineState g X h state) =
      (fun z => (⟨z.1.value, z.1.steps + cost.natOp + (if signing then 45 else 47)⟩,
        machineState g X h z.2)) <$>
        (reply (G₂ := G₂) cost (machineSampling sampling qS) g X h qS signing m).run state := by
  have hs := machineScalarCache_run (G₂ := G₂) cost sampling qS m state.scalars
    (machineState g X h state)
  have hc := machineCoinCache_run (F := F) (G₁ := G₁) (G₂ := G₂) cost sampling qS m state.coins
  simp only [StateT.run, machineState] at hs hc
  have hz : (arithmetic F G₁ G₂ M M cost).execute CryptoOp.zero () = 0 := rfl
  have hk : (arithmetic F G₁ G₂ M M cost).execute (CryptoOp.finZero qS) () = 0 := rfl
  cases signing <;>
    simp only [machineReply, Bool.false_eq_true, ite_false, ite_true] <;>
    dsimp [Program.run, Args.run, Expr.run, v0, v1, v2, v3,
      Var.get, Var.depth, StateT.run, StateT.bind, StateT.pure, machineState] <;>
    simp only [Machine.effects, pure_bind, reply, cacheHandler, coinValue, StateT.run,
      map_bind, bind_map_left, map_pure, bind_pure_comp] <;>
    simp only [Expr.run, Var.get, Var.depth, hz, hk, hs, hc, bind_map_left,
      Bool.false_eq_true, ite_false, ite_true]
  all_goals
    congr 1
    funext rho
    simp only [Functor.map_map]
    congr 1
    funext coin
    congr 2
    dsimp [arithmetic, CryptoOp.price]
    omega

/-- Proof-only view of the persistent lists; the executable program uses projections. -/
def machineCaches {qS : Nat} (s : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) :
    CacheState F M qS := ⟨s.2.1, s.2.2.1, s.2.2.2⟩

theorem machineReply_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (qS : Nat) (signing : Bool) (m : M) (state : CacheState F M qS)
    (z : Run G₁ × (machineStore qS).Value (cryptoBase F G₁ G₂ M M))
    (hz : z ∈ support (((machineReply qS signing).run (arithmetic F G₁ G₂ M M cost)
      (Machine.effects sampling (machineStore qS)) (m, ())).run (machineState g X h state))) :
    (machineCaches z.2).size ≤ state.size + 1 ∧
      z.1.steps ≤ replyBase cost (machineSampling sampling qS) signing + cost.natOp +
        (if signing then 45 else 47) + 2 * (cost.messageEq + 19) * state.size := by
  rw [machineReply_run] at hz
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  have hb := reply_bound (G₂ := G₂) cost (machineSampling sampling qS) g X h qS signing m state r hr
  exact ⟨hb.1, by dsimp; omega⟩

def machineRoutines (qS randomBound : Nat) {a b} (cmd : Command randomBound a b) :
    Program CryptoOp (Machine.Effect (machineStore qS)) [a] b := match cmd with
  | .random n => .query (.uniform n.val) .unit
  | .hash => machineReply qS false
  | .sign => machineReply qS true

noncomputable def machineHandler (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (qS randomBound : Nat) : HandlerM (cryptoBase F G₁ G₂ M M) (Command randomBound)
      (StateT ((machineStore qS).Value (cryptoBase F G₁ G₂ M M)) ProbComp) :=
  routineHandler (arithmetic F G₁ G₂ M M cost) (Machine.effects sampling (machineStore qS))
    (machineRoutines qS randomBound)

theorem machineHandler_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (qS randomBound : Nat) {a b} (cmd : Command randomBound a b)
    (arg : a.Value (cryptoBase F G₁ G₂ M M))
    (state : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) :
    (machineHandler cost sampling qS randomBound cmd arg).run state =
      (fun p => (⟨p.1.value, p.1.steps + 3⟩, p.2)) <$>
        ((machineRoutines qS randomBound cmd).run (arithmetic F G₁ G₂ M M cost)
          (Machine.effects sampling (machineStore qS)) (arg, ())).run state := by
  simp [machineHandler, routineHandler, bind_pure_comp]

def machinePrices (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (qS randomBound : Nat) (k : Fin 3) : Nat :=
  if k = 0 then (Finset.univ.sup fun n : Fin (randomBound + 1) => sampling.uniform n.val) + 5
  else replyBase cost (machineSampling sampling qS) (k == 2) + cost.natOp +
    (if k = 2 then 48 else 50)

theorem machineHandler_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (qS randomBound : Nat) {a b} (cmd : Command randomBound a b)
    (arg : a.Value (cryptoBase F G₁ G₂ M M))
    (state : (machineStore qS).Value (cryptoBase F G₁ G₂ M M))
    (z : Run (b.Value (cryptoBase F G₁ G₂ M M)) ×
      (machineStore qS).Value (cryptoBase F G₁ G₂ M M))
    (hz : z ∈ support ((machineHandler cost sampling qS randomBound cmd arg).run state)) :
    (machineCaches z.2).size ≤ (machineCaches state).size + 1 ∧
      z.1.steps ≤ machinePrices cost sampling qS randomBound (kind cmd) +
        2 * (cost.messageEq + 19) * (machineCaches state).size := by
  rw [machineHandler_run] at hz
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  rcases state with ⟨⟨g, X, h⟩, scalars, coins, signed⟩
  cases cmd with
  | random n =>
      dsimp [machineRoutines, Program.run, Expr.run, Machine.effects,
        StateT.run, StateT.bind, StateT.pure] at hr
      simp only [bind_pure_comp, Functor.map_map, support_map, Set.mem_image] at hr
      obtain ⟨v, _, rfl⟩ := hr
      have hn : sampling.uniform n.val ≤
          Finset.univ.sup (fun n : Fin (randomBound + 1) => sampling.uniform n.val) :=
        Finset.le_sup (f := fun n : Fin (randomBound + 1) => sampling.uniform n.val) (Finset.mem_univ n)
      simp only [kind, machinePrices, Fin.isValue, ite_true]
      exact ⟨Nat.le_succ _, by omega⟩
  | hash =>
      have hb := machineReply_bound cost sampling g X h qS false arg
        ⟨scalars, coins, signed⟩ r hr
      simp only [kind, machinePrices, Fin.isValue, Fin.reduceEq, ite_false,
        Bool.false_eq_true, show ((1 : Fin 3) == 2) = false from rfl] at *
      exact ⟨hb.1, by simp only [machineCaches] at *; omega⟩
  | sign =>
      have hb := machineReply_bound cost sampling g X h qS true arg
        ⟨scalars, coins, signed⟩ r hr
      simp only [kind, machinePrices, Fin.isValue, Fin.reduceEq, ite_false, ite_true,
        beq_self_eq_true] at *
      exact ⟨hb.1, by simp only [machineCaches] at *; omega⟩

/-- The bound applies to the inlined closed-machine program on every adaptive response path.
It includes all procedure-call overhead; no hash/sign capability remains in the target. -/
theorem machineSimulation_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (qS randomBound : Nat) {Γ a}
    (code : Program CryptoOp (Command randomBound) Γ a)
    (env : Env (cryptoBase F G₁ G₂ M M) Γ) (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ M M cost) (replies randomBound) kind
      code env localTime queries)
    (z : Run (a.Value (cryptoBase F G₁ G₂ M M)) ×
      (machineStore qS).Value (cryptoBase F G₁ G₂ M M))
    (hz : z ∈ support (((code.inline (machineRoutines qS randomBound)).run
      (arithmetic F G₁ G₂ M M cost) (Machine.effects sampling (machineStore qS)) env).run
        (machineState g X h .empty))) :
    (machineCaches z.2).size ≤ ∑ k, queries k ∧
      z.1.steps ≤ localTime + (∑ k, queries k * machinePrices cost sampling qS randomBound k) +
        2 * (cost.messageEq + 19) * (∑ k, queries k) ^ 2 := by
  rw [Program.inline_run] at hz
  have hb := SourceBudget.linear_state_bound (arithmetic F G₁ G₂ M M cost) (replies randomBound) kind
    code env localTime queries hsource (machineHandler cost sampling qS randomBound)
    (machinePrices cost sampling qS randomBound) (2 * (cost.messageEq + 19))
    (fun _ => True) (fun s => (machineCaches s).size) (by
      intro a b cmd arg state _ out hout
      exact ⟨trivial, trivial, machineHandler_bound cost sampling qS randomBound cmd arg state out hout⟩)
    (machineState g X h .empty) trivial rfl z hz
  exact hb.2

theorem machineHandler_erase (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (qS randomBound : Nat) {a b} (cmd : Command randomBound a b)
    (arg : a.Value (cryptoBase F G₁ G₂ M M)) (state : CacheState F M qS) :
    (fun p => (p.1.value, machineState g X h p.2)) <$>
        (handler cost (machineSampling sampling qS) g X h qS randomBound cmd arg).run state =
      (fun p => (p.1.value, p.2)) <$>
        (machineHandler cost sampling qS randomBound cmd arg).run (machineState g X h state) := by
  rw [machineHandler_run]
  cases cmd with
  | random n =>
      dsimp [machineRoutines, Program.run, Expr.run, Machine.effects, handler,
        StateT.run, StateT.bind, StateT.pure]
      simp
  | hash =>
      simp only [machineRoutines, handler, Functor.map_map]
      rw [machineReply_run (G₂ := G₂) cost sampling g X h qS false arg state]
      simp only [Functor.map_map]
  | sign =>
      simp only [machineRoutines, handler, Functor.map_map]
      rw [machineReply_run (G₂ := G₂) cost sampling g X h qS true arg state]
      simp only [Functor.map_map]

theorem machineHandler_refines (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (qS randomBound : Nat) {a b} (cmd : Command randomBound a b)
    (arg : a.Value (cryptoBase F G₁ G₂ M M)) :
    StateRefines (machineState g X h)
      (Run.value <$> handler cost (machineSampling sampling qS) g X h qS randomBound cmd arg)
      (Run.value <$> machineHandler cost sampling qS randomBound cmd arg) := by
  intro state
  have hl := StateT.run_map (m := ProbComp) Run.value
    (handler cost (machineSampling sampling qS) g X h qS randomBound cmd arg) state
  have hr := StateT.run_map (m := ProbComp) Run.value
    (machineHandler cost sampling qS randomBound cmd arg) (machineState g X h state)
  simp only [StateT.run] at hl hr ⊢
  rw [hl, hr]
  simpa only [Functor.map_map, StateT.run] using
    machineHandler_erase (G₂ := G₂) cost sampling g X h qS randomBound cmd arg state

/-- Inlining preserves every adaptive result and persistent state, not just the final
success probability. This is the bridge from target code to the existing evaluator. -/
theorem machineSimulation_refines (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (qS randomBound : Nat) {Γ a}
    (code : Program CryptoOp (Command randomBound) Γ a)
    (env : Env (cryptoBase F G₁ G₂ M M) Γ) :
    StateRefines (machineState g X h)
      (Run.value <$> code.run (arithmetic F G₁ G₂ M M cost)
        (handler cost (machineSampling sampling qS) g X h qS randomBound) env)
      (Run.value <$> (code.inline (machineRoutines qS randomBound)).run
        (arithmetic F G₁ G₂ M M cost) (Machine.effects sampling (machineStore qS)) env) := by
  rw [Program.inline_run, Program.run_erase, Program.run_erase]
  exact code.denote_refines (arithmetic F G₁ G₂ M M cost) (machineState g X h) _ _
    (machineHandler_refines cost sampling g X h qS randomBound) env

end Signatures.Runtime.Coron
