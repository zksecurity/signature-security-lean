import Proofs.Runtime.Machine
import Proofs.Runtime.GrowingState
import Proofs.Model.LazyAGM

/-! Closed-machine adaptive AGM oracle procedures. Reply computations are first-order
expressions; only primitive randomness and store effects remain in the compiled program.
Explicit replies are recorded in reverse order with charged constant-time list insertion. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.AGM

inductive Command (indexTy messageTy : Ty CryptoAtom) (randomBound : Nat) :
    Ty CryptoAtom → Ty CryptoAtom → Type
  | random (n : Fin (randomBound + 1)) : Command indexTy messageTy randomBound .unit (boundedNat n.val)
  | hash : Command indexTy messageTy randomBound indexTy point₁
  | sign : Command indexTy messageTy randomBound messageTy point₁

def kind {indexTy messageTy r a b} : Command indexTy messageTy r a b → Fin 3
  | .random _ => 0
  | .hash => 1
  | .sign => 2

abbrev transcriptTy (indexTy messageTy : Ty CryptoAtom) : Ty CryptoAtom :=
  .pair (.list (.pair indexTy point₁)) (.list (.pair messageTy point₁))

abbrev oracleStore (indexTy messageTy configTy : Ty CryptoAtom) : Ty CryptoAtom :=
  .pair configTy (transcriptTy indexTy messageTy)

private def v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private def v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private def v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))

variable {indexTy messageTy configTy : Ty CryptoAtom}

def machineHash (response : Expr CryptoOp [indexTy, configTy] point₁) :
    Program CryptoOp (Machine.Effect (oracleStore indexTy messageTy configTy)) [indexTy] point₁ :=
  .bind (.query .read .unit)
    (.bind (.call (.ret response) (.cons v1 (.cons (.fst v0) .nil)))
      (.bind (.query .write (.pair (.fst v1)
        (.pair (.cons (.pair v2 v0) (.fst (.snd v1))) (.snd (.snd v1)))))
        (.ret v1)))

def machineSign (response : Expr CryptoOp [messageTy, configTy] point₁) :
    Program CryptoOp (Machine.Effect (oracleStore indexTy messageTy configTy)) [messageTy] point₁ :=
  .bind (.query .read .unit)
    (.bind (.call (.ret response) (.cons v1 (.cons (.fst v0) .nil)))
      (.bind (.query .write (.pair (.fst v1)
        (.pair (.fst (.snd v1)) (.cons (.pair v2 v0) (.snd (.snd v1))))))
        (.ret v1)))

def machineRoutines (hash : Expr CryptoOp [indexTy, configTy] point₁)
    (sign : Expr CryptoOp [messageTy, configTy] point₁) (randomBound : Nat)
    {a b} (cmd : Command indexTy messageTy randomBound a b) :
    Program CryptoOp (Machine.Effect (oracleStore indexTy messageTy configTy)) [a] b := match cmd with
  | .random n => .query (.uniform n.val) .unit
  | .hash => machineHash hash
  | .sign => machineSign sign

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

theorem machineHash_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (response : Expr CryptoOp [indexTy, configTy] point₁)
    (i : indexTy.Value (cryptoBase F G₁ G₂ K M))
    (cfg : configTy.Value (cryptoBase F G₁ G₂ K M))
    (tr : (transcriptTy indexTy messageTy).Value (cryptoBase F G₁ G₂ K M)) :
    ((machineHash response).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling (oracleStore indexTy messageTy configTy)) (i, ())).run (cfg, tr) =
      let r := response.run (arithmetic F G₁ G₂ K M cost) (i, cfg, ())
      pure (⟨r.value, r.steps + 40⟩, (cfg, (i, r.value) :: tr.1, tr.2)) := by
  dsimp [machineHash, Program.run, Args.run, Expr.run, v0, v1, v2,
    Var.get, Var.depth, StateT.run, StateT.bind, StateT.pure, Machine.effects]
  simp only [pure_bind]
  congr 3
  omega

theorem machineSign_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (response : Expr CryptoOp [messageTy, configTy] point₁)
    (m : messageTy.Value (cryptoBase F G₁ G₂ K M))
    (cfg : configTy.Value (cryptoBase F G₁ G₂ K M))
    (tr : (transcriptTy indexTy messageTy).Value (cryptoBase F G₁ G₂ K M)) :
    ((machineSign response).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling (oracleStore indexTy messageTy configTy)) (m, ())).run (cfg, tr) =
      let r := response.run (arithmetic F G₁ G₂ K M cost) (m, cfg, ())
      pure (⟨r.value, r.steps + 40⟩, (cfg, tr.1, (m, r.value) :: tr.2)) := by
  dsimp [machineSign, Program.run, Args.run, Expr.run, v0, v1, v2,
    Var.get, Var.depth, StateT.run, StateT.bind, StateT.pure, Machine.effects]
  simp only [pure_bind]
  congr 3
  omega

noncomputable def machineHandler (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (hash : Expr CryptoOp [indexTy, configTy] point₁)
    (sign : Expr CryptoOp [messageTy, configTy] point₁) (randomBound : Nat) :
    HandlerM (cryptoBase F G₁ G₂ K M) (Command indexTy messageTy randomBound)
      (StateT ((oracleStore indexTy messageTy configTy).Value (cryptoBase F G₁ G₂ K M)) ProbComp) :=
  routineHandler (arithmetic F G₁ G₂ K M cost)
    (Machine.effects sampling (oracleStore indexTy messageTy configTy))
    (machineRoutines hash sign randomBound)

theorem machineHandler_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (hash : Expr CryptoOp [indexTy, configTy] point₁)
    (sign : Expr CryptoOp [messageTy, configTy] point₁) (randomBound : Nat)
    {a b} (cmd : Command indexTy messageTy randomBound a b)
    (arg : a.Value (cryptoBase F G₁ G₂ K M))
    (state : (oracleStore indexTy messageTy configTy).Value (cryptoBase F G₁ G₂ K M)) :
    (machineHandler cost sampling hash sign randomBound cmd arg).run state =
      (fun p => (⟨p.1.value, p.1.steps + 3⟩, p.2)) <$>
        ((machineRoutines hash sign randomBound cmd).run (arithmetic F G₁ G₂ K M cost)
          (Machine.effects sampling (oracleStore indexTy messageTy configTy)) (arg, ())).run state := by
  simp [machineHandler, routineHandler, bind_pure_comp]

theorem machineHandler_hash_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (hash : Expr CryptoOp [indexTy, configTy] point₁)
    (sign : Expr CryptoOp [messageTy, configTy] point₁) (randomBound : Nat)
    (i : indexTy.Value (cryptoBase F G₁ G₂ K M))
    (cfg : configTy.Value (cryptoBase F G₁ G₂ K M))
    (tr : (transcriptTy indexTy messageTy).Value (cryptoBase F G₁ G₂ K M)) :
    (machineHandler cost sampling hash sign randomBound .hash i).run (cfg, tr) =
      let r := hash.run (arithmetic F G₁ G₂ K M cost) (i, cfg, ())
      pure (⟨r.value, r.steps + 43⟩, (cfg, (i, r.value) :: tr.1, tr.2)) := by
  rw [machineHandler_run]
  simp only [machineRoutines,
    machineHash_run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M), map_pure]

theorem machineHandler_sign_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (hash : Expr CryptoOp [indexTy, configTy] point₁)
    (sign : Expr CryptoOp [messageTy, configTy] point₁) (randomBound : Nat)
    (m : messageTy.Value (cryptoBase F G₁ G₂ K M))
    (cfg : configTy.Value (cryptoBase F G₁ G₂ K M))
    (tr : (transcriptTy indexTy messageTy).Value (cryptoBase F G₁ G₂ K M)) :
    (machineHandler cost sampling hash sign randomBound .sign m).run (cfg, tr) =
      let r := sign.run (arithmetic F G₁ G₂ K M cost) (m, cfg, ())
      pure (⟨r.value, r.steps + 43⟩, (cfg, tr.1, (m, r.value) :: tr.2)) := by
  rw [machineHandler_run]
  simp only [machineRoutines,
    machineSign_run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M), map_pure]

theorem machineHandler_random_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (hash : Expr CryptoOp [indexTy, configTy] point₁)
    (sign : Expr CryptoOp [messageTy, configTy] point₁) (randomBound : Nat)
    (n : Fin (randomBound + 1))
    (state : (oracleStore indexTy messageTy configTy).Value (cryptoBase F G₁ G₂ K M)) :
    (machineHandler cost sampling hash sign randomBound (.random n) ()).run state =
      (fun x => (⟨x, sampling.uniform n.val + 5⟩, state)) <$>
        (liftM (unifSpec.query n.val) : ProbComp (Fin (n.val + 1))) := by
  rw [machineHandler_run]
  dsimp [machineRoutines, Program.run, Expr.run, Machine.effects, StateT.run, StateT.bind, StateT.pure]
  simp only [bind_pure_comp, Functor.map_map]
  congr 1
  funext x
  congr 2
  omega

def machinePrices (sampling : Machine.SamplingCosts) (randomBound cHash cSign : Nat) (k : Fin 3) : Nat :=
  if k = 0 then (Finset.univ.sup fun n : Fin (randomBound + 1) => sampling.uniform n.val) + 5
  else if k = 1 then cHash + 43 else cSign + 43

def transcriptSize
    (state : (oracleStore indexTy messageTy configTy).Value (cryptoBase F G₁ G₂ K M)) : Nat :=
  state.2.1.length + state.2.2.length

def replies (randomBound : Nat) : ReplyContract (cryptoBase F G₁ G₂ K M)
    (Command indexTy messageTy randomBound) where
  allows := fun _ _ _ => True
  responds := by
    intro a b cmd arg
    cases cmd with
    | random n => exact ⟨0, trivial⟩
    | hash => exact ⟨0, trivial⟩
    | sign => exact ⟨0, trivial⟩

theorem machineHandler_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (hash : Expr CryptoOp [indexTy, configTy] point₁)
    (sign : Expr CryptoOp [messageTy, configTy] point₁) (randomBound cHash cSign : Nat)
    (cfg : configTy.Value (cryptoBase F G₁ G₂ K M))
    (hHash : ∀ i, (hash.run (arithmetic F G₁ G₂ K M cost) (i, cfg, ())).steps ≤ cHash)
    (hSign : ∀ m, (sign.run (arithmetic F G₁ G₂ K M cost) (m, cfg, ())).steps ≤ cSign)
    {a b} (cmd : Command indexTy messageTy randomBound a b)
    (arg : a.Value (cryptoBase F G₁ G₂ K M))
    (tr : (transcriptTy indexTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (z : Run (b.Value (cryptoBase F G₁ G₂ K M)) ×
      (oracleStore indexTy messageTy configTy).Value (cryptoBase F G₁ G₂ K M))
    (hz : z ∈ support ((machineHandler cost sampling hash sign randomBound cmd arg).run (cfg, tr))) :
    z.2.1 = cfg ∧ transcriptSize z.2 ≤ tr.1.length + tr.2.length + 1 ∧
      z.1.steps ≤ machinePrices sampling randomBound cHash cSign (kind cmd) := by
  rw [machineHandler_run] at hz
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  cases cmd with
  | random n =>
      dsimp [machineRoutines, Program.run, Expr.run, Machine.effects,
        StateT.run, StateT.bind, StateT.pure] at hr
      simp only [bind_pure_comp, Functor.map_map, support_map, Set.mem_image] at hr
      obtain ⟨v, _, rfl⟩ := hr
      have hn : sampling.uniform n.val ≤
          Finset.univ.sup (fun n : Fin (randomBound + 1) => sampling.uniform n.val) :=
        Finset.le_sup (f := fun n : Fin (randomBound + 1) => sampling.uniform n.val) (Finset.mem_univ n)
      simp only [kind, machinePrices, Fin.isValue, ite_true, transcriptSize]
      exact ⟨trivial, Nat.le_succ _, by omega⟩
  | hash =>
      simp only [machineRoutines,
        machineHash_run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
        support_pure, Set.mem_singleton_iff] at hr
      subst r
      simp only [kind, machinePrices, Fin.isValue, Fin.reduceEq, ite_false, ite_true,
        transcriptSize, List.length_cons]
      exact ⟨trivial, by omega, by have := hHash arg; omega⟩
  | sign =>
      simp only [machineRoutines,
        machineSign_run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
        support_pure, Set.mem_singleton_iff] at hr
      subst r
      simp only [kind, machinePrices, Fin.isValue, Fin.reduceEq, ite_false,
        transcriptSize, List.length_cons]
      exact ⟨trivial, by omega, by have := hSign arg; omega⟩

theorem machineSimulation_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (hash : Expr CryptoOp [indexTy, configTy] point₁)
    (sign : Expr CryptoOp [messageTy, configTy] point₁) (randomBound cHash cSign : Nat)
    (cfg : configTy.Value (cryptoBase F G₁ G₂ K M))
    (hHash : ∀ i, (hash.run (arithmetic F G₁ G₂ K M cost) (i, cfg, ())).steps ≤ cHash)
    (hSign : ∀ m, (sign.run (arithmetic F G₁ G₂ K M cost) (m, cfg, ())).steps ≤ cSign)
    {Γ a} (code : Program CryptoOp (Command indexTy messageTy randomBound) Γ a)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      code env localTime queries)
    (z : Run (a.Value (cryptoBase F G₁ G₂ K M)) ×
      (oracleStore indexTy messageTy configTy).Value (cryptoBase F G₁ G₂ K M))
    (hz : z ∈ support (((code.inline (machineRoutines hash sign randomBound)).run
      (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling (oracleStore indexTy messageTy configTy))
      env).run (cfg, [], []))) :
    z.2.1 = cfg ∧ transcriptSize z.2 ≤ ∑ k, queries k ∧
      z.1.steps ≤ localTime + ∑ k, queries k * machinePrices sampling randomBound cHash cSign k := by
  rw [Program.inline_run] at hz
  have hb := SourceBudget.linear_state_bound (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
    code env localTime queries hsource (machineHandler cost sampling hash sign randomBound)
    (machinePrices sampling randomBound cHash cSign) 0
    (fun state => state.1 = cfg) transcriptSize (by
      intro a b cmd arg state hs out hout
      rcases state with ⟨cfg', tr⟩
      dsimp at hs
      subst cfg'
      have h := machineHandler_bound cost sampling hash sign randomBound cHash cSign cfg
        hHash hSign cmd arg tr out hout
      exact ⟨h.1, trivial, h.2.1, by simpa using h.2.2⟩)
    (cfg, [], []) rfl rfl z hz
  simpa using hb

end Signatures.Runtime.AGM
