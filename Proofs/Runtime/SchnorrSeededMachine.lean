import Proofs.Runtime.SchnorrSeededPassBudget
import Proofs.Runtime.SchnorrForkCorrectness

/-! A first-order controller for the fully seeded fork. The original seed stays
in a register across both passes. Only the hash family is reset; each pass starts
with empty caches. Replacement and fallback samples are primitive fresh draws. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.SeedTape

private def v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private def v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private def v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))
private def v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d := .var (.there (.there (.there .here)))
private def v4 {a b c d e Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: Γ) e :=
  .var (.there (.there (.there (.there .here))))
private def v5 {a b c d e f Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: f :: Γ) f :=
  .var (.there (.there (.there (.there (.there .here)))))
private def v6 {a b c d e f g Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: f :: g :: Γ) g :=
  .var (.there (.there (.there (.there (.there (.there .here))))))
private def v7 {a b c d e f g h Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: f :: g :: h :: Γ) h :=
  .var (.there (.there (.there (.there (.there (.there (.there .here)))))))

def emptyState {Γ} (g pk : Expr CryptoOp Γ point₁)
    (tape : Expr CryptoOp Γ (.list Replay.Mixed.event)) : Expr CryptoOp Γ machineStore :=
  .pair (.pair (.pair g pk) (.pair .nil .nil)) tape

/-- Capture the final cache so selection uses the pass's own ordered hash answers. -/
def capturePass {Γ} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) Γ forgery) :
    Program CryptoOp (Machine.Effect machineStore) Γ cachePassOutput :=
  .bind (passCode randomBound source)
    (.bind (.query .read .unit) (.ret (.pair v1 (.fst v0))))

/-- Discard the previous store before executing the source from its root. -/
def runWithTape {dataTy} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery) :
    Program CryptoOp (Machine.Effect machineStore)
      [.list Replay.Mixed.event, point₁, point₁, dataTy] cachePassOutput :=
  .bind (.query .write (emptyState v2 v1 v0))
    (.call (capturePass randomBound source) (.cons v2 (.cons v4 .nil)))

private def commitment {Γ} (x : Expr CryptoOp Γ cachePassOutput) : Expr CryptoOp Γ point₁ :=
  .fst (.snd (.fst (.fst x)))
private def response {Γ} (x : Expr CryptoOp Γ cachePassOutput) : Expr CryptoOp Γ scalar :=
  .snd (.snd (.fst (.fst x)))
private def challenge {Γ} (x : Expr CryptoOp Γ cachePassOutput) : Expr CryptoOp Γ scalar :=
  .snd (.fst x)
private def fallback {Γ} : Program CryptoOp (Machine.Effect machineStore) Γ scalar :=
  .query .scalar .unit

def finishGuards : Expr CryptoOp [cachePassOutput, cachePassOutput, indexResult, .nat] .bool :=
  .branch (.fst v2)
    (.branch (.op .natEq (.pair (.snd v2) v3))
      (.branch (.op .point₁Eq (.pair (commitment v0) (commitment v1)))
        (.branch (.op .scalarEq (.pair (challenge v0) (challenge v1))) (.bool false) (.bool true))
        (.bool false))
      (.bool false))
    (.bool false)

def finishFork : Program CryptoOp (Machine.Effect machineStore)
    [cachePassOutput, cachePassOutput, indexResult, .nat] scalar :=
  .branch finishGuards
    (.call (.ret extract) (.cons (response v0) (.cons (response v1)
      (.cons (challenge v0) (.cons (challenge v1) .nil)))))
    fallback

/-- The saved seed, first output, selected index, fresh answer, and fixed source inputs. -/
def secondStage {dataTy} (qH randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery) :
    Program CryptoOp (Machine.Effect machineStore)
      [.list Replay.Mixed.event, cachePassOutput, .nat, scalar, point₁, point₁, dataTy] scalar :=
  .bind (.call (.ret resetCode) (.cons (.nat 1) (.cons v2 (.cons v0
    (.cons (.pair (.nat 1) (.pair v3 (.nat 0))) .nil)))))
    (.bind (.call (runWithTape randomBound source) (.cons v0 (.cons v5 (.cons v6 (.cons v7 .nil)))))
      (.bind (.call selectCode (.cons (.fst v0) (.cons (.snd v0) (.cons (.nat qH) .nil))))
        (.call finishFork (.cons v4 (.cons v1 (.cons v0 (.cons v5 .nil)))))))

/-- A missing selected seed entry is not a collision. In particular the fresh
answer is still installed and the second pass is executed on that branch. -/
def firstStage {dataTy} (qH randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery) :
    Program CryptoOp (Machine.Effect machineStore)
      [.list Replay.Mixed.event, cachePassOutput, point₁, point₁, dataTy] scalar :=
  .bind (.call selectCode (.cons (.fst v1) (.cons (.snd v1) (.cons (.nat qH) .nil))))
    (.branch (.fst v0)
      (.bind (.query .scalar .unit)
        (.bind (.call (.ret scanCode) (.cons (.snd v1) (.cons v2 .nil)))
          (.branch (.branch (.fst v0) (.op .scalarEq (.pair (.fst (.snd v0)) v1)) (.bool false))
            fallback
            (.call (secondStage qH randomBound source)
              (.cons v3 (.cons v4 (.cons (.snd v2) (.cons v1
                (.cons v5 (.cons v6 (.cons v7 .nil)))))))))))
      fallback)

/-- The complete executable fork. Family capacities and qH are compiled
constants; loading their numeric values is charged by the machine language. -/
def forkCode {dataTy} (capacity : Family → Nat) (families : List Family) (qH randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery) :
    Machine.Code [point₁, point₁, dataTy] scalar where
  store := machineStore
  init := emptyState v1 v0 .nil
  body := .bind (.call (generateCode machineStore capacity families) .nil)
    (.bind (.call (runWithTape randomBound source) (.cons v0 (.cons v1 (.cons v2 (.cons v3 .nil)))))
      (.call (firstStage qH randomBound source)
        (.cons v1 (.cons v0 (.cons v2 (.cons v3 (.cons v4 .nil)))))))

def sourceForkCode {dataTy} (qH randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (localTime : Nat) (queries : Fin 3 → Nat) : Machine.Code [point₁, point₁, dataTy] scalar :=
  forkCode (Seeded.budget source localTime queries qH) (sourceFamilies source) qH randomBound source

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem capturePass_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ} (randomBound : Nat) (source : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (s : machineStore.Value (cryptoBase F G₁ G₂ K M)) :
    ((capturePass randomBound source).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling machineStore) env).run s =
      (fun p => (⟨(p.1.value, p.2.1), p.1.steps + 11⟩, p.2)) <$>
        ((passCode randomBound source).run (arithmetic F G₁ G₂ K M cost)
          (Machine.effects sampling machineStore) env).run s := by
  unfold capturePass
  generalize passCode randomBound source = pass
  dsimp [Program.run, Args.run, Expr.run, v0, v1, Var.get, Var.depth,
    StateT.run, StateT.bind, StateT.pure, Machine.effects]
  simp only [map_pure, bind_pure_comp]

theorem runWithTape_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (tape : List (TapeCell F)) (pk g : G₁) (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (s : machineStore.Value (cryptoBase F G₁ G₂ K M)) :
    ((runWithTape randomBound source).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling machineStore) (tape, pk, g, data, ())).run s =
      (fun p => (⟨p.1.value, p.1.steps + 28⟩, p.2)) <$>
        ((capturePass randomBound source).run (arithmetic F G₁ G₂ K M cost)
          (Machine.effects sampling machineStore) (pk, data, ())).run (((g, pk), [], []), tape) := by
  unfold runWithTape
  generalize capturePass randomBound source = pass
  dsimp [Program.run, Args.run, Expr.run, v0, v1, v2, v4, emptyState, Var.get, Var.depth,
    StateT.run, StateT.bind, StateT.pure, Machine.effects]
  simp only [pure_bind, map_pure, bind_pure_comp, Functor.map_map]
  congr 1
  funext p
  apply congrArg (fun r => (r, p.2))
  apply congrArg (Run.mk _)
  omega

theorem capturePass_seeded (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ} (randomBound : Nat) (source : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (cache : cacheStore.Value (cryptoBase F G₁ G₂ K M)) (tape : List (TapeCell F)) :
    (fun p => p.1.value) <$> ((capturePass randomBound source).run
      (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling machineStore) env).run (cache, tape) =
      simulateQ samples ((simulateQ seededOracle
        ((macroPass cost randomBound source env).run cache)).run' (toSeed tape)) := by
  rw [capturePass_run, Functor.map_map]
  exact passCode_seeded cost sampling randomBound source env cache tape

theorem runWithTape_seeded (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (tape : List (TapeCell F)) (pk g : G₁) (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (s : machineStore.Value (cryptoBase F G₁ G₂ K M)) :
    (fun p => p.1.value) <$> ((runWithTape randomBound source).run
      (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling machineStore)
      (tape, pk, g, data, ())).run s =
      simulateQ samples ((simulateQ seededOracle
        ((macroPass cost randomBound source (pk, data, ())).run ((g, pk), [], []))).run' (toSeed tape)) := by
  rw [runWithTape_run, Functor.map_map, capturePass_seeded]

omit [SampleableType F] [Field F] [DecidableEq F] in
theorem splitCells_answer (n : Nat) (xs : List (TapeCell F)) :
    (splitCells n xs).map Prod.snd = (values (.inr ()) xs)[n]? := by
  induction xs generalizing n with
  | nil => simp [splitCells, values]
  | cons x xs ih =>
      by_cases hx : x.1 = 1 <;> cases n <;>
        simp [splitCells, values, familyTag, decodeReply, hx, Option.map_map, Function.comp_def, ih]

omit [SampleableType F] in
theorem scanCode_collision (cost : PrimitiveCosts) (n : Nat) (xs : List (TapeCell F)) (fresh : F) :
    let r := scanCode.run (arithmetic F G₁ G₂ K M cost) (n, xs, ())
    (r.value.1 = true ∧ r.value.2.1 = fresh) ↔ (toSeed xs (.inr ()))[n]? = some fresh := by
  have h := congrArg (Option.map Prod.snd)
    (scanCode_split (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost n xs)
  rw [splitCells_answer] at h
  dsimp only [toSeed] at h ⊢
  rw [← h]
  split <;> simp_all

theorem selectionRun_seeded (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (p : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) (qH : Nat)
    (s : machineStore.Value (cryptoBase F G₁ G₂ K M)) :
    (selectCode.run (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling machineStore)
      (p.1, p.2, qH, ())).run s = pure (selectionRun cost (p.1, p.2, []) qH, s) := by
  rw [selectCode_run]
  unfold selectionRun
  dsimp only
  split <;> rfl

def accepted (first second : cachePassOutput.Value (cryptoBase F G₁ G₂ K M))
    (choice : Bool × Nat) (index : Nat) : Prop :=
  choice.1 = true ∧ choice.2 = index ∧ first.1.1.2.1 = second.1.1.2.1 ∧ first.1.2 ≠ second.1.2

instance (first second : cachePassOutput.Value (cryptoBase F G₁ G₂ K M))
    (choice : Bool × Nat) (index : Nat) : Decidable (accepted first second choice index) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

omit [SampleableType F] in
theorem finishGuards_denote (cost : PrimitiveCosts)
    (first second : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) (choice : Bool × Nat) (index : Nat) :
    finishGuards.denote (arithmetic F G₁ G₂ K M cost) (first, second, choice, index, ()) =
      decide (accepted first second choice index) := by
  by_cases h₁ : choice.1 = true <;> by_cases h₂ : choice.2 = index <;>
    by_cases h₃ : first.1.1.2.1 = second.1.1.2.1 <;> by_cases h₄ : first.1.2 = second.1.2 <;>
    simp [finishGuards, Expr.denote, v0, v1, v2, v3, commitment, challenge,
      Var.get, arithmetic, accepted, h₁, h₂, h₃, h₄]

private theorem state_map {S A B : Type} (f : A → B) (x : StateT S ProbComp A) (s : S) :
    (f <$> x) s = (fun p => (f p.1, p.2)) <$> x s := StateT.run_map _ _ _
private theorem state_pure {S A : Type} (a : A) (s : S) :
    (pure a : StateT S ProbComp A) s = pure (a, s) := rfl
private theorem state_bind {S A B : Type} (x : StateT S ProbComp A)
    (f : A → StateT S ProbComp B) (s : S) :
    (x >>= f) s = (x s >>= fun p => f p.1 p.2) := rfl

theorem finishFork_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (first second : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) (choice : Bool × Nat) (index : Nat)
    (s : machineStore.Value (cryptoBase F G₁ G₂ K M)) :
    (finishFork.run (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling machineStore)
      (first, second, choice, index, ())).run s =
      let checked := finishGuards.run (arithmetic F G₁ G₂ K M cost) (first, second, choice, index, ())
      if checked.value then
        let candidate := extract.run (arithmetic F G₁ G₂ K M cost)
          (first.1.1.2.2, second.1.1.2.2, first.1.2, second.1.2, ())
        pure (⟨candidate.value, checked.steps + candidate.steps + 27⟩, s)
      else (fun x => (⟨x, checked.steps + sampling.scalar + 3⟩, s)) <$> ($ᵗ F : ProbComp F) := by
  unfold finishFork
  generalize finishGuards = guards
  generalize extract = extraction
  dsimp [Program.run, Args.run, Expr.run, v0, v1, response, challenge, fallback,
    Var.get, Var.depth, StateT.run, StateT.bind, StateT.pure, Machine.effects]
  by_cases h : (guards.run (arithmetic F G₁ G₂ K M cost) (first, second, choice, index, ())).value = true
  · simp only [h, ite_true, pure_bind, state_pure]
    apply congrArg pure
    apply congrArg (fun r => (r, s))
    apply congrArg (Run.mk _)
    omega
  · simp only [h, Bool.false_eq_true, ite_false, state_map, Machine.effects,
      bind_pure_comp, Functor.map_map]
    congr 1
    funext x
    apply congrArg (fun r => (r, s))
    apply congrArg (Run.mk _)
    omega

theorem secondStage_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (qH randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (tape : List (TapeCell F)) (first : cachePassOutput.Value (cryptoBase F G₁ G₂ K M))
    (index : Nat) (fresh : F) (pk g : G₁) (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (s : machineStore.Value (cryptoBase F G₁ G₂ K M)) :
    ((secondStage qH randomBound source).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling machineStore) (tape, first, index, fresh, pk, g, data, ())).run s = (do
      let resetRun := resetCode.run (arithmetic F G₁ G₂ K M cost) (1, index, tape, (1, fresh, 0), ())
      let second ← ((runWithTape randomBound source).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling machineStore) (resetRun.value, pk, g, data, ())).run s
      let choice := selectionRun cost (second.1.value.1, second.1.value.2, []) qH
      let result ← (finishFork.run (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling machineStore)
        (first, second.1.value, choice.value, index, ())).run second.2
      pure (⟨result.1.value, resetRun.steps + second.1.steps + choice.steps + result.1.steps + qH + 87⟩,
        result.2)) := by
  unfold secondStage
  generalize resetCode = resetter
  generalize runWithTape randomBound source = pass
  generalize finishFork = finish
  simp only [Program.run, Args.run, Expr.run, v0, v1, v2, v3, v4, v5, v6, v7,
    Var.get, Var.depth]
  simp only [StateT.run, state_bind, state_pure, pure_bind, bind_pure_comp, state_map,
    bind_map_left, map_bind, map_pure, Functor.map_map]
  congr 1
  funext second
  have hselect := selectionRun_seeded cost sampling second.1.value qH second.2
  dsimp only [StateT.run] at hselect
  rw [hselect]
  simp only [pure_bind]
  congr 1
  funext result
  apply congrArg (fun r => (r, result.2))
  apply congrArg (Run.mk _)
  omega

set_option backward.isDefEq.respectTransparency false in
theorem firstStage_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (qH randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (tape : List (TapeCell F)) (first : cachePassOutput.Value (cryptoBase F G₁ G₂ K M))
    (pk g : G₁) (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (s : machineStore.Value (cryptoBase F G₁ G₂ K M)) :
    ((firstStage qH randomBound source).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling machineStore) (tape, first, pk, g, data, ())).run s =
      let choice := selectionRun cost (first.1, first.2, []) qH
      if choice.value.1 then (do
        let fresh ← ($ᵗ F : ProbComp F)
        let scan := scanCode.run (arithmetic F G₁ G₂ K M cost) (choice.value.2, tape, ())
        let checkPrice := if scan.value.1 then cost.scalarEq + 10 else 4
        if scan.value.1 = true ∧ scan.value.2.1 = fresh then
          (fun x => (⟨x, choice.steps + scan.steps + checkPrice + 2 * sampling.scalar + qH + 36⟩, s)) <$>
            ($ᵗ F : ProbComp F)
        else (fun result => (⟨result.1.value,
            choice.steps + scan.steps + checkPrice + sampling.scalar + result.1.steps + qH + 80⟩, result.2)) <$>
          ((secondStage qH randomBound source).run (arithmetic F G₁ G₂ K M cost)
            (Machine.effects sampling machineStore) (tape, first, choice.value.2, fresh, pk, g, data, ())).run s)
      else (fun x => (⟨x, choice.steps + sampling.scalar + qH + 19⟩, s)) <$> ($ᵗ F : ProbComp F) := by
  unfold firstStage
  generalize scanCode = scanner
  generalize secondStage qH randomBound source = stage
  simp only [Program.run, Args.run, Expr.run, v0, v1, v2, v3, v4, v5, v6, v7,
    Var.get, Var.depth]
  simp only [StateT.run, state_bind, state_map, pure_bind, bind_pure_comp, bind_map_left]
  have hselect := selectionRun_seeded cost sampling first qH s
  dsimp only [StateT.run] at hselect
  rw [hselect]
  simp only [pure_bind]
  split
  · simp only [state_bind, state_map, Machine.effects, bind_map_left, map_bind]
    congr 1
    funext fresh
    generalize scanner.run (arithmetic F G₁ G₂ K M cost)
      ((selectionRun cost (first.1, first.2, []) qH).value.2, tape, ()) = scanned
    by_cases hs : scanned.value.1 = true <;> by_cases he : scanned.value.2.1 = fresh <;>
      simp only [hs, he, true_and, false_and, ite_true, ite_false, arithmetic,
        CryptoOp.price, decide_true, decide_false, Bool.false_eq_true, fallback, Program.run,
        Expr.run, Machine.effects, state_map, bind_pure_comp, Functor.map_map]
    all_goals congr 1; funext result; congr 1; apply congrArg (Run.mk _); omega
  · simp only [fallback, Program.run, Expr.run, state_map, Machine.effects,
      bind_pure_comp, Functor.map_map]
    congr 1
    funext result
    congr 1
    apply congrArg (Run.mk _)
    omega

theorem forkCode_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (capacity : Family → Nat) (families : List Family) (qH randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (pk g : G₁) (data : dataTy.Value (cryptoBase F G₁ G₂ K M)) :
    (forkCode capacity families qH randomBound source).run cost sampling (pk, g, data, ()) = (do
      let seed ← ((generateCode machineStore capacity families).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling machineStore) ()).run (((g, pk), [], []), [])
      let first ← ((runWithTape randomBound source).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling machineStore) (seed.1.value, pk, g, data, ())).run seed.2
      let result ← ((firstStage qH randomBound source).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling machineStore) (seed.1.value, first.1.value, pk, g, data, ())).run first.2
      pure ⟨result.1.value, seed.1.steps + first.1.steps + result.1.steps + 57⟩) := by
  unfold forkCode Machine.Code.run
  generalize generateCode machineStore capacity families = setup
  generalize runWithTape randomBound source = pass
  generalize firstStage qH randomBound source = stage
  dsimp [Program.run, Args.run, Expr.run, emptyState, v0, v1, v2, v3, v4, Var.get, Var.depth]
  simp only [StateT.run, bind_pure_comp, bind_map_left, map_bind, Functor.map_map]
  congr 1
  funext seed
  congr 1
  funext first
  congr 1
  funext result
  apply congrArg (Run.mk _)
  omega

omit [SampleableType F] in
theorem finishGuards_steps (cost : PrimitiveCosts)
    (first second : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) (choice : Bool × Nat) (index : Nat) :
    (finishGuards.run (arithmetic F G₁ G₂ K M cost) (first, second, choice, index, ())).steps ≤
      cost.natOp + cost.point₁Eq + cost.scalarEq + 50 := by
  by_cases h₁ : choice.1 = true <;> by_cases h₂ : choice.2 = index <;>
    by_cases h₃ : first.1.1.2.1 = second.1.1.2.1 <;> by_cases h₄ : first.1.2 = second.1.2 <;>
    simp [finishGuards, Expr.run, v0, v1, v2, v3, commitment, challenge,
      arithmetic, CryptoOp.price, Var.get, Var.depth,
      h₁, h₂, h₃, h₄] <;> omega

end Signatures.Runtime.Schnorr.SeedTape
