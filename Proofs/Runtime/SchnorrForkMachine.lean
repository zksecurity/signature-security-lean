import Proofs.Runtime.SchnorrSelection
import Proofs.Runtime.ReplayScan

/-! The complete first-order Schnorr replay controller. It executes the source twice
from the root and only carries a recorded prefix between the two executions. -/

open OracleComp

namespace Signatures.Runtime.Schnorr

abbrev loggedOutput : Ty CryptoAtom := .pair observedForgery (.pair cacheStore (.list Replay.Mixed.event))

private theorem state_map {S A B : Type} (f : A → B) (x : StateT S ProbComp A) (s : S) :
    (f <$> x) s = (fun p => (f p.1, p.2)) <$> x s := StateT.run_map _ _ _

private theorem state_pure {S A : Type} (a : A) (s : S) :
    (pure a : StateT S ProbComp A) s = pure (a, s) := rfl

private theorem state_bind {S A B : Type} (x : StateT S ProbComp A)
    (f : A → StateT S ProbComp B) (s : S) :
    (x >>= f) s = (x s >>= fun p => f p.1 p.2) := rfl

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

def emptyReplay {Γ} (g pk : Expr CryptoOp Γ point₁) (limit : Expr CryptoOp Γ .nat)
    (tape : Expr CryptoOp Γ (.list Replay.Mixed.event)) : Expr CryptoOp Γ replayStore :=
  .pair (.pair (.pair g pk) (.pair .nil .nil))
    (.pair (.nat 0) (.pair limit (.pair tape .nil)))

/-- Include the final query and return a chronological random transcript. -/
def loggedPassProgram {Γ} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) Γ forgery) :
    Program CryptoOp (Machine.Effect replayStore) Γ loggedOutput :=
  .bind (replayPassProgram randomBound source)
    (.bind (.call (.ret reverseList)
      (.cons (.snd (.snd (.snd (.snd (.snd v0))))) .nil))
      (.ret (.pair (.fst v1) (.pair (.fst (.snd v1)) v0))))

private def commitment {Γ} (x : Expr CryptoOp Γ loggedOutput) : Expr CryptoOp Γ point₁ :=
  .fst (.snd (.fst (.fst x)))
private def response {Γ} (x : Expr CryptoOp Γ loggedOutput) : Expr CryptoOp Γ scalar :=
  .snd (.snd (.fst (.fst x)))
private def challenge {Γ} (x : Expr CryptoOp Γ loggedOutput) : Expr CryptoOp Γ scalar :=
  .snd (.fst x)
private def selectedAnswer {Γ} (x : Expr CryptoOp Γ scanResult) : Expr CryptoOp Γ scalar :=
  .fst (.snd x)
private def fallback {Γ} : Program CryptoOp (Machine.Effect replayStore) Γ scalar :=
  .query .scalar .unit

/-- First selection was accepted by the caller. Check the second selection, the changed
focused answer, and the upstream extractor's commitment/challenge guards. -/
def forkGuards : Expr CryptoOp
    [loggedOutput, loggedOutput, indexResult, indexResult, scanResult, scanResult] .bool :=
  .branch (.fst v3)
    (.branch (.op .natEq (.pair (.snd v2) (.snd v3)))
      (.branch (.fst v5)
        (.branch (.op .scalarEq (.pair (selectedAnswer v4) (selectedAnswer v5))) (.bool false)
          (.branch (.op .point₁Eq (.pair (commitment v0) (commitment v1)))
            (.branch (.op .scalarEq (.pair (challenge v0) (challenge v1))) (.bool false) (.bool true))
            (.bool false)))
        (.bool false))
      (.bool false))
    (.bool false)

def finishFork : Program CryptoOp (Machine.Effect replayStore)
    [loggedOutput, loggedOutput, indexResult, indexResult, scanResult, scanResult] scalar :=
  .branch forkGuards
    (.call (.ret extract) (.cons (response v0) (.cons (response v1)
      (.cons (challenge v0) (.cons (challenge v1) .nil)))))
    fallback

/-- Reset both caches, cursor and event log; retain only the selected chronological
prefix. The source still receives only its public key and original fixed data. -/
def secondStage {dataTy} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery) :
    Program CryptoOp (Machine.Effect replayStore)
      [loggedOutput, indexResult, scanResult, point₁, point₁, .nat, dataTy] scalar :=
  .bind (.query .write (emptyReplay v4 v3 (.fst (.snd (.snd v2))) (.snd (.snd (.snd v2)))))
    (.bind (.call (loggedPassProgram randomBound source) (.cons v4 (.cons v7 .nil)))
      (.bind (.call selectCode (.cons (.fst v0) (.cons (.fst (.snd v0)) (.cons v7 .nil))))
        (.bind (.call (.ret scanCode) (.cons (.snd v4) (.cons (.snd (.snd v1)) .nil)))
          (.call finishFork (.cons v4 (.cons v2 (.cons v5 (.cons v1 (.cons v6 (.cons v0 .nil))))))))))

def firstStage {dataTy} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery) :
    Program CryptoOp (Machine.Effect replayStore)
      [loggedOutput, point₁, point₁, .nat, dataTy] scalar :=
  .bind (.call selectCode (.cons (.fst v0) (.cons (.fst (.snd v0)) (.cons v3 .nil))))
    (.branch (.fst v0)
      (.bind (.call (.ret scanCode) (.cons (.snd v0) (.cons (.snd (.snd v1)) .nil)))
        (.branch (.fst v0)
          (.call (secondStage randomBound source)
            (.cons v2 (.cons v1 (.cons v0 (.cons v3 (.cons v4 (.cons v5 (.cons v6 .nil))))))))
          fallback))
      fallback)

/-- Input registers are public key, fixed generator, public query budget and fixed
adversary data. Fixed registers will be loaded and charged by the enclosing package. -/
def forkCode {dataTy} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery) :
    Machine.Code [point₁, point₁, .nat, dataTy] scalar where
  store := replayStore
  init := emptyReplay v1 v0 (.nat 0) .nil
  body := .bind (.call (loggedPassProgram randomBound source) (.cons v0 (.cons v3 .nil)))
    (.call (firstStage randomBound source) (.cons v0 (.cons v1 (.cons v2 (.cons v3 (.cons v4 .nil))))))

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem loggedPassProgram_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ} (randomBound : Nat) (source : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (s : replayStore.Value (cryptoBase F G₁ G₂ K M)) :
    ((loggedPassProgram randomBound source).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling replayStore) env).run s =
      (fun p =>
        let log := (reverseList (cell := Replay.Mixed.event) (Γ := [])).run (arithmetic F G₁ G₂ K M cost)
          (p.1.value.2.2.2.2.2, ())
        (⟨(p.1.value.1, p.1.value.2.1, log.value), p.1.steps + log.steps + 24⟩, p.2)) <$>
        ((replayPassProgram randomBound source).run (arithmetic F G₁ G₂ K M cost)
          (Machine.effects sampling replayStore) env).run s := by
  unfold loggedPassProgram
  generalize replayPassProgram randomBound source = pass
  generalize reverseList (Op := CryptoOp) (cell := Replay.Mixed.event) (Γ := []) = rev
  dsimp [Program.run, Args.run, Expr.run, v0, v1, Var.get, Var.depth,
    StateT.run, StateT.bind, StateT.pure]
  simp only [map_pure, bind_pure_comp]
  congr 1
  funext p
  apply congrArg (fun r => (r, p.2))
  apply congrArg (Run.mk _)
  omega

theorem loggedPassProgram_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ} (randomBound : Nat) (source : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (localTime : Nat) (queries : Fin 3 → Nat)
    (hsource : SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      source env localTime queries)
    (g pk : G₁) (cursor limit : Nat) (tape : List (Nat × F × Nat))
    (out : Run (loggedOutput.Value (cryptoBase F G₁ G₂ K M)) × replayStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support (((loggedPassProgram randomBound source).run
      (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling replayStore) env).run
        (((g, pk), [], []), cursor, limit, tape, []))) :
    out.1.steps ≤ passPrice cost sampling randomBound tape.length localTime queries +
        7 * ((∑ k, queries k * eventAllowance k) + 1) + 28 ∧
      out.1.value.2.1.1 = (g, pk) ∧
      cacheSize out.1.value.2.1 ≤ (∑ k, queries k) + 1 ∧
      out.1.value.2.2.length ≤ (∑ k, queries k * eventAllowance k) + 1 := by
  rw [loggedPassProgram_run] at hout
  simp only [support_map, Set.mem_image] at hout
  obtain ⟨p, hp, rfl⟩ := hout
  have h := replayPassProgram_bound cost sampling randomBound source env localTime queries hsource
    g pk cursor limit tape p hp
  have hr := reverseList_steps_le (cell := Replay.Mixed.event) (Γ := [])
    (arithmetic F G₁ G₂ K M cost) p.1.value.2.2.2.2.2 ()
  have he : p.1.value.2.2.2.2.2.length ≤ (∑ k, queries k * eventAllowance k) + 1 := by
    rw [h.2.1]
    exact h.2.2.2.2
  refine ⟨by dsimp; omega, ?_, ?_, ?_⟩
  · simpa only [h.2.1] using h.2.2.1
  · simpa only [h.2.1] using h.2.2.2.1
  · simpa only [Expr.run_value, reverseList_denote (cell := Replay.Mixed.event) (Γ := []),
      List.length_reverse] using he

noncomputable def selectionRun (cost : PrimitiveCosts)
    (p : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) (qH : Nat) : Run (Bool × Nat) :=
  let v := verifyObserved.run (arithmetic F G₁ G₂ K M cost)
    (p.1.1, p.1.2, p.2.1.1.1, p.2.1.1.2, ())
  if v.value then
    let i := liveIndex.run (arithmetic F G₁ G₂ K M cost) ((p.1.1.1, p.1.1.2.1), p.2.1.2.2, ())
    let checked := guardIndex.run (arithmetic F G₁ G₂ K M cost) (i.value, qH, ())
    ⟨checked.value, v.steps + i.steps + checked.steps + 57⟩
  else ⟨(false, 0), v.steps + 27⟩

theorem selectionRun_eq (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (p : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) (qH : Nat)
    (s : replayStore.Value (cryptoBase F G₁ G₂ K M)) :
    (selectCode.run (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling replayStore)
      (p.1, p.2.1, qH, ())).run s = pure (selectionRun cost p qH, s) := by
  rw [selectCode_run]
  unfold selectionRun
  dsimp only
  split <;> rfl

omit [SampleableType F] in
theorem selectionRun_bound (cost : PrimitiveCosts)
    (p : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) (qH : Nat) :
    (selectionRun cost p qH).steps ≤ selectionBound cost p.2.1.2.2.length := by
  have hi := liveIndex_steps (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost (p.1.1.1, p.1.1.2.1) p.2.1.2.2
  unfold selectionRun
  rw [verifyObserved_run]
  dsimp only
  split
  · rw [guardIndex_run]
    dsimp only
    split <;> (try split) <;> dsimp [selectionBound] <;> omega
  · dsimp [selectionBound]
    omega

def forkAccepted (first second : loggedOutput.Value (cryptoBase F G₁ G₂ K M))
    (choice₁ choice₂ : Bool × Nat) (scan₁ scan₂ : scanResult.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  choice₂.1 = true ∧ choice₁.2 = choice₂.2 ∧ scan₂.1 = true ∧ scan₁.2.1 ≠ scan₂.2.1 ∧
    first.1.1.2.1 = second.1.1.2.1 ∧ first.1.2 ≠ second.1.2

instance (first second : loggedOutput.Value (cryptoBase F G₁ G₂ K M))
    (choice₁ choice₂ : Bool × Nat) (scan₁ scan₂ : scanResult.Value (cryptoBase F G₁ G₂ K M)) :
    Decidable (forkAccepted first second choice₁ choice₂ scan₁ scan₂) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

set_option maxHeartbeats 2000000 in
omit [SampleableType F] in
theorem forkGuards_denote (cost : PrimitiveCosts)
    (first second : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) (choice₁ choice₂ : Bool × Nat)
    (scan₁ scan₂ : scanResult.Value (cryptoBase F G₁ G₂ K M)) :
    forkGuards.denote (arithmetic F G₁ G₂ K M cost)
        (first, second, choice₁, choice₂, scan₁, scan₂, ()) =
      decide (forkAccepted first second choice₁ choice₂ scan₁ scan₂) := by
  by_cases h₁ : choice₂.1 = true <;> by_cases h₂ : choice₁.2 = choice₂.2 <;>
    by_cases h₃ : scan₂.1 = true <;> by_cases h₄ : scan₁.2.1 = scan₂.2.1 <;>
    by_cases h₅ : first.1.1.2.1 = second.1.1.2.1 <;> by_cases h₆ : first.1.2 = second.1.2 <;>
    simp [forkGuards, Expr.denote, v0, v1, v2, v3, v4, v5, commitment, challenge,
      selectedAnswer, Var.get, arithmetic, forkAccepted, h₁, h₂, h₃, h₄, h₅, h₆]

set_option maxHeartbeats 2000000 in
omit [SampleableType F] in
theorem forkGuards_steps (cost : PrimitiveCosts)
    (first second : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) (choice₁ choice₂ : Bool × Nat)
    (scan₁ scan₂ : scanResult.Value (cryptoBase F G₁ G₂ K M)) :
    (forkGuards.run (arithmetic F G₁ G₂ K M cost)
      (first, second, choice₁, choice₂, scan₁, scan₂, ())).steps ≤
        cost.natOp + 2 * cost.scalarEq + cost.point₁Eq + 69 := by
  by_cases h₁ : choice₂.1 = true <;> by_cases h₂ : choice₁.2 = choice₂.2 <;>
    by_cases h₃ : scan₂.1 = true <;> by_cases h₄ : scan₁.2.1 = scan₂.2.1 <;>
    by_cases h₅ : first.1.1.2.1 = second.1.1.2.1 <;> by_cases h₆ : first.1.2 = second.1.2 <;>
    simp [forkGuards, Expr.run, v0, v1, v2, v3, v4, v5, commitment, challenge,
      selectedAnswer, Var.get, Var.depth, arithmetic, CryptoOp.price, h₁, h₂, h₃, h₄, h₅, h₆] <;> omega

theorem finishFork_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (first second : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) (choice₁ choice₂ : Bool × Nat)
    (scan₁ scan₂ : scanResult.Value (cryptoBase F G₁ G₂ K M))
    (s : replayStore.Value (cryptoBase F G₁ G₂ K M)) :
    (finishFork.run (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling replayStore)
        (first, second, choice₁, choice₂, scan₁, scan₂, ())).run s =
      let checked := forkGuards.run (arithmetic F G₁ G₂ K M cost)
        (first, second, choice₁, choice₂, scan₁, scan₂, ())
      if checked.value then
        let candidate := extract.run (arithmetic F G₁ G₂ K M cost)
          (first.1.1.2.2, second.1.1.2.2, first.1.2, second.1.2, ())
        pure (⟨candidate.value, checked.steps + candidate.steps + 27⟩, s)
      else (fun x => (⟨x, checked.steps + sampling.scalar + 3⟩, s)) <$> ($ᵗ F : ProbComp F) := by
  unfold finishFork
  generalize forkGuards = guards
  generalize extract = extraction
  dsimp [Program.run, Args.run, Expr.run, v0, v1, response, challenge, fallback,
    Var.get, Var.depth, StateT.run, StateT.bind, StateT.pure, Machine.effects]
  by_cases h : (guards.run (arithmetic F G₁ G₂ K M cost)
      (first, second, choice₁, choice₂, scan₁, scan₂, ())).value = true
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

def finishPrice (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts) : Nat :=
  2 * cost.field + cost.division + cost.natOp + 2 * cost.scalarEq + cost.point₁Eq + sampling.scalar + 112

theorem finishFork_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (first second : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) (choice₁ choice₂ : Bool × Nat)
    (scan₁ scan₂ : scanResult.Value (cryptoBase F G₁ G₂ K M))
    (s : replayStore.Value (cryptoBase F G₁ G₂ K M))
    (out : Run F × replayStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support ((finishFork.run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling replayStore) (first, second, choice₁, choice₂, scan₁, scan₂, ())).run s)) :
    out.1.steps ≤ finishPrice cost sampling ∧ out.2 = s := by
  rw [finishFork_run] at hout
  have hg := forkGuards_steps cost first second choice₁ choice₂ scan₁ scan₂
  have he : (extract.run (arithmetic F G₁ G₂ K M cost)
      (first.1.1.2.2, second.1.1.2.2, first.1.2, second.1.2, ())).steps =
        2 * cost.field + cost.division + 16 := by
    simp [extract, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price]
    omega
  dsimp only at hout
  split at hout
  · simp only [support_pure, Set.mem_singleton_iff] at hout
    subst out
    exact ⟨by dsimp [finishPrice]; omega, rfl⟩
  · simp only [support_map, Set.mem_image] at hout
    obtain ⟨x, _, rfl⟩ := hout
    exact ⟨by dsimp [finishPrice]; omega, rfl⟩

theorem secondStage_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (first : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) (choice₁ : Bool × Nat)
    (scan₁ : scanResult.Value (cryptoBase F G₁ G₂ K M)) (pk g : G₁) (qH : Nat)
    (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (s : replayStore.Value (cryptoBase F G₁ G₂ K M)) :
    ((secondStage randomBound source).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling replayStore) (first, choice₁, scan₁, pk, g, qH, data, ())).run s = (do
      let second ← ((loggedPassProgram randomBound source).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling replayStore) (pk, data, ())).run
          (((g, pk), [], []), 0, scan₁.2.2.1, scan₁.2.2.2, [])
      let choice₂ ← (selectCode.run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling replayStore) (second.1.value.1, second.1.value.2.1, qH, ())).run second.2
      let scan₂ := scanCode.run (arithmetic F G₁ G₂ K M cost) (choice₁.2, second.1.value.2.2, ())
      let result ← (finishFork.run (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling replayStore)
        (first, second.1.value, choice₁, choice₂.1.value, scan₁, scan₂.value, ())).run choice₂.2
      pure (⟨result.1.value, second.1.steps + choice₂.1.steps + scan₂.steps + result.1.steps + 124⟩,
        result.2)) := by
  unfold secondStage
  generalize loggedPassProgram randomBound source = pass
  generalize selectCode = choose
  generalize scanCode = scan
  generalize finishFork = finish
  dsimp [Program.run, Args.run, Expr.run, v0, v1, v2, v3, v4, v5, v6, v7,
    emptyReplay, Var.get, Var.depth]
  simp only [StateT.run, Machine.effects, pure_bind,
    bind_pure_comp, bind_map_left, map_bind, map_pure, Functor.map_map]
  congr 1
  funext second
  congr 1
  funext choice₂
  congr 1
  funext result
  apply congrArg (fun r => (r, result.2))
  apply congrArg (Run.mk _)
  omega

set_option backward.isDefEq.respectTransparency false in
theorem firstStage_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (first : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) (pk g : G₁) (qH : Nat)
    (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (s : replayStore.Value (cryptoBase F G₁ G₂ K M)) :
    ((firstStage randomBound source).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling replayStore) (first, pk, g, qH, data, ())).run s = (do
      let choice ← (selectCode.run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling replayStore) (first.1, first.2.1, qH, ())).run s
      if choice.1.value.1 then
        let scan := scanCode.run (arithmetic F G₁ G₂ K M cost) (choice.1.value.2, first.2.2, ())
        if scan.value.1 then
          (fun result => (⟨result.1.value, choice.1.steps + scan.steps + result.1.steps + 73⟩, result.2)) <$>
            ((secondStage randomBound source).run (arithmetic F G₁ G₂ K M cost)
              (Machine.effects sampling replayStore)
              (first, choice.1.value, scan.value, pk, g, qH, data, ())).run choice.2
        else (fun x => (⟨x, choice.1.steps + scan.steps + sampling.scalar + 37⟩, choice.2)) <$>
          ($ᵗ F : ProbComp F)
      else (fun x => (⟨x, choice.1.steps + sampling.scalar + 21⟩, choice.2)) <$>
        ($ᵗ F : ProbComp F)) := by
  unfold firstStage
  generalize selectCode = choose
  generalize scanCode = scanner
  generalize secondStage randomBound source = stage
  simp only [Program.run, Args.run, Expr.run, v0, v1, v2, v3, v4, v5, v6,
    Var.get, Var.depth]
  simp only [StateT.run, state_bind, state_map, pure_bind, bind_pure_comp,
    bind_map_left]
  congr 1
  funext choice
  by_cases hc : choice.1.value.1 = true
  · simp only [hc, ite_true]
    by_cases hs : (scanner.run (arithmetic F G₁ G₂ K M cost)
        (choice.1.value.2, first.2.2, ())).value.1 = true <;>
      simp only [hs, Bool.false_eq_true, ite_true, ite_false, state_map, bind_pure_comp,
        Functor.map_map, fallback, Program.run, Expr.run, Machine.effects]
    all_goals congr 1; funext result; congr 1; apply congrArg (Run.mk _); omega
  · simp only [hc, Bool.false_eq_true, ite_false, fallback, Program.run, Expr.run,
      state_map, Machine.effects, bind_pure_comp, Functor.map_map]
    congr 1
    funext result
    congr 1
    apply congrArg (Run.mk _)
    omega

theorem forkCode_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (pk g : G₁) (qH : Nat) (data : dataTy.Value (cryptoBase F G₁ G₂ K M)) :
    (forkCode randomBound source).run cost sampling (pk, g, qH, data, ()) = (do
      let first ← ((loggedPassProgram randomBound source).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling replayStore) (pk, data, ())).run (((g, pk), [], []), 0, 0, [], [])
      let result ← ((firstStage randomBound source).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling replayStore) (first.1.value, pk, g, qH, data, ())).run first.2
      pure ⟨result.1.value, first.1.steps + result.1.steps + 52⟩) := by
  unfold forkCode Machine.Code.run
  generalize loggedPassProgram randomBound source = pass
  generalize firstStage randomBound source = stage
  dsimp [Program.run, Args.run, Expr.run, emptyReplay, v0, v1, v2, v3, v4,
    Var.get, Var.depth]
  simp only [StateT.run, bind_pure_comp, bind_map_left, map_bind, Functor.map_map]
  congr 1
  funext first
  congr 1
  funext result
  apply congrArg (Run.mk _)
  omega

end Signatures.Runtime.Schnorr
