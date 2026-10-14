import Signatures.Runtime.SchnorrForkBudget
import Signatures.Runtime.ReplayCacheRefinement

/-! Exact probability semantics of the executable two-pass controller. -/

open OracleComp

namespace Signatures.Runtime.Schnorr

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

private theorem state_pure {S A : Type} (a : A) (s : S) :
    (pure a : StateT S ProbComp A) s = pure (a, s) := rfl

private theorem state_bind {S A B : Type} (x : StateT S ProbComp A)
    (f : A → StateT S ProbComp B) (s : S) :
    (x >>= f) s = (x s >>= fun p => f p.1 p.2) := rfl

theorem replayPassProgram_macro (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ} (randomBound : Nat) (source : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (s : replayStore.Value (cryptoBase F G₁ G₂ K M)) :
    (fun p => p.1.value) <$> ((replayPassProgram randomBound source).run
      (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling replayStore) env).run s =
      liftCacheReplay (macroPass cost randomBound source env) s := by
  rw [replayPassProgram_run]
  simp only [macroPass, liftCacheReplay_bind, liftCacheReplay_pure]
  simp_rw [← replayProgram_indexed (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost]
  simp only [StateT.run, state_bind, state_pure, map_bind, map_pure]
  have hs := replayProgram_run_erase cost sampling (source.inline (taggedRoutines randomBound)) env s
  dsimp only [StateT.run] at hs
  rw [← hs]
  simp only [bind_map_left]
  congr 1
  funext first
  have hf := replayProgram_run_erase cost sampling taggedFinalHash
    ((first.1.value.1, first.1.value.2.1), ()) first.2
  dsimp only [StateT.run] at hf
  rw [← hf]
  simp only [bind_map_left]

theorem loggedPassProgram_indexed (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ} (randomBound : Nat) (source : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (cache : cacheStore.Value (cryptoBase F G₁ G₂ K M)) (tape : List (TapeCell F)) :
    (fun p => p.1.value) <$> ((loggedPassProgram randomBound source).run
      (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling replayStore) env).run
        (cache, 0, tape.length, tape, []) =
      (fun p => (p.1.1, p.1.2, p.2)) <$>
        simulateQ sampleReplay (indexedLoggedRun ((macroPass cost randomBound source env).run cache) tape) := by
  rw [loggedPassProgram_run]
  simp only [Functor.map_map, Expr.run_value,
    reverseList_denote (cell := Replay.Mixed.event) (Γ := [])]
  have h := congrArg (fun main : ProbComp (passOutput.Value (cryptoBase F G₁ G₂ K M)) =>
    (fun p => (p.1, p.2.1, p.2.2.2.2.2.reverse)) <$> main)
    (replayPassProgram_macro cost sampling randomBound source env (cache, 0, tape.length, tape, []))
  simpa only [liftCacheReplay, indexedLoggedRun, StateT.run, simulateQ_map, Functor.map_map,
    Function.comp_def] using h

theorem finishFork_value (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (first second : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) (choice₁ choice₂ : Bool × Nat)
    (scan₁ scan₂ : scanResult.Value (cryptoBase F G₁ G₂ K M))
    (s : replayStore.Value (cryptoBase F G₁ G₂ K M)) :
    (fun p => p.1.value) <$> (finishFork.run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling replayStore) (first, second, choice₁, choice₂, scan₁, scan₂, ())).run s =
      if forkAccepted first second choice₁ choice₂ scan₁ scan₂ then
        pure ((first.1.1.2.2 - second.1.1.2.2) / (first.1.2 - second.1.2))
      else ($ᵗ F : ProbComp F) := by
  rw [finishFork_run]
  simp only [Expr.run_value, forkGuards_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    decide_eq_true_eq]
  split <;> simp [extract, Expr.denote, arithmetic, Var.get, Functor.map_map]

omit [SampleableType F] in
theorem selectionRun_value (cost : PrimitiveCosts)
    (p : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) (qH : Nat) :
    (selectionRun cost p qH).value =
      selectValue p.2.1.1.1 p.2.1.1.2 p.1.1 p.1.2 p.2.1.2.2 qH := by
  unfold selectionRun
  rw [verifyObserved_run]
  dsimp only
  split
  · rw [guardIndex_run]
    simp only [Expr.run_value,
      liveIndex_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M), selectValue]
    simp_all
  · simp_all [selectValue]

omit [SampleableType F] in
theorem scanCode_split (cost : PrimitiveCosts) (n : Nat) (xs : List (TapeCell F)) :
    let r := scanCode.run (arithmetic F G₁ G₂ K M cost) (n, xs, ())
    (if r.value.1 then some (r.value.2.2.2, r.value.2.1) else none) = splitCells n xs := by
  have h := scanFold_view (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost n xs
  simpa only [Expr.run_value,
    scanCode_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    scanFold_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M), scanView] using h

noncomputable def loggedPassValue (cost : PrimitiveCosts) {Γ} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (g pk : G₁) (tape : List (TapeCell F)) :
    ProbComp (loggedOutput.Value (cryptoBase F G₁ G₂ K M)) :=
  (fun p => (p.1.1, p.1.2, p.2)) <$>
    simulateQ sampleReplay (indexedLoggedRun ((macroPass cost randomBound source env).run
      ((g, pk), [], [])) tape)

noncomputable def finishValue
    (first second : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) (choice₁ choice₂ : Bool × Nat)
    (scan₁ scan₂ : scanResult.Value (cryptoBase F G₁ G₂ K M)) : ProbComp F :=
  if forkAccepted first second choice₁ choice₂ scan₁ scan₂ then
    pure ((first.1.1.2.2 - second.1.1.2.2) / (first.1.2 - second.1.2))
  else $ᵗ F

noncomputable def secondValue (cost : PrimitiveCosts) (qH : Nat)
    (pass : List (TapeCell F) → ProbComp (loggedOutput.Value (cryptoBase F G₁ G₂ K M)))
    (first : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) (choice₁ : Bool × Nat)
    (scan₁ : scanResult.Value (cryptoBase F G₁ G₂ K M)) : ProbComp F := do
  let second ← pass scan₁.2.2.2
  let choice₂ := (selectionRun cost second qH).value
  let scan₂ := (scanCode.run (arithmetic F G₁ G₂ K M cost) (choice₁.2, second.2.2, ())).value
  finishValue first second choice₁ choice₂ scan₁ scan₂

theorem secondStage_value (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (first : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) (choice₁ : Bool × Nat)
    (scan₁ : scanResult.Value (cryptoBase F G₁ G₂ K M))
    (hsize : scan₁.2.2.1 = scan₁.2.2.2.length) (pk g : G₁) (qH : Nat)
    (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (s : replayStore.Value (cryptoBase F G₁ G₂ K M)) :
    (fun p => p.1.value) <$> ((secondStage randomBound source).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling replayStore) (first, choice₁, scan₁, pk, g, qH, data, ())).run s =
      secondValue cost qH (loggedPassValue cost randomBound source (pk, data, ()) g pk) first choice₁ scan₁ := by
  rw [secondStage_run]
  simp only [map_bind, selectionRun_eq (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
    pure_bind, bind_pure_comp, Functor.map_map]
  simp_rw [finishFork_value (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]
  unfold secondValue loggedPassValue
  rw [← loggedPassProgram_indexed cost sampling randomBound source (pk, data, ())]
  simp only [bind_map_left, hsize, finishValue]

noncomputable def firstValue (cost : PrimitiveCosts) (qH : Nat)
    (pass : List (TapeCell F) → ProbComp (loggedOutput.Value (cryptoBase F G₁ G₂ K M)))
    (first : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) : ProbComp F :=
  let choice := (selectionRun cost first qH).value
  if choice.1 then
    let scan := (scanCode.run (arithmetic F G₁ G₂ K M cost) (choice.2, first.2.2, ())).value
    if scan.1 then secondValue cost qH pass first choice scan else $ᵗ F
  else $ᵗ F

theorem firstStage_value (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (first : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) (pk g : G₁) (qH : Nat)
    (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (s : replayStore.Value (cryptoBase F G₁ G₂ K M)) :
    (fun p => p.1.value) <$> ((firstStage randomBound source).run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling replayStore) (first, pk, g, qH, data, ())).run s =
      firstValue cost qH (loggedPassValue cost randomBound source (pk, data, ()) g pk) first := by
  rw [firstStage_run, selectionRun_eq]
  simp only [pure_bind, firstValue]
  split
  · split
    · simp only [Functor.map_map]
      exact secondStage_value cost sampling randomBound source first (selectionRun cost first qH).value _
        (scanCode_size cost (selectionRun cost first qH).value.2 first.2.2).1 pk g qH data s
    · simp only [Functor.map_map]
      exact id_map _
  · simp only [Functor.map_map]
    exact id_map _

noncomputable def forkValue (cost : PrimitiveCosts) (qH : Nat)
    (pass : List (TapeCell F) → ProbComp (loggedOutput.Value (cryptoBase F G₁ G₂ K M))) : ProbComp F :=
  pass [] >>= firstValue cost qH pass

/-- Erasing execution counts gives exactly the explicit replay-and-extract controller;
no hypothesis equating the completed solver to a probabilistic reduction is used. -/
theorem forkCode_value (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (pk g : G₁) (qH : Nat) (data : dataTy.Value (cryptoBase F G₁ G₂ K M)) :
    Run.value <$> (forkCode randomBound source).run cost sampling (pk, g, qH, data, ()) =
      forkValue cost qH (loggedPassValue cost randomBound source (pk, data, ()) g pk) := by
  rw [forkCode_run]
  simp only [map_bind, bind_pure_comp, Functor.map_map]
  simp_rw [firstStage_value (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]
  unfold forkValue loggedPassValue
  rw [← loggedPassProgram_indexed cost sampling randomBound source (pk, data, ()) ((g, pk), [], []) []]
  simp only [bind_map_left, List.length_nil]

omit [SampleableType F] in
theorem selectionRun_valid (cost : PrimitiveCosts)
    (p : loggedOutput.Value (cryptoBase F G₁ G₂ K M)) (qH : Nat)
    (h : (selectionRun cost p qH).value.1 = true) :
    (selectionRun cost p qH).value.2 < qH + 1 := by
  rw [selectionRun_value] at h ⊢
  unfold selectValue guarded at h ⊢
  split_ifs at *; simp_all

theorem asIndex_eq_some_iff (qH : Nat) (result : Bool × Nat) (i : Fin (qH + 1)) :
    asIndex qH result = some i ↔ result.1 = true ∧ result.2 = i.val := by
  unfold asIndex
  split
  · simp_all only [Option.some.injEq, Fin.ext_iff, true_and]
  · simp only [reduceCtorEq, false_iff, not_and]
    intro hfound heq
    rename_i hn
    exact hn ⟨hfound, heq ▸ i.isLt⟩

end Signatures.Runtime.Schnorr
