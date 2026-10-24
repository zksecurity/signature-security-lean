import Proofs.Runtime.SchnorrSeededMachine

/-! Exact query-tree semantics for the compiled fully seeded controller. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.SeedTape

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

noncomputable def passValue (cost : PrimitiveCosts) {dataTy} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (pk g : G₁) (data : dataTy.Value (cryptoBase F G₁ G₂ K M)) (seed : QuerySeed (replaySpec F)) :
    ProbComp (cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) :=
  simulateQ samples ((simulateQ seededOracle
    ((macroPass cost randomBound source (pk, data, ())).run ((g, pk), [], []))).run' seed)

theorem finishFork_value (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (first second : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) (choice : Bool × Nat)
    (qH : Nat) (index : Fin (qH + 1)) (s : machineStore.Value (cryptoBase F G₁ G₂ K M)) :
    (fun p => p.1.value) <$> (finishFork.run (arithmetic F G₁ G₂ K M cost)
      (Machine.effects sampling machineStore) (first, second, choice, index.val, ())).run s =
      if asIndex qH choice = some index then extractFork (some (first, second)) else ($ᵗ F : ProbComp F) := by
  rw [finishFork_run]
  simp only [Expr.run_value,
    finishGuards_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M), decide_eq_true_eq]
  simp only [accepted, extractFork, extractValues, asIndex_eq_some_iff]
  by_cases h₁ : choice.1 = true ∧ choice.2 = index.val <;>
    by_cases h₂ : first.1.1.2.1 = second.1.1.2.1 ∧ first.1.2 ≠ second.1.2 <;>
    simp [h₁, h₂, extract, Expr.denote, arithmetic, Var.get, Functor.map_map]

noncomputable def secondValue (cost : PrimitiveCosts) (qH : Nat)
    (pass : QuerySeed (replaySpec F) → ProbComp (cachePassOutput.Value (cryptoBase F G₁ G₂ K M)))
    (seed : QuerySeed (replaySpec F)) (first : cachePassOutput.Value (cryptoBase F G₁ G₂ K M))
    (index : Fin (qH + 1)) (fresh : F) : ProbComp F := do
  let second ← pass ((seed.takeAtIndex (.inr ()) index.val).addValue (.inr ()) fresh)
  if selectPass cost qH second = some index then extractFork (some (first, second)) else $ᵗ F

theorem secondStage_value (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (qH randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (tape : List (TapeCell F)) (first : cachePassOutput.Value (cryptoBase F G₁ G₂ K M))
    (index : Fin (qH + 1)) (fresh : F) (pk g : G₁) (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (s : machineStore.Value (cryptoBase F G₁ G₂ K M)) :
    (fun p => p.1.value) <$> ((secondStage qH randomBound source).run
      (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling machineStore)
      (tape, first, index.val, fresh, pk, g, data, ())).run s =
      secondValue cost qH (passValue cost randomBound source pk g data) (toSeed tape) first index fresh := by
  rw [secondStage_run]
  simp only [map_bind, bind_pure_comp, Functor.map_map]
  simp_rw [finishFork_value (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost sampling _ _ _ qH index]
  have hp := runWithTape_seeded cost sampling randomBound source
    (resetCode.run (arithmetic F G₁ G₂ K M cost) (1, index.val, tape, (1, fresh, 0), ())).value pk g data s
  rw [Expr.run_value, resetCode_denote] at hp
  have hr : toSeed (reset 1 index.val (1, fresh, 0) tape) =
      ((toSeed tape).takeAtIndex (.inr ()) index.val).addValue (.inr ()) fresh :=
    toSeed_reset (.inr ()) index.val fresh tape
  rw [hr] at hp
  unfold secondValue passValue
  rw [← hp]
  simp only [bind_map_left, selectPass, Expr.run_value,
    resetCode_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]
  rfl

noncomputable def firstValue (cost : PrimitiveCosts) (qH : Nat)
    (pass : QuerySeed (replaySpec F) → ProbComp (cachePassOutput.Value (cryptoBase F G₁ G₂ K M)))
    (seed : QuerySeed (replaySpec F)) (first : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) : ProbComp F :=
  match selectPass cost qH first with
  | none => $ᵗ F
  | some index => do
    let fresh ← ($ᵗ F : ProbComp F)
    if (seed (.inr ()))[index.val]? = some fresh then $ᵗ F
    else secondValue cost qH pass seed first index fresh

theorem firstStage_value (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (qH randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (tape : List (TapeCell F)) (first : cachePassOutput.Value (cryptoBase F G₁ G₂ K M))
    (pk g : G₁) (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (s : machineStore.Value (cryptoBase F G₁ G₂ K M)) :
    (fun p => p.1.value) <$> ((firstStage qH randomBound source).run
      (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling machineStore)
      (tape, first, pk, g, data, ())).run s =
      firstValue cost qH (passValue cost randomBound source pk g data) (toSeed tape) first := by
  rw [firstStage_run]
  by_cases hc : (selectionRun cost (first.1, first.2, []) qH).value.1 = true
  · let index : Fin (qH + 1) := ⟨(selectionRun cost (first.1, first.2, []) qH).value.2,
      selectionRun_valid cost (first.1, first.2, []) qH hc⟩
    have hi : selectPass cost qH first = some index :=
      (asIndex_eq_some_iff qH _ index).mpr ⟨hc, rfl⟩
    simp only [firstValue, hi, hc, ite_true, map_bind]
    congr 1
    funext fresh
    have hcollision := scanCode_collision (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
      cost index.val tape fresh
    dsimp only [index] at hcollision
    by_cases h : (toSeed tape (.inr ()))[index.val]? = some fresh
    · have hc := hcollision.mpr h
      simp only [hc, h, and_self, ite_true, Functor.map_map]
      exact id_map _
    · have hc := mt hcollision.mp h
      simp only [hc, h, ite_false, Functor.map_map]
      exact secondStage_value cost sampling qH randomBound source tape first index fresh pk g data s
  · simp [firstValue, selectPass, asIndex, hc, Functor.map_map]

noncomputable def forkValue (cost : PrimitiveCosts) (capacity : Family → Nat) (families : List Family)
    (qH : Nat) (pass : QuerySeed (replaySpec F) →
      ProbComp (cachePassOutput.Value (cryptoBase F G₁ G₂ K M))) : ProbComp F := do
  let seed ← generateSeed (replaySpec F) capacity families
  let first ← pass seed
  firstValue cost qH pass seed first

theorem forkCode_value (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (capacity : Family → Nat) (families : List Family) (qH randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (pk g : G₁) (data : dataTy.Value (cryptoBase F G₁ G₂ K M)) :
    Run.value <$> (forkCode capacity families qH randomBound source).run cost sampling (pk, g, data, ()) =
      forkValue cost capacity families qH (passValue cost randomBound source pk g data) := by
  rw [forkCode_run]
  simp only [map_bind, bind_pure_comp, Functor.map_map]
  simp_rw [firstStage_value (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]
  let pass := passValue cost randomBound source pk g data
  have hp (tape : List (TapeCell F)) (s : machineStore.Value (cryptoBase F G₁ G₂ K M)) :=
    runWithTape_seeded cost sampling randomBound source tape pk g data s
  change _ = (generateSeed (replaySpec F) capacity families >>= fun seed =>
    pass seed >>= firstValue cost qH pass seed)
  have hg := congrArg (fun action : ProbComp
      (QuerySeed (replaySpec F) × machineStore.Value (cryptoBase F G₁ G₂ K M)) =>
    action >>= fun seed => pass seed.1 >>= firstValue cost qH pass seed.1)
    (generateCode_seed cost sampling machineStore capacity families (((g, pk), [], []), []))
  simp only [bind_map_left] at hg
  rw [← hg]
  congr 1
  funext seed
  dsimp only [pass, passValue]
  rw [← hp seed.1.value seed.2]
  simp only [bind_map_left]

omit [Field F] [DecidableEq F] in
theorem samples_liftComp {A : Type} (main : ProbComp A) :
    simulateQ (samples (F := F)) (liftComp main (replaySpec F)) = main := by
  induction main using OracleComp.inductionOn with
  | pure x => simp
  | query_bind n next ih =>
      rw [liftComp_bind, simulateQ_bind]
      have hq : simulateQ (samples (F := F))
          (liftComp (liftM (unifSpec.query n) : ProbComp _) (replaySpec F)) =
          (liftM (unifSpec.query n) : ProbComp _) := by rfl
      rw [hq]
      exact congrArg (fun f : Fin (n + 1) → ProbComp A =>
        (liftM (unifSpec.query n) : ProbComp _) >>= f) (funext ih)

/-- The cache-level controller is the reference seeded fork followed by the
guarded extractor, as an equality of computations, including failed forks. -/
theorem forkValue_seeded (cost : PrimitiveCosts) (capacity : Family → Nat) (families : List Family)
    (qH : Nat) (hQ : qH ≤ capacity (.inr ()))
    (main : OracleComp (replaySpec F) (cachePassOutput.Value (cryptoBase F G₁ G₂ K M))) :
    forkValue cost capacity families qH (fun seed =>
      simulateQ samples ((simulateQ seededOracle main).run' seed)) =
      (simulateQ samples (seededFork main capacity families (.inr ())
        (Option.map (Fin.castLE (Nat.succ_le_succ hQ)) ∘ selectPass cost qH)) >>= extractFork) := by
  unfold forkValue seededFork
  simp only [simulateQ_bind, samples_liftComp, bind_assoc]
  congr 1
  funext seed
  congr 1
  funext first
  unfold firstValue
  simp only [Function.comp_def]
  cases hi : selectPass cost qH first with
  | none => simp [simulateQ_pure, extractFork]
  | some index =>
      simp only [Option.map_some, simulateQ_bind, samples_liftComp, bind_assoc]
      congr 1
      funext fresh
      by_cases hc : (seed (.inr ()))[index.val]? = some fresh
      · simp [hc, simulateQ_pure, extractFork]
      · simp only [Fin.getElem?_fin, Fin.val_castLE, hc, ite_false, secondValue, simulateQ_bind, bind_assoc]
        congr 1
        funext second
        have he : Option.map (Fin.castLE (Nat.succ_le_succ hQ)) (selectPass cost qH second) =
            some (index.castLE (Nat.succ_le_succ hQ)) ↔ selectPass cost qH second = some index := by
          cases selectPass cost qH second <;> simp [Fin.ext_iff]
        simp only [he]
        split <;> simp [simulateQ_pure, extractFork]

theorem sourceForkCode_seeded (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (qH randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (localTime : Nat) (queries : Fin 3 → Nat)
    (pk g : G₁) (data : dataTy.Value (cryptoBase F G₁ G₂ K M)) :
    Run.value <$> (sourceForkCode qH randomBound source localTime queries).run
      cost sampling (pk, g, data, ()) =
      (simulateQ samples (seededFork
        ((macroPass cost randomBound source (pk, data, ())).run ((g, pk), [], []))
        (Seeded.budget source localTime queries qH) (sourceFamilies source) (.inr ())
        (Option.map (Fin.castLE (Nat.succ_le_succ (Seeded.target_le source localTime queries qH))) ∘
          selectPass cost qH)) >>= extractFork) := by
  rw [sourceForkCode, forkCode_value]
  exact forkValue_seeded cost _ _ qH (Seeded.target_le source localTime queries qH) _

end Signatures.Runtime.Schnorr.SeedTape
