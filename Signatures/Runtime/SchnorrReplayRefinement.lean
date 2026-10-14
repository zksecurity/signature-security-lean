import Signatures.Runtime.SchnorrReplayMachine

/-! Exact erasure for the combined cache/replay machine. It retains the entire
updated store, so subsequent adaptive requests see precisely the recorded state. -/

open OracleComp

namespace Signatures.Runtime.Schnorr

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

noncomputable def replaySemantics : SemanticsM (cryptoBase F G₁ G₂ K M) TaggedEffect
    (StateT (replayStore.Value (cryptoBase F G₁ G₂ K M)) ProbComp) := fun cmd arg s =>
  match cmd with
  | .read => pure (s.1, s)
  | .write => pure ((), (arg, s.2))
  | .scalar tag =>
    (fun answer => (answer, (s.1, s.2.1 + 1, s.2.2.1, s.2.2.2.1,
      ((if tag then 1 else 0), answer, 0) :: s.2.2.2.2))) <$>
      (if s.2.1 < s.2.2.1 then pure (((s.2.2.2.1[s.2.1]?).getD (0, 0, 0)).2.1)
       else ($ᵗ F : ProbComp F))
  | .uniform n =>
    (fun answer : Fin (n + 1) => (answer, (s.1, s.2.1 + 1, s.2.2.1, s.2.2.2.1,
      (n + 2, 0, answer.val) :: s.2.2.2.2))) <$>
      (if s.2.1 < s.2.2.1 then
        pure ⟨(((s.2.2.2.1[s.2.1]?).getD (0, 0, 0)).2.2) % (n + 1),
          Nat.mod_lt _ (Nat.zero_lt_succ n)⟩
       else (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))

theorem replayHandler_erase (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {a b} (cmd : TaggedEffect a b) (arg : a.Value (cryptoBase F G₁ G₂ K M)) :
    Run.value <$> replayHandler cost sampling cmd arg = replaySemantics cmd arg := by
  funext s
  rcases s with ⟨cache, cursor, limit, tape, events⟩
  cases cmd with
  | read =>
    cases arg
    change (Run.value <$> replayHandler cost sampling .read ()).run _ = _
    rw [StateT.run_map, replayHandler_read]
    rfl
  | write =>
    change (Run.value <$> replayHandler cost sampling .write arg).run _ = _
    rw [StateT.run_map, replayHandler_write]
    rfl
  | scalar tag =>
    cases arg
    change (Run.value <$> replayHandler cost sampling (.scalar tag) ()).run _ = _
    simp only [replayHandler, routineHandler, bind_pure_comp, StateT.run_map, Functor.map_map]
    rw [replayRoutines, Machine.secondStore_run]
    have h := Replay.Mixed.draw_erase (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
      cost (Machine.forwardedSampling sampling) 10 14 .scalar Replay.Mixed.scalarDecode
      (Replay.Mixed.scalarEncode tag) ($ᵗ F) (sampling.scalar + 5) (fun _ => rfl)
      cursor limit tape events
    have hh := congrArg (Functor.map (fun p : F × Replay.Mixed.store.Value (cryptoBase F G₁ G₂ K M) =>
      (p.1, (cache, p.2)))) h
    simpa only [Functor.map_map, Replay.Mixed.scalarDraw,
      Replay.Mixed.scalarDecode_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
      Replay.Mixed.scalarEncode_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
      replaySemantics] using hh
  | uniform n =>
    cases arg
    change (Run.value <$> replayHandler cost sampling (.uniform n) ()).run _ = _
    simp only [replayHandler, routineHandler, bind_pure_comp, StateT.run_map, Functor.map_map]
    rw [replayRoutines, Machine.secondStore_run]
    have h := Replay.Mixed.draw_erase (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
      cost (Machine.forwardedSampling sampling) 10 14 (.uniform n) (Replay.Mixed.uniformDecode n)
      (Replay.Mixed.uniformEncode n) (liftM (unifSpec.query n)) (sampling.uniform n + 5)
      (fun _ => rfl) cursor limit tape events
    have hh := congrArg (Functor.map
      (fun p : Fin (n + 1) × Replay.Mixed.store.Value (cryptoBase F G₁ G₂ K M) =>
        (p.1, (cache, p.2)))) h
    simpa only [Functor.map_map, Replay.Mixed.uniformDraw,
      Replay.Mixed.uniformDecode_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
      Replay.Mixed.uniformEncode_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M),
      replaySemantics] using hh

/-- This equality includes cache state and the new transcript, not just the final output. -/
theorem replayProgram_erase (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ a} (code : Program CryptoOp TaggedEffect Γ a) (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    Run.value <$> (code.inline replayRoutines).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling replayStore) env =
      code.denote (arithmetic F G₁ G₂ K M cost) replaySemantics env := by
  rw [Program.inline_run]
  change Run.value <$> code.run (arithmetic F G₁ G₂ K M cost)
    (replayHandler cost sampling) env = _
  rw [Program.run_erase]
  simp_rw [replayHandler_erase]

theorem replayProgram_run_erase (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ a} (code : Program CryptoOp TaggedEffect Γ a) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (s : replayStore.Value (cryptoBase F G₁ G₂ K M)) :
    (fun p => (p.1.value, p.2)) <$>
        ((code.inline replayRoutines).run (arithmetic F G₁ G₂ K M cost)
          (Machine.effects sampling replayStore) env).run s =
      (code.denote (arithmetic F G₁ G₂ K M cost) replaySemantics env).run s := by
  rw [← StateT.run_map, replayProgram_erase]

end Signatures.Runtime.Schnorr
