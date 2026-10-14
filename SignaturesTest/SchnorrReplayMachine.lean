import Signatures.Runtime.ReplayCacheRefinement
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp Signatures.Runtime Signatures.Runtime.Schnorr

namespace SignaturesTest.SchnorrReplayMachine

private abbrev F := ZMod 5
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def primitives := arithmetic F F F Unit Unit PrimitiveCosts.unit
private def sampling : Machine.SamplingCosts := ⟨11, fun _ => 7⟩
private def cache : cacheStore.Value (cryptoBase F F F Unit Unit) := ((1, 2), [], [])
private def tape : Replay.Mixed.store.Value (cryptoBase F F F Unit Unit) := (0, 1, [(1, 0, 0)], [])

private def returnForgery : Program CryptoOp (Command 0) [forgery] forgery := .ret (.var .here)

-- Reading or replacing caches does not reset the replay cursor or discard the log.
example : (replayHandler PrimitiveCosts.unit sampling .read ()).run (cache, tape) =
    pure (⟨cache, 10⟩, (cache, tape)) :=
  replayHandler_read (F := F) (G₁ := F) (G₂ := F) (K := Unit) (M := Unit) _ _ _ _

example : (replayHandler PrimitiveCosts.unit sampling .write (((3 : F), 4), [], [])).run (cache, tape) =
    pure (⟨(), 14⟩, ((((3 : F), 4), [], []), tape)) :=
  replayHandler_write (F := F) (G₁ := F) (G₂ := F) (K := Unit) (M := Unit) _ _ _ _ _

-- A scalar replay preserves the cache field and records the forced zero answer.
example : (Run.value <$> replayHandler PrimitiveCosts.unit sampling (.scalar true) ()).run (cache, tape) =
    pure ((0 : F), (cache, 1, 1, [(1, (0 : F), 0)], [(1, (0 : F), 0)])) := by
  rw [replayHandler_erase]
  rfl

-- The callable pass charges the final query even when the adversary makes no calls.
attribute [local irreducible] Program.run

example {E N : Type} [Field E] [SampleableType E] [DecidableEq E] [DecidableEq N]
    (g pk R : E) (msg : N) (z : E) (limit : Nat) (recorded : List (Nat × E × Nat))
    (out : Run (passOutput.Value (cryptoBase E E E Unit N)) × replayStore.Value (cryptoBase E E E Unit N))
    (hout : out ∈ support (((replayPassProgram 0 returnForgery).run
      (arithmetic E E E Unit N PrimitiveCosts.unit) (Machine.effects sampling replayStore)
      ((msg, R, z), ())).run (((g, pk), [], []), 0, limit, recorded, []))) :
    out.1.steps ≤ passPrice PrimitiveCosts.unit sampling 0 recorded.length 2 (fun _ => 0) ∧
      replayEvents (F := E) (G₁ := E) (G₂ := E) (K := Unit) (M := N) out.2 ≤ 1 := by
  have hb : SourceBudget (arithmetic E E E Unit N PrimitiveCosts.unit) (replies 0) kind
      returnForgery ((msg, R, z), ()) 2 (fun _ => 0) := by
    intro price result hr
    simp only [returnForgery, Program.run, Expr.run, Var.get, Var.depth, support_pure,
      Set.mem_singleton_iff] at hr
    have hsteps := congrArg Run.steps hr
    change result.steps = 2 at hsteps
    simpa only [Nat.zero_mul, Finset.sum_const_zero, Nat.add_zero] using hsteps.le
  have h := replayPassProgram_bound PrimitiveCosts.unit sampling 0 returnForgery
    ((msg, R, z), ()) 2 (fun _ => 0) hb g pk 0 limit recorded out hout
  exact ⟨h.1, by simpa only [Nat.zero_mul, Finset.sum_const_zero, Nat.zero_add] using h.2.2.2.2⟩

-- The actual compiled hash call consumes the prefix and populates both caches.
example : (Run.value <$> (taggedHash.inline replayRoutines).run primitives
    (Machine.effects sampling replayStore) (((), (3 : F)), ())).run (cache, tape) =
      pure ((0 : F), ((((1 : F), (2 : F)), [(((), (3 : F)), (0 : F))],
        [(((), (3 : F)), (0 : F))]), 1, 1, [(1, (0 : F), 0)], [(1, (0 : F), 0)])) := by
  unfold primitives
  rw [replayProgram_erase]
  unfold taggedHash
  rw [hashProgram_denote]
  dsimp [cache, tape, StateT.run, StateT.bind, StateT.pure, replaySemantics]
  simp only [pure_bind]
  rw [managedGet_denote]
  simp only [lookupValue, Bool.false_eq_true]
  rw [cacheGetExpr_denote _ _ _ _ (hashEq_value (F := F) (G₂ := F) (K := Unit) PrimitiveCosts.unit)]
  rfl

end SignaturesTest.SchnorrReplayMachine

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``Machine.firstStore_refines, ``Machine.secondStore_refines,
      ``Machine.firstStore_run, ``Machine.secondStore_run,
      ``replayHandler_scalar_bound, ``replayHandler_uniform_bound, ``replayHandler_erase,
      ``replayProgram_erase, ``replayedHash_bound, ``replayedSign_bound,
      ``replayedFinalHash_bound, ``replaySourceHandler_bound, ``replaySimulation_bound,
      ``replayPassProgram_run, ``replayPassProgram_bound,
      ``liftCacheReplay_tagged, ``replayProgram_indexed] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
