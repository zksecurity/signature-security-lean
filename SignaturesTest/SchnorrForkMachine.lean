import Proofs.Runtime.SchnorrForkCorrectness
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp Signatures.Runtime Signatures.Runtime.Schnorr

namespace SignaturesTest.SchnorrForkMachine

private abbrev F := ZMod 5
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def primitives := arithmetic F F F Unit Nat PrimitiveCosts.unit
private def sampling : Machine.SamplingCosts := ⟨11, fun _ => 7⟩
private def first : loggedOutput.Value (cryptoBase F F F Unit Nat) :=
  (((0, 0, 1), 1), ((1, 1), [], []), [])
private def second : loggedOutput.Value (cryptoBase F F F Unit Nat) :=
  (((0, 0, 2), 2), ((1, 1), [], []), [])

-- Same commitment, changed challenge, same selected index and changed focused answer.
example : (forkGuards.run primitives
    (first, second, (true, 0), (true, 0), (true, 1, 0, []), (true, 2, 0, []), ())).value = true := by
  rw [Expr.run_value]
  unfold primitives
  rw [forkGuards_denote]
  decide

-- A different selected ordinal is rejected even if both signatures verify.
example : (forkGuards.run primitives
    (first, second, (true, 0), (true, 1), (true, 1, 0, []), (true, 2, 0, []), ())).value = false := by
  rw [Expr.run_value]
  unfold primitives
  rw [forkGuards_denote]
  decide

-- Distinct challenges do not permit extracting from different commitments.
example : (forkGuards.run primitives
    (first, (((0, 1, 2), 2), ((1, 1), [], []), []),
      (true, 0), (true, 0), (true, 1, 0, []), (true, 2, 0, []), ())).value = false := by
  rw [Expr.run_value]
  unfold primitives
  rw [forkGuards_denote]
  decide

-- A rejected second selection cannot pass by returning the first run's index.
example : (forkGuards.run primitives
    (first, second, (true, 0), (false, 0), (true, 1, 0, []), (true, 2, 0, []), ())).value = false := by
  rw [Expr.run_value]
  unfold primitives
  rw [forkGuards_denote]
  decide

-- Replaying the same focused answer does not constitute a fork.
example : (forkGuards.run primitives
    (first, second, (true, 0), (true, 0), (true, 1, 0, []), (true, 1, 0, []), ())).value = false := by
  rw [Expr.run_value]
  unfold primitives
  rw [forkGuards_denote]
  decide

-- A missing second live query is not silently decoded as an answer of zero.
example : (forkGuards.run primitives
    (first, second, (true, 0), (true, 0), (true, 1, 0, []), (false, 2, 0, []), ())).value = false := by
  rw [Expr.run_value]
  unfold primitives
  rw [forkGuards_denote]
  decide

-- Distinct focused answers do not bypass the extractor's own challenge check.
example : (forkGuards.run primitives
    (first, first, (true, 0), (true, 0), (true, 1, 0, []), (true, 2, 0, []), ())).value = false := by
  rw [Expr.run_value]
  unfold primitives
  rw [forkGuards_denote]
  decide

example : finishValue first second (true, 0) (true, 0)
    (true, 1, 0, []) (true, 2, 0, []) = pure (1 : F) := by
  have h : (1 : F) ≠ 2 := by decide
  norm_num [finishValue, forkAccepted, first, second, h]

private def returnForgery : Program CryptoOp (Command 0) [point₁, forgery] forgery :=
  .ret (.var (.there .here))

attribute [local irreducible] Machine.Code.run Machine.Package.run

-- A full two-pass package is certified from a three-step, zero-query source alone.
example {E N : Type} [Field E] [SampleableType E] [DecidableEq E] [DecidableEq N]
    (g pk R : E) (msg : N) (z : E) (out : Run E)
    (hout : out ∈ support ((forkPackage 0 returnForgery g 0 (msg, R, z)).run
      (F := E) (G₁ := E) (G₂ := E) (K := Unit) (M := N)
      PrimitiveCosts.unit sampling (pk, ()))) :
    out.steps ≤ forkPrice PrimitiveCosts.unit sampling 0 3 (fun _ => 0) +
      (Env.load (base := cryptoBase E E E Unit N) (Γ := [point₁, .nat, forgery])
        (g, 0, (msg, R, z), ())).steps + 3 := by
  have hb : SourceBudget (arithmetic E E E Unit N PrimitiveCosts.unit) (replies 0) kind
      returnForgery (pk, (msg, R, z), ()) 3 (fun _ => 0) := by
    intro price result hr
    simp only [returnForgery, Program.run, Expr.run, Var.get, Var.depth, support_pure,
      Set.mem_singleton_iff] at hr
    have hsteps := congrArg Run.steps hr
    change result.steps = 3 at hsteps
    simpa only [Nat.zero_mul, Finset.sum_const_zero, Nat.add_zero] using hsteps.le
  exact forkPackage_bound PrimitiveCosts.unit sampling 0 returnForgery pk g 0 (msg, R, z)
    3 (fun _ => 0) hb out hout

end SignaturesTest.SchnorrForkMachine

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``loggedPassProgram_run, ``loggedPassProgram_bound, ``selectionRun_bound,
      ``forkGuards_denote, ``forkGuards_steps, ``finishFork_run, ``finishFork_bound,
      ``secondStage_run, ``firstStage_run, ``forkCode_run, ``passPrice_mono,
      ``scanCode_size, ``secondStage_bound, ``firstStage_bound, ``forkCode_bound,
      ``forkPackage_bound, ``replayPassProgram_macro, ``loggedPassProgram_indexed,
      ``finishFork_value, ``selectionRun_value, ``scanCode_split,
      ``secondStage_value, ``firstStage_value, ``forkCode_value, ``selectionRun_valid,
      ``asIndex_eq_some_iff, ``finishValue_checked, ``firstValue_checked,
      ``forkValue_indexed, ``forkCode_indexed,
      ``sampleExpanded_liftRandom, ``sampleExpanded_expand, ``forkCode_context] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
