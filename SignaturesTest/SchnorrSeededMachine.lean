import Signatures.Schnorr.SeededBitStatement
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.Schnorr

namespace SignaturesTest.SchnorrSeededMachine

private abbrev F := ZMod 5
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def primitives := arithmetic F F F Unit Nat PrimitiveCosts.unit
private def sampling : Machine.SamplingCosts := ⟨11, fun _ => 7⟩
private def first : cachePassOutput.Value (cryptoBase F F F Unit Nat) :=
  (((0, 0, 1), 1), ((1, 1), [], [((0, 0), 1)]))
private def second : cachePassOutput.Value (cryptoBase F F F Unit Nat) :=
  (((0, 0, 2), 2), ((1, 1), [], [((0, 0), 2)]))

private theorem select_first : selectPass PrimitiveCosts.unit 0 first = some 0 := by
  rw [selectPass, selectionRun_value]
  decide

private theorem select_second : selectPass PrimitiveCosts.unit 0 second = some 0 := by
  rw [selectPass, selectionRun_value]
  decide

private theorem extract_pair : extractFork (some (first, second)) = pure (1 : F) := by
  have h : (1 : F) ≠ 2 := by decide
  norm_num [extractFork, extractValues, first, second, h]

/-- The absent seed entry must reach the second pass. Returning a fresh fallback
here would change this computation and invalidate exact fork semantics. -/
example : SeedTape.firstValue PrimitiveCosts.unit 0 (fun _ => pure second)
    (SeedTape.toSeed []) first = (do
      let _ ← ($ᵗ F : ProbComp F)
      pure (1 : F)) := by
  simp [SeedTape.firstValue, select_first, SeedTape.toSeed, SeedTape.values,
    SeedTape.secondValue, select_second]
  have h : (1 : F) ≠ 2 := by decide
  norm_num [extractFork, extractValues, first, second, h]

/-- An existing equal answer rejects the fork before its second pass. -/
example : SeedTape.firstValue PrimitiveCosts.unit 0 (fun _ => pure second)
    (SeedTape.toSeed [(1, (3 : F), 0)]) first = (do
      let fresh ← ($ᵗ F : ProbComp F)
      if (3 : F) = fresh then $ᵗ F else pure 1) := by
  simp [SeedTape.firstValue, select_first, SeedTape.toSeed, SeedTape.values, SeedTape.familyTag,
    decodeReply, SeedTape.secondValue, select_second]
  have h : (1 : F) ≠ 2 := by decide
  norm_num [extractFork, extractValues, first, second, h]

/-- The compiled extractor must reject a different ordinal even if its two
transcripts yield the same algebraic solution. -/
example : (SeedTape.finishGuards.run primitives (first, second, (true, 1), 0, ())).value = false := by
  rw [Expr.run_value]
  unfold primitives
  rw [SeedTape.finishGuards_denote]
  decide

example : (SeedTape.finishGuards.run primitives (first, second, (true, 0), 0, ())).value = true := by
  rw [Expr.run_value]
  unfold primitives
  rw [SeedTape.finishGuards_denote]
  decide

private def returnForgery : Program CryptoOp (Command 0) [point₁, forgery] forgery :=
  .ret (.var (.there .here))

attribute [local irreducible] Machine.Code.run Machine.Package.run

/-- The full package, including setup, follows from a three-step source budget
with zero source queries; no premise bounds the finished fork machine. -/
example {E N : Type} [Field E] [SampleableType E] [DecidableEq E] [DecidableEq N]
    (g pk R : E) (msg : N) (z : E) (out : Run E)
    (hout : out ∈ support ((SeedTape.forkPackage 0 0 returnForgery 3 (fun _ => 0) g (msg, R, z)).run
      (F := E) (G₁ := E) (G₂ := E) (K := Unit) (M := N)
      PrimitiveCosts.unit sampling (pk, ()))) :
    out.steps ≤ SeedTape.packagePrice (F := E) (G₂ := E) (K := Unit)
      PrimitiveCosts.unit sampling 0 0 returnForgery 3 (fun _ => 0) g (msg, R, z) := by
  have hb : SourceBudget (arithmetic E E E Unit N PrimitiveCosts.unit) (replies 0) kind
      returnForgery (pk, (msg, R, z), ()) 3 (fun _ => 0) := by
    intro price result hr
    simp only [returnForgery, Program.run, Expr.run, Var.get, Var.depth, support_pure,
      Set.mem_singleton_iff] at hr
    have hsteps := congrArg Run.steps hr
    change result.steps = 3 at hsteps
    simpa only [Nat.zero_mul, Finset.sum_const_zero, Nat.add_zero] using hsteps.le
  exact SeedTape.forkPackage_bound PrimitiveCosts.unit sampling 0 0 returnForgery pk g (msg, R, z)
    3 (fun _ => 0) hb out hout

end SignaturesTest.SchnorrSeededMachine

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``SeedTape.capturePass_run, ``SeedTape.runWithTape_run, ``SeedTape.capturePass_seeded,
      ``SeedTape.runWithTape_seeded, ``SeedTape.splitCells_answer, ``SeedTape.scanCode_collision,
      ``SeedTape.finishFork_run, ``SeedTape.secondStage_run, ``SeedTape.firstStage_run,
      ``SeedTape.forkCode_run, ``SeedTape.forkCode_bound, ``SeedTape.forkPackage_bound,
      ``SeedTape.firstStage_value, ``SeedTape.forkCode_value, ``SeedTape.forkValue_seeded,
      ``SeedTape.sourceForkCode_seeded, ``SeedTape.sourceForkCode_reduction,
      ``SeedTape.source_within, ``SeedTape.security,
      ``SourceCertificate.seededBitCode_costed, ``SourceCertificate.seededBitCode_error,
      ``Schnorr.Statement.schnorr_eufcma_of_dlog_seeded_bit_hardness] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
