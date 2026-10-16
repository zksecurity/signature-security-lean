import Signatures.BLS.Statement
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open Signatures.Runtime Signatures.Runtime.Coron OracleComp OracleSpec

namespace SignaturesTest.RuntimeCertificate

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5
private def cost := PrimitiveCosts.unit
private def sampling : Machine.SamplingCosts := ⟨1, fun _ => 1⟩

private def constantAdv : BLS.ROM.AdversaryPK Bool F F :=
  fun _ => (pure (false, 0) : OracleComp (BLS.ROM.advSpec Bool F) (Bool × F))

private def constantCode : Program CryptoOp (Command 1)
    (challengeInputs ++ [message]) (.pair message point₁) :=
  .ret (.pair (.var (.there (.there (.there (.there (.there .here)))))) (.op .zero₁ .unit))

-- Fixed message data is loaded explicitly; no message or key-dependent host initializer.
private def cert : SourceCertificate (F := F) cost 1 11 (fun _ => 0) constantAdv where
  dataTypes := [message]
  data := (false, ())
  code := constantCode
  semantics _ _ _ _ _ := rfl
  budget g g₂ X X₂ h := by
    intro price z hz
    simp only [constantCode, Program.run, support_pure, Set.mem_singleton_iff] at hz
    subst z
    simp [Expr.run, Var.depth, cost, arithmetic, CryptoOp.price, PrimitiveCosts.unit]

example : cert.targetBudget sampling 0 = 309 := by
  simp [SourceCertificate.targetBudget, cert, machineReductionBound, finishBound, replyBase,
    machineSampling, sampling, cost, PrimitiveCosts.unit, Env.load, Ty.load]

-- This certifies the exact named solver, including final hashing and extraction.
example : coCDHWithin (M := Bool) cost sampling 309
    (BLS.CoCDH.coronReductionLazyPK (F := F) 0 (BLS.ROM.cacheForgeryPK constantAdv)) := by
  have hb := cert.within sampling 0
  simpa [SourceCertificate.targetBudget, cert, machineReductionBound, finishBound, replyBase,
    machineSampling, sampling, cost, PrimitiveCosts.unit, Env.load, Ty.load] using hb

example (g g₂ X X₂ h : F) :
    Run.value <$> (cert.package 0).run cost sampling (g, g₂, X, X₂, h, ()) =
      BLS.CoCDH.coronReductionLazyPK (F := F) 0 (BLS.ROM.cacheForgeryPK constantAdv)
        g g₂ X X₂ h := by
  rw [Machine.Package.run_eq]
  simp only [Functor.map_map]
  change Run.value <$> (machineReductionCode 0 1 challengeSetup constantCode).run
      cost sampling (g, g₂, X, X₂, h, false, ()) = _
  rw [machineReductionCode_erase cost sampling g X h 0 1 challengeSetup constantCode
    (g, g₂, X, X₂, h, false, ()) 11 (by rfl)]
  exact reduction_erase cost (machineSampling sampling 0) g X h g₂ X₂ 0 1 constantCode
    (g, g₂, X, X₂, h, false, ()) constantAdv rfl

example : (Ty.load (base := cryptoBase F F F Bool Bool) (.list .nat) [0, 2]).steps = 7 := rfl

-- A constant source cannot certify a different adversary merely by matching one key.
example : ¬ (∀ (g g₂ X X₂ h : F),
    constantCode.denote (arithmetic F F F Bool Bool cost) (sourceSemantics 1)
      (g, g₂, X, X₂, h, false, ()) =
      (pure (decide (X₂ = 0), 0) : OracleComp (BLS.ROM.advSpec Bool F) (Bool × F))) := by
  intro he
  have hz := he 0 0 0 0 0
  simp [constantCode, Program.denote, Expr.denote, Var.get, arithmetic] at hz

private def fixedAnswer : Machine.Package (cryptoBase F F F Bool Bool) [] .nat where
  dataTypes := [.nat]
  data := (41, ())
  code := ⟨.unit, .unit, .ret (.var .here)⟩

-- Loading a constant is not a free pure computation, even when there are no oracle queries.
example : fixedAnswer.run cost sampling () = pure ⟨41, 51⟩ := by
  rw [Machine.Package.run_eq]
  dsimp [fixedAnswer, Env.append, Machine.Code.run, Program.run, Expr.run,
    Var.get, Var.depth, StateT.run, StateT.bind, StateT.pure, Env.load, Ty.load]
  simp

end SignaturesTest.RuntimeCertificate

open Lean Elab Command

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Ty.load_value, ``Env.load_value, ``Env.attach_value, ``Env.attach_steps,
      ``Machine.Package.run_eq, ``Machine.Package.steps_pos, ``Machine.Within.two_lt,
      ``Coron.machineFinish_run, ``Coron.machineFinish_bound, ``Coron.machineFinish_erase,
      ``Coron.machineReductionCode_run, ``Coron.machineReductionCode_bound,
      ``Coron.machineReductionCode_erase, ``Coron.challengeSetup_run,
      ``Coron.SourceCertificate.within, ``BLS.Statement.bls_eufcma_of_cocdh_machine_hardness] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
