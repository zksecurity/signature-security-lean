import Signatures.Runtime.BackendSchnorrPrivateSamplingResources
import Lean.Util.CollectAxioms

/-! Resource regressions for sequential replay-store growth and total native
sampler certification. The loop examples inspect the same proof instrumentation
whose cost projection is proved equal to actual compiled execution. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr.RawTape

namespace SignaturesTest.BackendStateSimulationBudget

variable {C : StepClass} [C.HasProd] {Q : QuantitativeStepClass C} (nat : C.Str Nat)

private def control : ControlCosts where
  localCall := fun _ _ => 0
  query := fun _ _ => 0
  sequence := fun _ _ => 0
  branch := fun _ => 0
  retain := fun _ _ => 0
  loop := fun _ _ => 2

/-- One consumed request appends a cell and costs four steps. -/
private def draw (p : Nat × Nat) : ProbComp (StateSimulation.Audit Nat Nat Nat) :=
  pure (⟨(p.1, p.2 + 1), 4⟩, { visits := 1, requests := [0] })

/-- Two draws advance the same store twice and incur all three loop tests.
The pricing bound also reserves a routing charge at each source query node. -/
example :
    (fun z : StateSimulation.Audit Nat Nat Nat =>
      (z.1.value, z.1.steps, z.2.price 2 4, z.2.requests)) <$>
      StateSimulation.auditIteration (Q := Q) nat control nat nat draw 2 (7, 10) =
      pure ((7, 12), 14, 18, [0, 0]) := by
  rfl

/-- No iterations means no request and no store growth, but the exit test
still costs time. -/
example :
    (fun z : StateSimulation.Audit Nat Nat Nat => (z.1.value, z.1.steps, z.2.requests)) <$>
      StateSimulation.auditIteration (Q := Q) nat control nat nat draw 0 (7, 10) =
      pure ((7, 10), 2, []) := by
  rfl

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``StateSimulation.structuralBound, ``StateSimulation.auditLoop_bound,
      ``StateSimulation.auditIteration_bound, ``StateSimulation.audit_bound,
      ``StateSimulation.native_bound, ``NativePrivate.runtimeBound_saved_mono,
      ``NativePrivate.sampler_bound, ``NativePrivate.samplerTime_polynomial] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  forallTelescope (← getConstInfo ``NativePrivate.sampler_bound).type fun params conclusion => do
    unless conclusion.isAppOf ``Bounds do
      throwError "the complete sampler must have an actual native runtime bound"
    let mut sourceResource := false
    for param in params do
      let type ← inferType param
      if (type.find? (fun e => e.isConstOf ``ExecutionProfile.Within)).isSome then
        sourceResource := true
      for forbidden in #[``Bounds, ``StateSimulation.StructuralBound, ``StateSimulation.AuditBound,
          `Signatures.Runtime.Schnorr.SourceCertificate, ``Program, ``Fintype, ``Finite] do
        if (type.find? (fun e => e.isConstOf forbidden)).isSome then
          throwError "the total sampler must derive native budgets from source resources and primitive laws"
    unless sourceResource do
      throwError "the total sampler theorem must account for the original sampler's measured execution"
  for name in #[``NativePrivate.samplerTime, ``NativePrivate.samplerTime_polynomial] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let name := (← getFVarLocalDecl param).userName
        if #[`arityCap, `counter, `counterCap, `randomBound, `domainSize].contains name then
          throwError "runtime must not enumerate numeric counters, sampling arities or the query domain"

end SignaturesTest.BackendStateSimulationBudget
