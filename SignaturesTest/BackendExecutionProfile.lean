import Signatures.Runtime.BackendStateSimulationResources
import Signatures.Runtime.BackendStateSimulationRouting
import Lean.Util.CollectAxioms

/-! Regression cases for source resources and their coupling to actual compiled
costs. Control visits must survive zero primitive costs, skipped branches must
not count, and exhausted loops must charge their stop program. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram

namespace SignaturesTest.BackendExecutionProfile

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C}
  [Q.HasCategory] [Q.HasProd] [QS : Q.HasSum] [Q.IsDistributive]
  (nat : C.Str Nat) {iface : Interface (C := C) unifSpec}

private def summary (z : ExecutionProfile.Result Nat Nat) : Nat × Nat × Nat × List Nat :=
  (z.1, z.2.work, z.2.visits, z.2.requests)

/-- Three iterations count their three body calls, four loop tests and one
outer frame. The body is stored once, but its work is charged three times. -/
example :
    summary <$> ExecutionProfile.run (iface := iface) (.iterate nat (.atomic (Q.identity nat))) (3, 2) =
      pure (2, 3 * Q.cost (Q.identity nat) 2, 8, []) := by
  simp [ExecutionProfile.run, ExecutionProfile.iteration, ExecutionProfile.frame, ExecutionProfile.Metrics.join, ExecutionProfile.Metrics.node, summary,
    Nat.succ_mul, Nat.add_assoc]

/-- A backend's zero local cost cannot erase executed control nodes. -/
example (hcost : Q.cost (Q.identity nat) 2 = 0) :
    summary <$> ExecutionProfile.run (iface := iface) (.iterate nat (.atomic (Q.identity nat))) (3, 2) =
      pure (2, 0, 8, []) := by
  simp [ExecutionProfile.run, ExecutionProfile.iteration, ExecutionProfile.frame, ExecutionProfile.Metrics.join, ExecutionProfile.Metrics.node, summary, hcost]

/-- The enormous fuel in the unchosen branch contributes no visits or work. -/
example :
    summary <$> ExecutionProfile.run (iface := iface)
      (.branch (.loop (.atomic (QS.inl nat nat)) (.atomic (Q.identity nat)) (2^64))
        (.atomic (Q.identity nat))) (.inr 7) =
      pure (7, Q.cost (Q.identity nat) 7, 2, []) := by
  simp [ExecutionProfile.run, ExecutionProfile.frame, ExecutionProfile.Metrics.node, summary]

/-- Fuel zero executes and charges stop code. -/
example :
    summary <$> ExecutionProfile.run (iface := iface)
      (.loop (.atomic (QS.inr nat nat)) (.atomic (Q.identity nat)) 0) 7 =
      pure (7, Q.cost (Q.identity nat) 7, 2, []) := by
  simp [ExecutionProfile.run, ExecutionProfile.loop, ExecutionProfile.frame, ExecutionProfile.Metrics.node, summary]

/-- An immediate return charges the body and loop test, but does not execute
stop code or use the remaining fuel. The reached counter is still recorded. -/
example :
    (fun z : ExecutionProfile.Result Nat Nat => (summary z, z.2.counter)) <$>
      ExecutionProfile.run (iface := iface)
        (.loop (.atomic (QS.inl nat nat)) (.atomic (Q.identity nat)) 100) 7 =
      pure ((7, Q.cost (QS.inl nat nat) 7, 2, []), 100) := by
  rfl

/-- Queries remain oracle effects and their actual request is recorded. -/
example :
    (fun z => (z.1, z.2.work, z.2.visits, z.2.requests)) <$>
      ExecutionProfile.run (Q := Q) (iface := iface) .query 2 =
      (fun r : Fin 3 => (Sigma.mk 2 r, 0, 1, [2])) <$>
        (unifSpec.query 2 : ProbComp (Fin 3)) := by
  simp [ExecutionProfile.run, ExecutionProfile.frame, ExecutionProfile.Metrics.node, Functor.map_map]

private def control : ControlCosts where
  localCall := fun _ _ => 3
  query := fun _ _ => 0
  sequence := fun _ _ => 0
  branch := fun _ => 0
  retain := fun _ _ => 5
  loop := fun _ _ => 0

/-- The joint witness retains actual call/copy costs separately from original
local work. They cannot disappear by merely projecting the returned value. -/
example {S : Type} (store : C.Str S) (saved : S)
    (handler : Code Q unifSpec iface (StepClass.HasProd.prod iface.position store)
      (StepClass.HasProd.prod iface.response store)) :
    (fun z : StateSimulation.Audit Nat Nat S => (z.1.steps, z.2.work, z.2.visits)) <$>
      StateSimulation.audit store control (fun _ _ => 0) handler (.atomic (Q.identity nat)) (7, saved) =
      pure (Q.cost (Q.identity nat) 7 + 8, Q.cost (Q.identity nat) 7, 1) := by
  simp [StateSimulation.audit, StateSimulation.auditFrame, StateSimulation.localWork, ExecutionProfile.frame, ExecutionProfile.Metrics.node, control,
    Nat.add_assoc]

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``ExecutionProfile.erase, ``ExecutionProfile.run_sizes, ``ExecutionProfile.Within.price,
      ``StateSimulation.audit_erase, ``StateSimulation.audit_source, ``StateSimulation.native_profile, ``StateSimulation.native_resources,
      ``StateSimulation.atomic_work, ``StateSimulation.sequence_work, ``StateSimulation.first_work, ``StateSimulation.iteration_work,
      ``StateSimulation.branch_work, ``StateSimulation.loop_body_work] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``StateSimulation.audit_erase, ``StateSimulation.audit_source] do
    forallTelescope (← getConstInfo name).type fun _ conclusion => do
      unless conclusion.isAppOf ``Eq do
        throwError "{name}: the complete computation must agree"
  for name in #[``StateSimulation.native_profile, ``StateSimulation.native_resources] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[``Bounds, `Signatures.Runtime.Schnorr.SourceCertificate,
            `Signatures.Runtime.AGM.SourceCertificate, ``Program] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: original resources cannot require a completed native budget or arithmetic source"

end SignaturesTest.BackendExecutionProfile
