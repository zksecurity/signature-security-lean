import Proofs.Runtime.BackendStateSimulationErasure
import Proofs.Runtime.BackendStateSimulationProfile
import Proofs.Runtime.BackendExecutionProfileBounds

/-! Recover original execution resources on the same path as an actual native
run. The native result includes its actual step count, not merely the output
distribution. Numeric overhead composition is separate from this coupling. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.StateSimulation

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QD : Q.IsDistributive]
  {I J S : Type} {source : OracleSpec I} {target : OracleSpec J}
  {src : Interface (C := C) source} {dst : Interface (C := C) target}
  (store : C.Str S) (control : ControlCosts)
  (queryCost : (j : J) → target.Range j → Nat)
  (handler : Code Q target dst (StepClass.HasProd.prod src.position store)
    (StepClass.HasProd.prod src.response store))
  (H : QueryImpl source (StateT S (OracleComp target)))
  (hhandler : ∀ i saved, handler.denote (i, saved) =
    (fun p => (Sigma.mk i p.1, p.2)) <$> (H i).run saved)

include hhandler

theorem native_profile {A B : Type} {a : C.Str A} {b : C.Str B}
    (program : Code Q source src a b) (input : A) (saved : S) (z : Run (B × S))
    (hz : z ∈ support ((compile store handler program).run control queryCost (input, saved))) :
    ∃ metrics : ExecutionProfile.Metrics I,
      (z, metrics) ∈ support (audit store control queryCost handler program (input, saved)) ∧
        (z.value.1, metrics) ∈ support (ExecutionProfile.run program input) := by
  rw [← audit_erase, support_map] at hz
  obtain ⟨⟨run, metrics⟩, hr, he⟩ := hz
  change run = z at he
  subst run
  exact ⟨metrics, hr, audit_mem_profile store control queryCost handler H hhandler program input saved _ hr⟩

theorem native_resources {A B : Type} {a : C.Str A} {b : C.Str B}
    (program : Code Q source src a b) (input : A)
    (work visits queries width counter : Nat) (allowed : I → Prop)
    (hsource : ExecutionProfile.Within program input work visits queries width counter allowed)
    (saved : S) (z : Run (B × S))
    (hz : z ∈ support ((compile store handler program).run control queryCost (input, saved))) :
    ∃ metrics : ExecutionProfile.Metrics I,
      (z, metrics) ∈ support (audit store control queryCost handler program (input, saved)) ∧
        metrics.work ≤ work ∧ metrics.visits ≤ visits ∧ metrics.requests.length ≤ queries ∧
          metrics.Fits width counter allowed ∧ Q.size a input ≤ width ∧ Q.size b z.value.1 ≤ width := by
  obtain ⟨metrics, ha, hm⟩ := native_profile store control queryCost handler H hhandler program input saved z hz
  obtain ⟨hw, hv, hq, hf⟩ := hsource _ hm
  obtain ⟨hi, ho⟩ := ExecutionProfile.run_sizes program input _ hm
  exact ⟨metrics, ha, hw, hv, hq, hf, hi.trans hf.1, ho.trans hf.1⟩

end Signatures.Runtime.BackendProgram.StateSimulation
