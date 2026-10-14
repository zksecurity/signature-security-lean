import Signatures.Runtime.BackendCoronSolverCorrectness
import Signatures.Runtime.GeneralCallerOutput

/-! Transfer caller output bounds to the actual native solver boundary. The
caller invariant bounds returned messages and the encoded terminal readout;
source correspondence transfers those state facts without transferring costs. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Coron.NativeSolver

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂ (M × G₁))
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (data : DataCode Q rep.data) (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (inv : Nat → R.machine.State → Prop) (valid : M × G₁ → Prop)
  (hstep : ∀ n state, inv (n + 1) state → ∀ i next,
    R.machine.view state = .inr ⟨i, next⟩ → ∀ reply, inv n (next reply))
  (hreturn : ∀ n state, inv n state → ∀ out, R.machine.view state = .inl out → valid out)

include hstep hreturn

theorem caller_output_invariant (qS fuel : Nat) (pk : G₂) (hi : inv fuel (R.machine.init pk))
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M))
    (z : Run (Option (M × G₁) × (machineStore qS).Value (cryptoBase F G₁ G₂ M M)))
    (hz : z ∈ support ((NativeHandler.caller rep bd ports sampler data samplingCode cost primitive R qS fuel).run
      control queryCost (pk, saved))) (out : M × G₁) (hout : z.value.1 = some out) : valid out := by
  have hv := Code.value_mem_denote control queryCost
    (NativeHandler.caller rep bd ports sampler data samplingCode cost primitive R qS fuel) (pk, saved) z hz
  rw [caller_reference_denote rep bd ports sampler data samplingCode cost primitive R ⟨0, fun _ => 0⟩,
    support_map] at hv
  obtain ⟨p, hp, he⟩ := hv
  exact GeneralCaller.run_output_invariant R
    (generalHandler (F := F) (G₂ := G₂) cost ⟨0, fun _ => 0⟩ qS randomBound)
    inv valid hstep hreturn fuel pk hi saved p hp out ((congrArg Prod.fst he).trans hout)

variable {header : Nat} (sizes : SizeLaws Q header)

include sizes

omit hreturn in
theorem caller_output_sizes (width routeWidth : Nat)
    (hhead : ∀ n state, inv n state → Q.size bd.head (R.machine.head state) ≤ routeWidth)
    (hmessage : ∀ n state, inv n state → ∀ out, R.machine.view state = .inl out →
      Q.size (rep.ty message) out.1 ≤ width)
    (qS fuel : Nat) (pk : G₂) (hi : inv fuel (R.machine.init pk))
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M))
    (z : Run (Option (M × G₁) × (machineStore qS).Value (cryptoBase F G₁ G₂ M M)))
    (hz : z ∈ support ((NativeHandler.caller rep bd ports sampler data samplingCode cost primitive R qS fuel).run
      control queryCost (pk, saved))) (out : M × G₁) (hout : z.value.1 = some out) :
    Q.size bd.out out ≤ routeWidth ∧ Q.size (rep.ty message) out.1 ≤ width := by
  apply caller_output_invariant rep bd ports sampler data samplingCode cost primitive control queryCost R inv
    (fun out => Q.size bd.out out ≤ routeWidth ∧ Q.size (rep.ty message) out.1 ≤ width) hstep _ qS fuel pk hi saved z hz out hout
  intro n state hs out hv
  have hh := hhead n state hs
  rw [R.machine.head_eq_inl_of_view hv] at hh
  exact ⟨(sizes.sum_payload_le bd.out bd.pos (.inl out)).trans hh, hmessage n state hs out hv⟩

end Signatures.Runtime.Coron.NativeSolver
