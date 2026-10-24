import Proofs.Runtime.BackendMachine
import Proofs.Runtime.CoronMachineReduction

/-! The lazy Coron reply and final extraction routines in the common backend.

These definitions compile the existing first-order routines. Their semantics and
cache growth are proved from the existing lazy simulation, preserving its joint
randomness and persistent state. Their backend costs are still the costs of the
compiled code; the old arithmetic step count is not silently reused.
-/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Coron

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (data : DataCode Q rep.data) (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))

@[irreducible] def backendReply (qS : Nat) (signing : Bool) :
    Code Q unifSpec iface (StepClass.HasProd.prod (rep.ty message) (rep.ty (machineStore qS)))
      (StepClass.HasProd.prod (rep.ty point₁) (rep.ty (machineStore qS))) :=
  MachineCompiler.unary rep data samplingCode cost primitive (machineStore qS) (machineReply qS signing)

@[irreducible] def backendFinish (qS : Nat) :
    Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.ty (.pair message point₁)) (rep.ty (machineStore qS)))
      (StepClass.HasProd.prod (rep.ty point₁) (rep.ty (machineStore qS))) :=
  MachineCompiler.unary rep data samplingCode cost primitive (machineStore qS) (machineFinish qS)

theorem backendReply_denote (sampling : Machine.SamplingCosts)
    (g X h : G₁) (qS : Nat) (signing : Bool) (m : M) (state : CacheState F M qS) :
    (backendReply rep data samplingCode cost primitive qS signing).denote (m, machineState g X h state) =
      (fun r => (r.1.value, machineState g X h r.2)) <$>
        (reply (G₂ := G₂) cost (machineSampling sampling qS) g X h qS signing m).run state := by
  rw [backendReply, MachineCompiler.unary_denote rep data samplingCode cost primitive sampling,
    machineReply_run]
  simp only [Functor.map_map]

theorem backendFinish_denote (sampling : Machine.SamplingCosts)
    (g X h : G₁) (qS : Nat) (out : M × G₁) (state : CacheState F M qS) :
    Prod.fst <$> (backendFinish rep data samplingCode cost primitive qS).denote
      (out, machineState g X h state) =
        Run.value <$> finish (G₂ := G₂) cost (machineSampling sampling qS) g X h qS out state := by
  rw [backendFinish, MachineCompiler.unary_denote rep data samplingCode cost primitive sampling]
  simpa only [Functor.map_map] using machineFinish_erase cost sampling g X h qS out state

/-- Cache growth transfers to the new execution while retaining its actual
backend cost. The bound counts encountered messages, including signing lookups. -/
theorem backendReply_cache_bound (control : ControlCosts)
    (queryCost : (i : Nat) → unifSpec.Range i → Nat) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (qS : Nat) (signing : Bool) (m : M) (state : CacheState F M qS)
    (z : Run (G₁ × (machineStore qS).Value (cryptoBase F G₁ G₂ M M)))
    (hz : z ∈ support ((backendReply rep data samplingCode cost primitive qS signing).run
      control queryCost (m, machineState g X h state))) :
    (machineCaches z.value.2).size ≤ state.size + 1 := by
  have hv : z.value ∈ support ((backendReply rep data samplingCode cost primitive qS signing).denote
      (m, machineState g X h state)) := by
    exact Code.value_mem_denote control queryCost
      (backendReply rep data samplingCode cost primitive qS signing) (m, machineState g X h state) z hz
  rw [backendReply_denote rep data samplingCode cost primitive sampling, support_map] at hv
  obtain ⟨r, hr, he⟩ := hv
  rw [← he]
  exact (reply_bound (G₂ := G₂) cost (machineSampling sampling qS) g X h qS signing m state r hr).1

end Signatures.Runtime.Coron
