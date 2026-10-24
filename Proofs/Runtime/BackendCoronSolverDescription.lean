import Proofs.Runtime.BackendCoronSolver
import Proofs.Runtime.BackendCoronHandlerDescription

/-! Complete stored-code bound for the native Coron solver. The challenge is
input data, and setup stores only its fixed expression and empty-list code. All
attacker, handler, extraction, encoding, cutoff, and control descriptions are
counted; both terminal branches are stored even when cutoff is unreachable. -/

open OracleSpec PFunctor
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
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (sizes : DescriptionSize Q) (allowance : Nat)
  (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
  (dispatchLaws : DispatchDescriptionLaws (Q := Q) sizes allowance)

structure PortDescriptions (portSize : Nat) : Prop where
  key : sizes.localSize boundary.key ≤ portSize
  forgery : sizes.localSize boundary.forgery ≤ portSize
  optional : sizes.localSize boundary.optional ≤ portSize

include laws dataLaws

omit QO QD OC [SampleableType F] in
theorem setup_descriptionSize (qS : Nat) :
    (setup (iface := iface) rep bd boundary data cost primitive qS).descriptionSize sizes ≤
      37 * allowance + sizes.localSize boundary.key + 4 := by
  have h := Expression.compile_size rep data (arithmetic F G₁ G₂ M M cost) primitive sizes allowance laws dataLaws
    (fun instr => sizes.localSize (primitive instr)) (fun _ => le_refl _) (initial qS)
  dsimp only [initial, Expression.descriptionBound, Expression.variableDescription] at h
  dsimp only [setup, Code.descriptionSize, initial]
  omega

omit dataLaws QO QD OC in
theorem finishSome_descriptionSize (qS : Nat) :
    (finishSome rep bd boundary data samplingCode cost primitive qS).descriptionSize sizes ≤
      (backendFinish rep data samplingCode cost primitive qS).descriptionSize sizes +
        sizes.localSize boundary.forgery + allowance + 5 := by
  have h := laws.fst (rep.ty point₁) (rep.ty (machineStore qS))
  dsimp only [finishSome, Code.descriptionSize]
  omega

omit QO QD OC [C.HasOption] [SampleableType F] in
theorem cutoff_descriptionSize (qS : Nat) :
    (cutoff (iface := iface) rep data cost primitive qS).descriptionSize sizes ≤
      sizes.localSize (primitive CryptoOp.zero₁) + 2 * allowance + 1 := by
  have h := laws.compose_bound (dataLaws.unit (StepClass.HasProd.prod rep.data.unit (rep.ty (machineStore qS))))
    (le_refl (sizes.localSize (primitive CryptoOp.zero₁)))
  dsimp only [cutoff, Code.descriptionSize]
  omega

include dispatchLaws

theorem terminal_descriptionSize (qS : Nat) :
    (terminal rep bd boundary data samplingCode cost primitive qS).descriptionSize sizes ≤
      (backendFinish rep data samplingCode cost primitive qS).descriptionSize sizes +
        sizes.localSize boundary.optional + sizes.localSize boundary.forgery +
        sizes.localSize (primitive CryptoOp.zero₁) + 4 * allowance + 12 := by
  have hf := finishSome_descriptionSize rep bd boundary data samplingCode cost primitive sizes allowance laws qS
  have hc := cutoff_descriptionSize (iface := iface) rep data cost primitive sizes allowance laws dataLaws qS
  have hd := dispatchLaws.distribute rep.data.unit bd.out (rep.ty (machineStore qS))
  dsimp only [terminal, Code.descriptionSize]
  omega

theorem program_descriptionSize (qS fuel instructionSize handlerPortSize solverPortSize : Nat)
    (ops : NativeInstructionDescriptions rep cost primitive sizes qS instructionSize)
    (handlerPorts : NativeHandler.PortDescriptions rep bd ports sizes handlerPortSize)
    (solverPorts : PortDescriptions rep bd boundary sizes solverPortSize) :
    (program rep bd ports sampler boundary data samplingCode cost primitive R qS fuel).descriptionSize sizes ≤
      sizes.localSize R.initCode + 2 * sizes.localSize R.headCode + sizes.localSize R.updateCode + fuel +
      3 * samplingCode.scalar.descriptionSize sizes + 3 * (samplingCode.uniform qS).descriptionSize sizes +
      sampler.code.descriptionSize sizes + 4000 * allowance + 40 * instructionSize +
      4 * handlerPortSize + 3 * solverPortSize + 500 := by
  have hs := setup_descriptionSize (iface := iface) rep bd boundary data cost primitive sizes allowance laws dataLaws qS
  have ht := terminal_descriptionSize rep bd boundary data samplingCode cost primitive sizes allowance laws dataLaws dispatchLaws qS
  have hf := backendFinish_descriptionSize rep data samplingCode cost primitive sizes allowance laws dataLaws qS instructionSize ops
  have hh := NativeHandler.code_descriptionSize rep bd ports sampler data samplingCode cost primitive
    sizes allowance laws dataLaws dispatchLaws qS instructionSize handlerPortSize ops handlerPorts
  have hc := Caller.program_descriptionSize_bound R (rep.ty (machineStore qS)) sizes allowance laws dispatchLaws
    (NativeHandler.code rep bd ports sampler data samplingCode cost primitive qS) fuel
  have hk := solverPorts.key
  have hforgery := solverPorts.forgery
  have ho := solverPorts.optional
  have hz := ops.pointZero
  dsimp only [program, NativeHandler.caller, Code.descriptionSize] at *
  omega

end Signatures.Runtime.Coron.NativeSolver
