import Proofs.Runtime.BackendCoronHandler
import Proofs.Runtime.BackendCallerDescription

/-! Code-size overhead of the complete native Coron dispatcher. There are
three branches and one dynamic sampler; no table indexed by message or random
range is stored. The caller's own descriptions are handled separately by
`Caller.program_descriptionSize_bound`. -/

open OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Coron.NativeHandler

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
  (sizes : DescriptionSize Q) (allowance : Nat)
  (laws : LocalDescriptionLaws sizes allowance)

include laws

omit [C.HasOption] QO QD OC in
theorem group_descriptionSize (qS : Nat) (signing : Bool) :
    (group rep bd ports data samplingCode cost primitive qS signing).descriptionSize sizes ≤
      (backendReply rep data samplingCode cost primitive qS signing).descriptionSize sizes +
      sizes.localSize (ports.groupTag signing) + 18 * allowance + 8 := by
  have hc := Language.withContext_descriptionSize sizes allowance laws (rep.ty (machineStore qS))
    (Q.identity (rep.ty message)) (backendReply rep data samplingCode cost primitive qS signing)
  have hi := laws.identity (rep.ty message)
  have ht : sizes.localSize (Q.compose
      (QP.pair (QP.snd (rep.ty point₁) (rep.ty message)) (QP.fst (rep.ty point₁) (rep.ty message)))
      (ports.groupTag signing)) ≤ sizes.localSize (ports.groupTag signing) + 4 * allowance :=
    (laws.compose_bound (laws.pair_bound (laws.snd _ _) (laws.fst _ _))
      (le_refl (sizes.localSize (ports.groupTag signing)))).trans (by omega)
  dsimp only [group, Code.descriptionSize]
  omega

omit laws [C.HasOption] [Q.HasCategory] QP QS QO QD OC [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq M] in
theorem random_descriptionSize (qS : Nat) :
    (random rep bd ports sampler qS).descriptionSize sizes =
      sampler.code.descriptionSize sizes + sizes.localSize ports.randomTag + 4 := by
  dsimp only [random, Code.descriptionSize]
  omega

variable (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
  (dispatchLaws : DispatchDescriptionLaws (Q := Q) sizes allowance)

structure PortDescriptions (portSize : Nat) : Prop where
  request : sizes.localSize ports.request ≤ portSize
  randomTag : sizes.localSize ports.randomTag ≤ portSize
  groupTag : ∀ signing, sizes.localSize (ports.groupTag signing) ≤ portSize

include dataLaws dispatchLaws

theorem code_descriptionSize (qS instructionSize portSize : Nat)
    (ops : NativeInstructionDescriptions rep cost primitive sizes qS instructionSize)
    (portCaps : PortDescriptions rep bd ports sizes portSize) :
    (code rep bd ports sampler data samplingCode cost primitive qS).descriptionSize sizes ≤
      2 * samplingCode.scalar.descriptionSize sizes + 2 * (samplingCode.uniform qS).descriptionSize sizes +
      sampler.code.descriptionSize sizes + 2100 * allowance + 20 * instructionSize + 4 * portSize + 250 := by
  have hh := group_descriptionSize rep bd ports data samplingCode cost primitive sizes allowance laws qS false
  have hs := group_descriptionSize rep bd ports data samplingCode cost primitive sizes allowance laws qS true
  have hhr := backendReply_descriptionSize rep data samplingCode cost primitive sizes allowance laws dataLaws qS false instructionSize ops
  have hsr := backendReply_descriptionSize rep data samplingCode cost primitive sizes allowance laws dataLaws qS true instructionSize ops
  have hr := random_descriptionSize rep bd ports sampler sizes qS
  have hd1 := dispatchLaws.distribute (rep.ty (boundedNat randomBound)) (rep.ty message) (rep.ty (machineStore qS))
  have hd2 := dispatchLaws.distribute (StepClass.HasSum.sum (rep.ty (boundedNat randomBound)) (rep.ty message))
    (rep.ty message) (rep.ty (machineStore qS))
  have hp := portCaps.request
  have hpr := portCaps.randomTag
  have hph := portCaps.groupTag false
  have hps := portCaps.groupTag true
  dsimp only [code, dispatch, inner, Code.descriptionSize, generalPositions] at *
  omega

end Signatures.Runtime.Coron.NativeHandler
