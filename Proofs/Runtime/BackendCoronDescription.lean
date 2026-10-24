import Proofs.Runtime.BackendMachineSize
import Proofs.Runtime.BackendCoronFinishBudget

/-! Static descriptions for Coron's actual native reply and final extraction.
The bound contains the two primitive sampler descriptions, structural encoding
allowance, and descriptions of only the instructions that occur in these finite
wrappers. There is no enumeration of the message space or run transcript. -/

open OracleSpec PFunctor

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
  (sizes : DescriptionSize Q)

structure NativeInstructionDescriptions (qS instructionSize : Nat) : Prop where
  message : sizes.localSize (primitive CryptoOp.messageEq) ≤ instructionSize
  fieldZero : sizes.localSize (primitive CryptoOp.zero) ≤ instructionSize
  coinZero : sizes.localSize (primitive (CryptoOp.finZero qS)) ≤ instructionSize
  convert : sizes.localSize (primitive (CryptoOp.finVal qS)) ≤ instructionSize
  natEq : sizes.localSize (primitive CryptoOp.natEq) ≤ instructionSize
  pointZero : sizes.localSize (primitive CryptoOp.zero₁) ≤ instructionSize
  scale : sizes.localSize (primitive CryptoOp.scale₁) ≤ instructionSize
  add : sizes.localSize (primitive CryptoOp.add₁) ≤ instructionSize
  sub : sizes.localSize (primitive CryptoOp.sub₁) ≤ instructionSize

variable (allowance : Nat) (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)

include laws dataLaws

theorem backendReply_descriptionSize (qS : Nat) (signing : Bool) (instructionSize : Nat)
    (ops : NativeInstructionDescriptions rep cost primitive sizes qS instructionSize) :
    (backendReply rep data samplingCode cost primitive qS signing).descriptionSize sizes ≤
      samplingCode.scalar.descriptionSize sizes + (samplingCode.uniform qS).descriptionSize sizes +
        1000 * allowance + 10 * instructionSize + 100 := by
  unfold backendReply
  refine (MachineCompiler.unary_descriptionSize rep data samplingCode sizes allowance laws dataLaws cost primitive
    (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl) (machineStore qS) (machineReply qS signing)).trans ?_
  obtain ⟨hm, hf, hc, hv, he, hz, hs, ha, hsub⟩ := ops
  rw [ReplyCompiler.machineReply_eq]
  cases signing <;>
    simp only [ReplyCompiler.body, Bool.false_eq_true, ite_false, ite_true,
      Language.descriptionBound, ReplyCompiler.scalarArgs_description, ReplyCompiler.coinArgs_description,
      ReplyCompiler.writeState_description, ReplyCompiler.signArgs_description, ReplyCompiler.hashArgs_description] <;>
    dsimp [cacheGet, lookup, lookupBody, signReply, hashReply,
      MachineCompiler.effectsDescription, Language.descriptionBound, Expression.descriptionBound, Expression.argumentsDescription,
      Expression.variableDescription] <;> omega

theorem backendFinish_descriptionSize (qS instructionSize : Nat)
    (ops : NativeInstructionDescriptions rep cost primitive sizes qS instructionSize) :
    (backendFinish rep data samplingCode cost primitive qS).descriptionSize sizes ≤
      samplingCode.scalar.descriptionSize sizes + (samplingCode.uniform qS).descriptionSize sizes +
        1500 * allowance + 14 * instructionSize + 150 := by
  unfold backendFinish
  refine (MachineCompiler.unary_descriptionSize rep data samplingCode sizes allowance laws dataLaws cost primitive
    (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl) (machineStore qS) (machineFinish qS)).trans ?_
  obtain ⟨hm, hf, hc, hv, he, hz, hs, ha, hsub⟩ := ops
  simp only [machineFinish, ReplyCompiler.machineReply_eq, ReplyCompiler.body, Bool.false_eq_true, ite_false,
    Language.descriptionBound, ReplyCompiler.scalarArgs_description, ReplyCompiler.coinArgs_description,
    ReplyCompiler.writeState_description, ReplyCompiler.hashArgs_description]
  dsimp [cacheGet, lookup, lookupBody, signReply, hashReply, extract,
    MachineCompiler.effectsDescription, Language.descriptionBound, Expression.descriptionBound, Expression.argumentsDescription,
    Expression.variableDescription]
  omega

end Signatures.Runtime.Coron
