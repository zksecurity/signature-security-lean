import Proofs.Runtime.BackendWeightedSolver
import Proofs.Runtime.BackendWeightedOracleDescription
import Proofs.Runtime.BackendWeightedExtractionDescription

/-! Stored descriptions of the complete native AGM solvers. The bounds count
the attacker's actual code, query handler, samplers, both terminal branches, and
the extractor. A common conservative allowance covers either solver. Challenges
are input data, and neither bound depends on the size of the message domain. -/

open OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.WeightedAGM.NativeSolver

open BackendProgram NativeHandler Reply LazyAGM.ReplySyntax

def termDescriptionCap (degree allowance instructionSize : Nat) : Nat :=
  (degree + 1) * (degree + 1 + 2 * instructionSize + 32 * allowance) +
    2 * instructionSize + 16 * allowance

theorem termsDescription_le (index : Index) (allowance instructionSize : Nat)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (ops : ∀ {a b} (instr : CryptoOp a b), primitiveSize instr ≤ instructionSize) :
    index.termsDescription allowance primitiveSize ≤ termDescriptionCap index.bound allowance instructionSize := by
  have hfin := ops (.finOfNat index.bound)
  have hzero := ops (.finZero index.bound)
  have hone := ops .one
  have hmul := ops .mul
  cases index <;>
    dsimp only [Index.termsDescription, Index.bound, Terms.oopsDescription,
      Terms.oopsFromDescription, Terms.proximityDescription, Terms.proximityFromDescription,
      Terms.syncDescription, termDescriptionCap] at * <;>
    nlinarith

def programDescription (degree callerSize scalarSamplerSize dynamicSamplerSize fuel allowance
    instructionSize handlerPortSize solverPortSize : Nat) : Nat :=
  callerSize + 9 * scalarSamplerSize + dynamicSamplerSize + fuel +
    128 * instructionSize + 4 * handlerPortSize + 3 * solverPortSize +
    3 * termDescriptionCap degree allowance instructionSize + 16000 * allowance + 2048

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (index : Index)
  (bd : Boundary C (generalSpec (index.ty.Value (cryptoBase F G₁ G₂ K M)) (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor G₂
    ((AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M)))
  (ports : NativePorts (Q := Q) rep index.ty index.messageTy bd) (sampler : BoundedSampler rep index.ty index.messageTy bd ports (iface := iface))
  (boundary : DataPorts (Q := Q) rep index bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (sizes : DescriptionSize Q) (allowance : Nat)
  (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
  (dispatch : DispatchDescriptionLaws (Q := Q) sizes allowance)

structure PortDescriptions (portSize : Nat) : Prop where
  key : sizes.localSize boundary.key ≤ portSize
  output : sizes.localSize boundary.output ≤ portSize
  optional : sizes.localSize boundary.optional ≤ portSize

structure HandlerPortDescriptions (portSize : Nat) : Prop where
  request : sizes.localSize ports.request ≤ portSize
  randomTag : sizes.localSize ports.randomTag ≤ portSize
  hashTag : sizes.localSize ports.hashTag ≤ portSize
  signTag : sizes.localSize ports.signTag ≤ portSize

include laws dataLaws

omit QO QD OC [SampleableType F] in
theorem setupGood_description :
    (setupGood (iface := iface) rep index bd boundary data cost primitive).descriptionSize sizes ≤
      sizes.localSize boundary.key + 40 * allowance + 4 := by
  have h := Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance laws dataLaws
    (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl) (initialGood index)
  dsimp only [initialGood, v0, v1, v3, Expression.descriptionBound, Expression.variableDescription] at h
  dsimp only [setupGood, Code.descriptionSize, initialGood, v0, v1, v3]
  omega

omit QO QD OC in
theorem setupBad_description :
    (setupBad rep index bd boundary data cost primitive sampling).descriptionSize sizes ≤
      sampling.scalar.descriptionSize sizes + sizes.localSize (primitive .scale₂) +
        sizes.localSize boundary.key + 80 * allowance + 12 := by
  have h := Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance laws dataLaws
    (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl) (initialBad index)
  have hp := laws.pair_bound (dataLaws.unit (rep.env inputTypes)) (laws.identity (rep.env inputTypes))
  dsimp only [initialBad, v0, v1, v2, v3, Expression.descriptionBound, Expression.variableDescription] at h
  dsimp only [setupBad, Code.descriptionSize, initialBad, v0, v1, v2, v3]
  omega

omit QO QD OC [C.HasOption] [SampleableType F] in
theorem extractionArgsCode_description (value config : Ty CryptoAtom) :
    sizes.localSize (extractionArgsCode rep index data cost primitive value config) ≤ 64 * allowance := by
  have h := Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance laws dataLaws
    (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl) (extractionArgs index value config)
  have hp := laws.pair_bound (laws.identity (rep.ty (.pair (AGM.outputTy index.messageTy) (Reply.storeTy index.ty index.messageTy value config))))
    (dataLaws.unit (rep.ty (.pair (AGM.outputTy index.messageTy) (Reply.storeTy index.ty index.messageTy value config))))
  have hc := laws.compose_bound hp h
  dsimp only [extractionArgs, v0, Expression.descriptionBound, Expression.variableDescription] at hc
  exact hc.trans (by omega)

omit QO QD OC [SampleableType F] in
theorem finishSome_description (value config : Ty CryptoAtom)
    (extractor : Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.env [AGM.outputTy index.messageTy, (Reply.transcriptTy index.ty index.messageTy)]) (rep.ty (Reply.cacheTy index.ty value)))
      (rep.ty (.pair scalar (Reply.cacheTy index.ty value)))) :
    (finishSome rep index bd boundary data cost primitive value config extractor).descriptionSize sizes ≤
      extractor.descriptionSize sizes + sizes.localSize boundary.output + 65 * allowance + 7 := by
  have ha := extractionArgsCode_description rep index data cost primitive sizes allowance laws dataLaws value config
  have hf := laws.fst (rep.ty scalar) (rep.ty (Reply.cacheTy index.ty value))
  dsimp only [finishSome, Code.descriptionSize]
  omega

omit QO QD OC [C.HasOption] [SampleableType F] in
theorem cutoff_description (value config : Ty CryptoAtom) :
    (cutoff (iface := iface) rep index data cost primitive value config).descriptionSize sizes ≤
      sizes.localSize (primitive .zero) + 2 * allowance + 1 := by
  have h := laws.compose_bound (dataLaws.unit (StepClass.HasProd.prod rep.data.unit (rep.ty (Reply.storeTy index.ty index.messageTy value config))))
    (le_rfl : sizes.localSize (primitive .zero) ≤ sizes.localSize (primitive .zero))
  dsimp only [cutoff, Code.descriptionSize]
  omega

include dispatch

omit [SampleableType F] in
theorem terminal_description (value config : Ty CryptoAtom)
    (extractor : Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.env [AGM.outputTy index.messageTy, (Reply.transcriptTy index.ty index.messageTy)]) (rep.ty (Reply.cacheTy index.ty value)))
      (rep.ty (.pair scalar (Reply.cacheTy index.ty value)))) :
    (terminal rep index bd boundary data cost primitive value config extractor).descriptionSize sizes ≤
      extractor.descriptionSize sizes + sizes.localSize boundary.output + sizes.localSize boundary.optional +
        sizes.localSize (primitive .zero) + 80 * allowance + 20 := by
  have hf := finishSome_description rep index bd boundary data cost primitive sizes allowance laws dataLaws value config extractor
  have hc := cutoff_description (iface := iface) rep index data cost primitive sizes allowance laws dataLaws value config
  have hd := dispatch.distribute rep.data.unit bd.out (rep.ty (Reply.storeTy index.ty index.messageTy value config))
  dsimp only [terminal, Code.descriptionSize]
  omega

variable (R : GeneralCaller.Caller (Q := Q) (bd := bd))

theorem goodProgram_description (fuel instructionSize handlerPortSize solverPortSize : Nat)
    (ops : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ instructionSize)
    (handlerPorts : HandlerPortDescriptions rep index bd ports sizes handlerPortSize)
    (solverPorts : PortDescriptions rep index bd boundary sizes solverPortSize) :
    (goodProgram rep index bd ports sampler boundary data cost primitive sampling R fuel).descriptionSize sizes ≤
      programDescription index.bound (sizes.localSize R.initCode + 2 * sizes.localSize R.headCode + sizes.localSize R.updateCode)
        (sampling.scalar.descriptionSize sizes) (sampler.code.descriptionSize sizes)
        fuel allowance instructionSize handlerPortSize solverPortSize := by
  have hs := setupGood_description (iface := iface) rep index bd boundary data cost primitive sizes allowance laws dataLaws
  have hc := goodCaller_description rep index bd ports sampler data cost primitive sampling sizes allowance laws dataLaws dispatch R fuel
  have he := Extract.backendGood_description rep data cost primitive sampling index sizes allowance laws dataLaws
  have ht := terminal_description rep index bd boundary data cost primitive sizes allowance laws dataLaws dispatch
    scalar LazyAGM.goodConfigTy (Extract.backendGood rep data cost primitive sampling index)
  have hk := solverPorts.key
  have ho := solverPorts.output
  have hopt := solverPorts.optional
  have hr := handlerPorts.request
  have hrt := handlerPorts.randomTag
  have hgh := handlerPorts.hashTag
  have hgs := handlerPorts.signTag
  have hz := ops .zero
  have heq := ops .keyEq
  have hval := ops (.finVal index.bound)
  have hfin := ops (.finZero index.bound)
  have hone := ops .one
  have hterms := termsDescription_le index allowance instructionSize (fun instr => sizes.localSize (primitive instr)) ops
  have hscale := ops .scale₁
  have hne := ops .natEq
  have hns := ops .natSub
  have hna := ops .natAdd
  have ha := ops .add
  have hm := ops .mul
  have hsub := ops .sub
  have hd := ops .div
  dsimp only [goodProgram, Code.descriptionSize, programDescription]
  omega

theorem badProgram_description (fuel instructionSize handlerPortSize solverPortSize : Nat)
    (ops : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ instructionSize)
    (handlerPorts : HandlerPortDescriptions rep index bd ports sizes handlerPortSize)
    (solverPorts : PortDescriptions rep index bd boundary sizes solverPortSize) :
    (badProgram rep index bd ports sampler boundary data cost primitive sampling R fuel).descriptionSize sizes ≤
      programDescription index.bound (sizes.localSize R.initCode + 2 * sizes.localSize R.headCode + sizes.localSize R.updateCode)
        (sampling.scalar.descriptionSize sizes) (sampler.code.descriptionSize sizes)
        fuel allowance instructionSize handlerPortSize solverPortSize := by
  have hs := setupBad_description rep index bd boundary data cost primitive sampling sizes allowance laws dataLaws
  have hc := badCaller_description rep index bd ports sampler data cost primitive sampling sizes allowance laws dataLaws dispatch R fuel
  have he := Extract.backendBad_description rep data cost primitive sampling index sizes allowance laws dataLaws
  have ht := terminal_description rep index bd boundary data cost primitive sizes allowance laws dataLaws dispatch
    (.pair scalar scalar) LazyAGM.badConfigTy (Extract.backendBad rep data cost primitive sampling index)
  have hk := solverPorts.key
  have ho := solverPorts.output
  have hopt := solverPorts.optional
  have hr := handlerPorts.request
  have hrt := handlerPorts.randomTag
  have hgh := handlerPorts.hashTag
  have hgs := handlerPorts.signTag
  have hz := ops .zero
  have heq := ops .keyEq
  have hval := ops (.finVal index.bound)
  have hfin := ops (.finZero index.bound)
  have hone := ops .one
  have hterms := termsDescription_le index allowance instructionSize (fun instr => sizes.localSize (primitive instr)) ops
  have hscale := ops .scale₁
  have hscale₂ := ops .scale₂
  have hgroupAdd := ops .add₁
  have hne := ops .natEq
  have hns := ops .natSub
  have hna := ops .natAdd
  have ha := ops .add
  have hm := ops .mul
  have hsub := ops .sub
  have hneg := ops .neg
  have hd := ops .div
  dsimp only [badProgram, Code.descriptionSize, programDescription]
  omega

end Signatures.Runtime.WeightedAGM.NativeSolver
