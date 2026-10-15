import Signatures.Runtime.BackendSchnorrAGMSolver
import Signatures.Runtime.BackendSchnorrAGMHandlerDescription

/-! Complete stored-code bound for the assembled native Schnorr AGM solver.
The caller's own code, both sampling interfaces, every handler, extraction,
initial basis construction, boundary adapters and cutoff branch are counted. -/

open OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Solver

open BackendProgram Interface

def programDescription (callerCode samplerCode randomPortSize handlerPortSize solverPortSize fuel allowance instructionSize : Nat) : Nat :=
  callerCode + 4 * samplerCode + 2 * randomPortSize + 4 * handlerPortSize + 3 * solverPortSize +
    49 * instructionSize + fuel + 23000 * allowance + 512

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor (SourceInput G₁) (SourceForgery F G₁ M))
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sizes : DescriptionSize Q) (allowance : Nat) (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
  (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
  (hp : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ primitiveSize instr)

include laws dataLaws hp

theorem setup_description :
    (setup (iface := iface) rep bd boundary data cost primitive).descriptionSize sizes ≤
      sizes.localSize boundary.input + 2 * primitiveSize .zero + 2 * primitiveSize .one + 512 * allowance + 4 := by
  have h := Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance laws dataLaws
    primitiveSize hp initialExpression
  have h' : sizes.localSize (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive initialExpression) ≤
      2 * primitiveSize .zero + 2 * primitiveSize .one + 512 * allowance :=
    h.trans (by simp only [initialExpression, Expression.descriptionBound, Expression.variableDescription]; omega)
  dsimp only [setup, Code.descriptionSize]
  omega

omit dataLaws hp [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M] in
theorem finishSome_description (extractor : Code Q unifSpec iface (rep.ty Extraction.inputTy) (rep.ty Read.outputTy)) :
    (finishSome rep bd boundary extractor).descriptionSize sizes ≤
      extractor.descriptionSize sizes + sizes.localSize boundary.output + 6 * allowance + 8 := by
  have ha := adaptOutput_description (iface := iface) rep bd boundary.output sizes allowance laws
  have hf := laws.fst (rep.ty scalar) (rep.ty stateTy)
  dsimp only [finishSome, Code.descriptionSize]
  omega

omit [C.HasOption] in
theorem cutoff_description :
    (cutoff (iface := iface) rep data cost primitive).descriptionSize sizes ≤ primitiveSize .zero + 2 * allowance + 1 := by
  have h := laws.compose_bound (dataLaws.unit (StepClass.HasProd.prod rep.data.unit (rep.ty storeTy))) (hp .zero)
  dsimp only [cutoff, Code.descriptionSize]
  omega

variable [Q.HasOption] [OptionCode (Q := Q)] [QD : Q.IsDistributive]
  (dispatch : DispatchDescriptionLaws (Q := Q) sizes allowance)

include dispatch

theorem terminal_description (extractor : Code Q unifSpec iface (rep.ty Extraction.inputTy) (rep.ty Read.outputTy)) :
    (terminal rep bd boundary data cost primitive extractor).descriptionSize sizes ≤
      extractor.descriptionSize sizes + sizes.localSize boundary.output + sizes.localSize boundary.optional +
        primitiveSize .zero + 9 * allowance + 16 := by
  have hf := finishSome_description rep bd boundary sizes allowance laws extractor
  have hc := cutoff_description (iface := iface) rep data cost primitive sizes allowance laws dataLaws primitiveSize hp
  have hd := dispatch.distribute rep.data.unit bd.out (rep.ty storeTy)
  dsimp only [terminal, Code.descriptionSize]
  omega

variable [DecidableEq (SourceRequest F G₁ M)]
  (ports : Ports (Q := Q) rep bd)
  (randomPorts : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

theorem program_description (fuel : Nat) :
    (program rep bd boundary data cost primitive ports randomPorts sampler R fuel).descriptionSize sizes ≤
      sizes.localSize R.initCode + 2 * sizes.localSize R.headCode + sizes.localSize R.updateCode +
        4 * sampler.descriptionSize sizes + sizes.localSize randomPorts.request + sizes.localSize randomPorts.response +
        sizes.localSize ports.request + sizes.localSize ports.randomTag +
        sizes.localSize (ports.scalarTag false) + sizes.localSize (ports.scalarTag true) +
        sizes.localSize boundary.input + sizes.localSize boundary.output + sizes.localSize boundary.optional +
        3 * primitiveSize .messageEq + 3 * primitiveSize .point₁Eq + 7 * primitiveSize .add +
        14 * primitiveSize .zero + 2 * primitiveSize .one + 2 * primitiveSize .zero₁ + 2 * primitiveSize .scalarEq +
        2 * primitiveSize .natEq + 2 * primitiveSize .natSub + 2 * primitiveSize .natAdd + 4 * primitiveSize .mul +
        primitiveSize .neg + 2 * primitiveSize .scale₁ + primitiveSize .sub₁ + primitiveSize .sub + primitiveSize .div +
        fuel + 23000 * allowance + 512 := by
  have hs := setup_description (iface := iface) rep bd boundary data cost primitive sizes allowance laws dataLaws primitiveSize hp
  have hc := Handler.caller_description rep bd ports data cost primitive randomPorts sampler sizes allowance laws dispatch R fuel
  have hh := Handler.code_description rep bd ports data cost primitive randomPorts sampler sizes allowance laws dataLaws dispatch primitiveSize hp
  have he := Extraction.description rep data cost primitive sampler sizes allowance laws dataLaws primitiveSize hp dispatch
  have ht := terminal_description rep bd boundary data cost primitive sizes allowance laws dataLaws primitiveSize hp dispatch
    (Extraction.code rep data cost primitive sampler)
  dsimp only [program, Code.descriptionSize]
  omega

omit hp in
theorem program_description_uniform (fuel instructionSize randomPortSize handlerPortSize solverPortSize : Nat)
    (hinstr : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ instructionSize)
    (hrequest : sizes.localSize randomPorts.request ≤ randomPortSize)
    (hresponse : sizes.localSize randomPorts.response ≤ randomPortSize)
    (hhandler : sizes.localSize ports.request ≤ handlerPortSize ∧ sizes.localSize ports.randomTag ≤ handlerPortSize ∧
      sizes.localSize (ports.scalarTag false) ≤ handlerPortSize ∧ sizes.localSize (ports.scalarTag true) ≤ handlerPortSize)
    (hsolver : sizes.localSize boundary.input ≤ solverPortSize ∧ sizes.localSize boundary.output ≤ solverPortSize ∧
      sizes.localSize boundary.optional ≤ solverPortSize) :
    (program rep bd boundary data cost primitive ports randomPorts sampler R fuel).descriptionSize sizes ≤
      programDescription (sizes.localSize R.initCode + 2 * sizes.localSize R.headCode + sizes.localSize R.updateCode)
        (sampler.descriptionSize sizes) randomPortSize handlerPortSize solverPortSize fuel allowance instructionSize := by
  have h := program_description rep bd boundary data cost primitive sizes allowance laws dataLaws (fun _ => instructionSize)
    hinstr dispatch ports randomPorts sampler R fuel
  obtain ⟨hh1, hh2, hh3, hh4⟩ := hhandler
  obtain ⟨hs1, hs2, hs3⟩ := hsolver
  dsimp only [programDescription]
  omega

end Signatures.Runtime.SchnorrAGM.Native.Solver
