import Signatures.Runtime.BackendLazyAGMSolverBudget
import Signatures.Runtime.BackendLazyAGMSolverDescription
import Signatures.Runtime.BackendLazyAGMSolverCorrectness

/-! Executable witnesses for both named lazy AGM DLog solvers in a fixed
backend. Their complete runtime and stored-code bounds are derived from primitive
contracts and the general attacker's own resources, with exact source semantics
at every input. No arithmetic-language implementation of the attacker is needed. -/

open OracleComp OracleSpec PFunctor Model.LazyAGM
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.LazyAGM.NativeSolver

open BackendProgram Coron NativeHandler

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂
    ((AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M)))
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (lengths : ListLengthLaws Q rep.data)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead) (routing : RoutingCostLaws control overhead)
  (dispatch : DispatchCostLaws (Q := Q) overhead)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
  (recovery : SignatureHandler.RequestRecovery (Q := Q) rep bd)

  (backend : Backend.{v, w, x} Q unifSpec iface control queryCost)
  (descriptionSizes : DescriptionSize Q) (factor : Nat)
  (description : backend.DescriptionBound descriptionSizes factor)
  (allowance : Nat) (descriptionLaws : LocalDescriptionLaws descriptionSizes allowance)
  (descriptionData : DataDescriptionLaws descriptionSizes rep.data data allowance)
  (descriptionDispatch : DispatchDescriptionLaws (Q := Q) descriptionSizes allowance)

include sizes lists lengths laws dataLaws primitiveBound mono routing dispatch hrun recovery
  descriptionLaws descriptionData descriptionDispatch

set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] PFunctor.Idx
theorem goodProgram_within
    (inputWidth width outputWidth routeWidth cap fuel messageWidth comparisonTime scalarTime opTime
      handlerAdapterTime solverAdapterTime dynamicTime callerTickTime extractionTickTime : Nat)
    (hh : header ≤ width) (hcap : fuel ≤ cap)
    (values : ValueCaps (Q := Q) rep width cap)
    (ops : OperationCaps rep cost primitive primitiveBound cap messageWidth opTime comparisonTime)
    (handlerCaps : SignatureHandler.PortCaps rep bd ports width handlerAdapterTime)
    (solverCaps : PortCaps rep bd boundary width outputWidth routeWidth solverAdapterTime)
    (dynamicSamples : SignatureHandler.DynamicSamplingCaps rep bd ports sampler control queryCost width dynamicTime)
    (hroute : handlerStoreWidth width cap ≤ routeWidth)
    (hhandlerComparison : 5 * handlerStoreWidth width cap ≤ messageWidth)
    (hcomparison : 3 * extractionWidth (terminalInputWidth width outputWidth cap) cap outputWidth cap ≤ messageWidth)
    (hrequest : recovery.recover bound.peakHeadSize ≤ width)
    (hstate : bound.peakStateSize ≤ routeWidth) (hhead : bound.peakHeadSize ≤ routeWidth)
    (hsample : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hcallerTick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ callerTickTime)
    (hextractionTick : ∀ n ≤ cap,
      ∀ encoded ≤ 7 * extractionWidth (terminalInputWidth width outputWidth cap) cap outputWidth cap,
      control.loop n encoded ≤ extractionTickTime)

    (hfuel : bound.queries ≤ fuel)
    (sourceProgram : G₂ → OracleComp (generalSpec M G₁ randomBound)
      ((AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M)))
    (hprogram : R.machine.Implements sourceProgram)
    (adv : Adversary F M M G₁ G₂)
    (hsource : ∀ pk, AGM.outputView <$> simulateQ (generalSource randomBound) (sourceProgram pk) = adv.main pk)
    (instructionSize handlerPortSize solverPortSize : Nat)
    (instructionDescriptions : ∀ {a b} (instr : CryptoOp a b),
      descriptionSizes.localSize (primitive instr) ≤ instructionSize)
    (handlerDescriptions : HandlerPortDescriptions rep bd ports descriptionSizes handlerPortSize)
    (solverDescriptions : PortDescriptions rep bd boundary descriptionSizes solverPortSize) :
    Within backend descriptionSizes factor description (rep.env inputTypes) (rep.ty scalar) inputWidth
      (factor * programDescription
        (descriptionSizes.localSize R.initCode + 2 * descriptionSizes.localSize R.headCode +
          descriptionSizes.localSize R.updateCode)
        (sampling.scalar.descriptionSize descriptionSizes) (sampler.code.descriptionSize descriptionSizes)
        fuel allowance instructionSize handlerPortSize solverPortSize)
      (goodProgramTime overhead bound inputWidth width outputWidth routeWidth cap fuel comparisonTime
        scalarTime opTime handlerAdapterTime solverAdapterTime dynamicTime callerTickTime extractionTickTime)
      (fun input => BLS.LazyAGM.Reduction.goodReductionList adv input.1 input.2.1 input.2.2.1 input.2.2.2.1) := by
  have he : ∀ input,
      (goodProgram rep bd ports sampler boundary data cost primitive sampling R fuel).denote input =
        BLS.LazyAGM.Reduction.goodReductionList adv input.1 input.2.1 input.2.2.1 input.2.2.2.1 := by
    rintro ⟨g, X, g₂, pk, u⟩
    cases u
    exact goodProgram_source_of_resources rep bd ports sampler boundary data cost primitive sampling R
      fuel sourceProgram adv hsource bound hrun hfuel hprogram g X g₂ pk
  have hb : Bounds control queryCost
      (goodProgram rep bd ports sampler boundary data cost primitive sampling R fuel)
      (fun input => Q.size (rep.env inputTypes) input ≤ inputWidth) (fun _ => True)
      (goodProgramTime overhead bound inputWidth width outputWidth routeWidth cap fuel comparisonTime
        scalarTime opTime handlerAdapterTime solverAdapterTime dynamicTime callerTickTime extractionTickTime) := by
    rintro ⟨g, X, g₂, pk, u⟩ hi z hz
    cases u
    have ht := goodProgram_bound rep bd ports sampler boundary data cost primitive sampling control queryCost
      sizes lists lengths laws dataLaws primitiveBound mono routing dispatch R bound hrun recovery
      inputWidth width outputWidth routeWidth cap fuel messageWidth comparisonTime scalarTime opTime
      handlerAdapterTime solverAdapterTime dynamicTime callerTickTime extractionTickTime
      hh hcap values ops handlerCaps solverCaps dynamicSamples hroute hhandlerComparison hcomparison
      hrequest hstate hhead hsample hcallerTick hextractionTick g X g₂ pk hi (g, X, g₂, pk, ()) rfl z hz
    exact ⟨trivial, ht.2⟩
  have h := within_compile backend descriptionSizes factor description
    (goodProgram rep bd ports sampler boundary data cost primitive sampling R fuel) inputWidth _ _ he hb
  have hd := goodProgram_description rep bd ports sampler boundary data cost primitive sampling
    descriptionSizes allowance descriptionLaws descriptionData descriptionDispatch R
    fuel instructionSize handlerPortSize solverPortSize instructionDescriptions handlerDescriptions solverDescriptions
  exact Within.mono backend descriptionSizes factor description h (Nat.mul_le_mul_left factor hd) le_rfl

theorem badProgram_within
    (inputWidth width outputWidth routeWidth cap fuel messageWidth comparisonTime scalarTime opTime
      handlerAdapterTime solverAdapterTime dynamicTime callerTickTime extractionTickTime : Nat)
    (hh : header ≤ width) (hcap : fuel ≤ cap)
    (values : ValueCaps (Q := Q) rep width cap)
    (ops : OperationCaps rep cost primitive primitiveBound cap messageWidth opTime comparisonTime)
    (handlerCaps : SignatureHandler.PortCaps rep bd ports width handlerAdapterTime)
    (solverCaps : PortCaps rep bd boundary width outputWidth routeWidth solverAdapterTime)
    (dynamicSamples : SignatureHandler.DynamicSamplingCaps rep bd ports sampler control queryCost width dynamicTime)
    (hroute : handlerStoreWidth width cap ≤ routeWidth)
    (hhandlerComparison : 15 * handlerStoreWidth width cap ≤ messageWidth)
    (hcomparison : 3 * extractionWidth (terminalInputWidth width outputWidth cap) cap outputWidth cap ≤ messageWidth)
    (hrequest : recovery.recover bound.peakHeadSize ≤ width)
    (hstate : bound.peakStateSize ≤ routeWidth) (hhead : bound.peakHeadSize ≤ routeWidth)
    (hsample : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hcallerTick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ callerTickTime)
    (hextractionTick : ∀ n ≤ cap,
      ∀ encoded ≤ 7 * extractionWidth (terminalInputWidth width outputWidth cap) cap outputWidth cap,
      control.loop n encoded ≤ extractionTickTime)

    (hfuel : bound.queries ≤ fuel)
    (sourceProgram : G₂ → OracleComp (generalSpec M G₁ randomBound)
      ((AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M)))
    (hprogram : R.machine.Implements sourceProgram)
    (adv : Adversary F M M G₁ G₂)
    (hsource : ∀ pk, AGM.outputView <$> simulateQ (generalSource randomBound) (sourceProgram pk) = adv.main pk)
    (instructionSize handlerPortSize solverPortSize : Nat)
    (instructionDescriptions : ∀ {a b} (instr : CryptoOp a b),
      descriptionSizes.localSize (primitive instr) ≤ instructionSize)
    (handlerDescriptions : HandlerPortDescriptions rep bd ports descriptionSizes handlerPortSize)
    (solverDescriptions : PortDescriptions rep bd boundary descriptionSizes solverPortSize) :
    Within backend descriptionSizes factor description (rep.env inputTypes) (rep.ty scalar) inputWidth
      (factor * programDescription
        (descriptionSizes.localSize R.initCode + 2 * descriptionSizes.localSize R.headCode +
          descriptionSizes.localSize R.updateCode)
        (sampling.scalar.descriptionSize descriptionSizes) (sampler.code.descriptionSize descriptionSizes)
        fuel allowance instructionSize handlerPortSize solverPortSize)
      (badProgramTime overhead bound inputWidth width outputWidth routeWidth cap fuel comparisonTime
        scalarTime opTime handlerAdapterTime solverAdapterTime dynamicTime callerTickTime extractionTickTime)
      (fun input => BLS.LazyAGM.Reduction.badReductionList adv input.1 input.2.1 input.2.2.1 input.2.2.2.1) := by
  have he : ∀ input,
      (badProgram rep bd ports sampler boundary data cost primitive sampling R fuel).denote input =
        BLS.LazyAGM.Reduction.badReductionList adv input.1 input.2.1 input.2.2.1 input.2.2.2.1 := by
    rintro ⟨g, X, g₂, pk, u⟩
    cases u
    exact badProgram_source_of_resources rep bd ports sampler boundary data cost primitive sampling R
      fuel sourceProgram adv hsource bound hrun hfuel hprogram g X g₂ pk
  have hb : Bounds control queryCost
      (badProgram rep bd ports sampler boundary data cost primitive sampling R fuel)
      (fun input => Q.size (rep.env inputTypes) input ≤ inputWidth) (fun _ => True)
      (badProgramTime overhead bound inputWidth width outputWidth routeWidth cap fuel comparisonTime
        scalarTime opTime handlerAdapterTime solverAdapterTime dynamicTime callerTickTime extractionTickTime) := by
    rintro ⟨g, X, g₂, pk, u⟩ hi z hz
    cases u
    have ht := badProgram_bound rep bd ports sampler boundary data cost primitive sampling control queryCost
      sizes lists lengths laws dataLaws primitiveBound mono routing dispatch R bound hrun recovery
      inputWidth width outputWidth routeWidth cap fuel messageWidth comparisonTime scalarTime opTime
      handlerAdapterTime solverAdapterTime dynamicTime callerTickTime extractionTickTime
      hh hcap values ops handlerCaps solverCaps dynamicSamples hroute hhandlerComparison hcomparison
      hrequest hstate hhead hsample hcallerTick hextractionTick g X g₂ pk hi (g, X, g₂, pk, ()) rfl z hz
    exact ⟨trivial, ht.2⟩
  have h := within_compile backend descriptionSizes factor description
    (badProgram rep bd ports sampler boundary data cost primitive sampling R fuel) inputWidth _ _ he hb
  have hd := badProgram_description rep bd ports sampler boundary data cost primitive sampling
    descriptionSizes allowance descriptionLaws descriptionData descriptionDispatch R
    fuel instructionSize handlerPortSize solverPortSize instructionDescriptions handlerDescriptions solverDescriptions
  exact Within.mono backend descriptionSizes factor description h (Nat.mul_le_mul_left factor hd) le_rfl

end Signatures.Runtime.LazyAGM.NativeSolver
