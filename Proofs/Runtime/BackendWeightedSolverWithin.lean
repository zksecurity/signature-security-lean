import Proofs.Runtime.BackendWeightedSolverBudget
import Proofs.Runtime.BackendWeightedSolverDescription
import Proofs.Runtime.BackendWeightedSolverCorrectness

/-! Executable witnesses for both weighted lazy AGM reductions. Complete runtime
and stored-code bounds follow from primitive contracts and the general caller's
own measured resources. Exact source semantics retain the original weighted index
and message types; neither domain is required to be finite. -/

open OracleComp OracleSpec PFunctor Model.LazyAGM
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.WeightedAGM.NativeSolver

open BackendProgram NativeHandler Reply

universe v w x

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
  (recovery : NativeHandler.RequestRecovery (Q := Q) rep index.ty index.messageTy bd)

  (sourceProgram : G₂ → OracleComp (generalSpec (index.ty.Value (cryptoBase F G₁ G₂ K M))
    (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound)
    ((AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M)))
  (hprogram : R.machine.Implements sourceProgram)

  (backend : Backend.{v, w, x} Q unifSpec iface control queryCost)
  (descriptionSizes : DescriptionSize Q) (factor : Nat)
  (description : backend.DescriptionBound descriptionSizes factor)
  (allowance : Nat) (descriptionLaws : LocalDescriptionLaws descriptionSizes allowance)
  (descriptionData : DataDescriptionLaws descriptionSizes rep.data data allowance)
  (descriptionDispatch : DispatchDescriptionLaws (Q := Q) descriptionSizes allowance)

include sizes lists lengths laws dataLaws primitiveBound mono routing dispatch hrun recovery hprogram
  descriptionLaws descriptionData descriptionDispatch

attribute [local implicit_reducible] PFunctor.Idx

theorem goodProgram_within
    (inputWidth width outputWidth routeWidth cap fuel keyWidth comparisonTime scalarTime opTime
      handlerAdapterTime solverAdapterTime dynamicTime handlerTickTime callerTickTime extractionTickTime : Nat)
    (hh : header ≤ width) (hcap : fuel ≤ cap) (hfuel : bound.queries ≤ fuel)
    (values : ValueCaps (Q := Q) rep index width cap)
    (ops : OperationCaps rep index cost primitive primitiveBound cap keyWidth opTime comparisonTime)
    (handlerCaps : NativeHandler.PortCaps rep index.ty index.messageTy bd ports width handlerAdapterTime)
    (solverCaps : PortCaps rep index bd boundary width outputWidth routeWidth solverAdapterTime)
    (dynamicSamples : NativeHandler.DynamicSamplingCaps rep index.ty index.messageTy bd ports sampler control queryCost width dynamicTime)
    (hroute : handlerStoreWidth index width cap ≤ routeWidth)
    (hhandlerComparison : Reply.goodSignEvaluationWidth index (handlerStoreWidth index width cap) (cap * (index.bound + 1)) ≤ keyWidth)
    (hcomparison : 3 * Extract.extractionWidth index (extractionEntryWidth width cap outputWidth) cap cap outputWidth (cap * (index.bound + 1)) ≤ keyWidth)
    (hrequest : recovery.recover bound.peakHeadSize ≤ width)
    (hstate : bound.peakStateSize ≤ routeWidth) (hhead : bound.peakHeadSize ≤ routeWidth)
    (hsample : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hcallerTick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ callerTickTime)
    (hhandlerTick : ∀ n ≤ index.bound + 1, ∀ encoded ≤ 7 * Reply.goodSignEvaluationWidth index
      (handlerStoreWidth index width cap) (cap * (index.bound + 1)), control.loop n encoded ≤ handlerTickTime)
    (hextractionTick : ∀ n ≤ rowCap index cap,
      ∀ encoded ≤ 7 * Extract.extractionWidth index (extractionEntryWidth width cap outputWidth) cap cap outputWidth (cap * (index.bound + 1)),
      control.loop n encoded ≤ extractionTickTime)
    (adv : Adversary F (index.ty.Value (cryptoBase F G₁ G₂ K M))
      (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ G₂)
    (hsource : ∀ pk, AGM.outputView <$> simulateQ (generalSource randomBound) (sourceProgram pk) = adv.main pk)
    (instructionSize handlerPortSize solverPortSize : Nat)
    (instructionDescriptions : ∀ {a b} (instr : CryptoOp a b),
      descriptionSizes.localSize (primitive instr) ≤ instructionSize)
    (handlerDescriptions : HandlerPortDescriptions rep index bd ports descriptionSizes handlerPortSize)
    (solverDescriptions : PortDescriptions rep index bd boundary descriptionSizes solverPortSize) :
    Within backend descriptionSizes factor description (rep.env inputTypes) (rep.ty scalar) inputWidth
      (factor * programDescription index.bound
        (descriptionSizes.localSize R.initCode + 2 * descriptionSizes.localSize R.headCode +
          descriptionSizes.localSize R.updateCode)
        (sampling.scalar.descriptionSize descriptionSizes) (sampler.code.descriptionSize descriptionSizes)
        fuel allowance instructionSize handlerPortSize solverPortSize)
      (goodProgramTime index overhead bound inputWidth width outputWidth routeWidth cap fuel comparisonTime
        scalarTime opTime handlerAdapterTime solverAdapterTime dynamicTime handlerTickTime callerTickTime extractionTickTime)
      (fun input => Model.LazyAGM.WeightedReduction.goodReductionList (index.sourceTerms cost)
        adv input.1 input.2.1 input.2.2.1 input.2.2.2.1) := by
  have he : ∀ input,
      (goodProgram rep index bd ports sampler boundary data cost primitive sampling R fuel).denote input =
        Model.LazyAGM.WeightedReduction.goodReductionList (index.sourceTerms cost)
          adv input.1 input.2.1 input.2.2.1 input.2.2.2.1 := by
    rintro ⟨g, X, g₂, pk, u⟩
    cases u
    exact goodProgram_source_of_resources rep index bd ports sampler boundary data cost primitive sampling R
      fuel sourceProgram adv hsource bound hrun hfuel hprogram g X g₂ pk
  have hb : Bounds control queryCost
      (goodProgram rep index bd ports sampler boundary data cost primitive sampling R fuel)
      (fun input => Q.size (rep.env inputTypes) input ≤ inputWidth) (fun _ => True)
      (goodProgramTime index overhead bound inputWidth width outputWidth routeWidth cap fuel comparisonTime
        scalarTime opTime handlerAdapterTime solverAdapterTime dynamicTime handlerTickTime callerTickTime extractionTickTime) := by
    rintro ⟨g, X, g₂, pk, u⟩ hi z hz
    cases u
    have ht := goodProgram_bound rep index bd ports sampler boundary data cost primitive sampling control queryCost
      sizes lists lengths laws dataLaws primitiveBound mono routing dispatch R bound hrun recovery sourceProgram hprogram
      inputWidth width outputWidth routeWidth cap fuel keyWidth comparisonTime scalarTime opTime
      handlerAdapterTime solverAdapterTime dynamicTime handlerTickTime callerTickTime extractionTickTime
      hh hcap hfuel values ops handlerCaps solverCaps dynamicSamples hroute hhandlerComparison hcomparison
      hrequest hstate hhead hsample hcallerTick hhandlerTick hextractionTick g X g₂ pk hi (g, X, g₂, pk, ()) rfl z hz
    exact ⟨trivial, ht.2⟩
  have h := within_compile backend descriptionSizes factor description
    (goodProgram rep index bd ports sampler boundary data cost primitive sampling R fuel) inputWidth _ _ he hb
  have hd := goodProgram_description rep index bd ports sampler boundary data cost primitive sampling
    descriptionSizes allowance descriptionLaws descriptionData descriptionDispatch R
    fuel instructionSize handlerPortSize solverPortSize instructionDescriptions handlerDescriptions solverDescriptions
  exact Within.mono backend descriptionSizes factor description h (Nat.mul_le_mul_left factor hd) le_rfl

theorem badProgram_within
    (inputWidth width outputWidth routeWidth cap fuel keyWidth comparisonTime scalarTime opTime
      handlerAdapterTime solverAdapterTime dynamicTime handlerTickTime callerTickTime extractionTickTime : Nat)
    (hh : header ≤ width) (hcap : fuel ≤ cap) (hfuel : bound.queries ≤ fuel)
    (values : ValueCaps (Q := Q) rep index width cap)
    (ops : OperationCaps rep index cost primitive primitiveBound cap keyWidth opTime comparisonTime)
    (handlerCaps : NativeHandler.PortCaps rep index.ty index.messageTy bd ports width handlerAdapterTime)
    (solverCaps : PortCaps rep index bd boundary width outputWidth routeWidth solverAdapterTime)
    (dynamicSamples : NativeHandler.DynamicSamplingCaps rep index.ty index.messageTy bd ports sampler control queryCost width dynamicTime)
    (hroute : handlerStoreWidth index width cap ≤ routeWidth)
    (hhandlerComparison : 3 * Reply.badSignEvaluationWidth index (handlerStoreWidth index width cap) (cap * (index.bound + 1)) ≤ keyWidth)
    (hcomparison : 3 * Extract.extractionWidth index (extractionEntryWidth width cap outputWidth) cap cap outputWidth (cap * (index.bound + 1)) ≤ keyWidth)
    (hrequest : recovery.recover bound.peakHeadSize ≤ width)
    (hstate : bound.peakStateSize ≤ routeWidth) (hhead : bound.peakHeadSize ≤ routeWidth)
    (hsample : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hcallerTick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ callerTickTime)
    (hhandlerTick : ∀ n ≤ index.bound + 1, ∀ encoded ≤ 7 * Reply.badSignEvaluationWidth index
      (handlerStoreWidth index width cap) (cap * (index.bound + 1)), control.loop n encoded ≤ handlerTickTime)
    (hextractionTick : ∀ n ≤ rowCap index cap,
      ∀ encoded ≤ 7 * Extract.extractionWidth index (extractionEntryWidth width cap outputWidth) cap cap outputWidth (cap * (index.bound + 1)),
      control.loop n encoded ≤ extractionTickTime)
    (adv : Adversary F (index.ty.Value (cryptoBase F G₁ G₂ K M))
      (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ G₂)
    (hsource : ∀ pk, AGM.outputView <$> simulateQ (generalSource randomBound) (sourceProgram pk) = adv.main pk)
    (instructionSize handlerPortSize solverPortSize : Nat)
    (instructionDescriptions : ∀ {a b} (instr : CryptoOp a b),
      descriptionSizes.localSize (primitive instr) ≤ instructionSize)
    (handlerDescriptions : HandlerPortDescriptions rep index bd ports descriptionSizes handlerPortSize)
    (solverDescriptions : PortDescriptions rep index bd boundary descriptionSizes solverPortSize) :
    Within backend descriptionSizes factor description (rep.env inputTypes) (rep.ty scalar) inputWidth
      (factor * programDescription index.bound
        (descriptionSizes.localSize R.initCode + 2 * descriptionSizes.localSize R.headCode +
          descriptionSizes.localSize R.updateCode)
        (sampling.scalar.descriptionSize descriptionSizes) (sampler.code.descriptionSize descriptionSizes)
        fuel allowance instructionSize handlerPortSize solverPortSize)
      (badProgramTime index overhead bound inputWidth width outputWidth routeWidth cap fuel comparisonTime
        scalarTime opTime handlerAdapterTime solverAdapterTime dynamicTime handlerTickTime callerTickTime extractionTickTime)
      (fun input => Model.LazyAGM.WeightedReduction.badReductionList (index.sourceTerms cost)
        adv input.1 input.2.1 input.2.2.1 input.2.2.2.1) := by
  have he : ∀ input,
      (badProgram rep index bd ports sampler boundary data cost primitive sampling R fuel).denote input =
        Model.LazyAGM.WeightedReduction.badReductionList (index.sourceTerms cost)
          adv input.1 input.2.1 input.2.2.1 input.2.2.2.1 := by
    rintro ⟨g, X, g₂, pk, u⟩
    cases u
    exact badProgram_source_of_resources rep index bd ports sampler boundary data cost primitive sampling R
      fuel sourceProgram adv hsource bound hrun hfuel hprogram g X g₂ pk
  have hb : Bounds control queryCost
      (badProgram rep index bd ports sampler boundary data cost primitive sampling R fuel)
      (fun input => Q.size (rep.env inputTypes) input ≤ inputWidth) (fun _ => True)
      (badProgramTime index overhead bound inputWidth width outputWidth routeWidth cap fuel comparisonTime
        scalarTime opTime handlerAdapterTime solverAdapterTime dynamicTime handlerTickTime callerTickTime extractionTickTime) := by
    rintro ⟨g, X, g₂, pk, u⟩ hi z hz
    cases u
    have ht := badProgram_bound rep index bd ports sampler boundary data cost primitive sampling control queryCost
      sizes lists lengths laws dataLaws primitiveBound mono routing dispatch R bound hrun recovery sourceProgram hprogram
      inputWidth width outputWidth routeWidth cap fuel keyWidth comparisonTime scalarTime opTime
      handlerAdapterTime solverAdapterTime dynamicTime handlerTickTime callerTickTime extractionTickTime
      hh hcap hfuel values ops handlerCaps solverCaps dynamicSamples hroute hhandlerComparison hcomparison
      hrequest hstate hhead hsample hcallerTick hhandlerTick hextractionTick g X g₂ pk hi (g, X, g₂, pk, ()) rfl z hz
    exact ⟨trivial, ht.2⟩
  have h := within_compile backend descriptionSizes factor description
    (badProgram rep index bd ports sampler boundary data cost primitive sampling R fuel) inputWidth _ _ he hb
  have hd := badProgram_description rep index bd ports sampler boundary data cost primitive sampling
    descriptionSizes allowance descriptionLaws descriptionData descriptionDispatch R
    fuel instructionSize handlerPortSize solverPortSize instructionDescriptions handlerDescriptions solverDescriptions
  exact Within.mono backend descriptionSizes factor description h (Nat.mul_le_mul_left factor hd) le_rfl

end Signatures.Runtime.WeightedAGM.NativeSolver
