import Signatures.Runtime.BackendLazyAGMDLog
import Signatures.BLS.Proofs.LazyAGMArbitraryMessages

/-! Concrete BLS AGM security from general attacker code in a fixed backend.
Both complete solver resource witnesses are constructed, then supplied to DLog
hardness in that same implementation class. The message type is arbitrary;
algebraicity is expressed by the source game, independently of local code. -/

open OracleComp OracleSpec PFunctor Model.LazyAGM AlgebraicGroupModel
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.LazyAGM.NativeSolver

open BackendProgram Coron NativeHandler

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ M : Type} [Field F] [SampleableType F] [Fintype F]
  [SampleableType G₁] [Fintype G₁]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  [AddCommGroup Gₜ] [Module F Gₜ] [AlgebraicGroupModel.BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]
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

theorem security_of_resources
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
    (solverDescriptions : PortDescriptions rep bd boundary descriptionSizes solverPortSize)
    (g : G₁) (g₂ : G₂)
    (hgen : Function.Bijective (fun r : F => r • g))
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g g₂ : Gₜ)))
    (hchallenge : ∀ x : F, Q.size (rep.env inputTypes) (g, x • g, g₂, x • g₂, ()) ≤ inputWidth)
    (codeBudget goodTimeBudget badTimeBudget : Nat) (goodEpsilon badEpsilon : ENNReal)
    (hcode : factor * programDescription
        (descriptionSizes.localSize R.initCode + 2 * descriptionSizes.localSize R.headCode +
          descriptionSizes.localSize R.updateCode)
        (sampling.scalar.descriptionSize descriptionSizes) (sampler.code.descriptionSize descriptionSizes)
        fuel allowance instructionSize handlerPortSize solverPortSize ≤ codeBudget)
    (hgoodTime : goodProgramTime overhead bound inputWidth width outputWidth routeWidth cap fuel comparisonTime
        scalarTime opTime handlerAdapterTime solverAdapterTime dynamicTime callerTickTime extractionTickTime ≤ goodTimeBudget)
    (hbadTime : badProgramTime overhead bound inputWidth width outputWidth routeWidth cap fuel comparisonTime
        scalarTime opTime handlerAdapterTime solverAdapterTime dynamicTime callerTickTime extractionTickTime ≤ badTimeBudget)
    (goodHardness : Model.HardWithin (Model.dlog11Advantage (F := F) g g₂)
      (dlogWithin rep backend descriptionSizes factor description g g₂ inputWidth codeBudget) goodTimeBudget goodEpsilon)
    (badHardness : Model.HardWithin (Model.dlog11Advantage (F := F) g g₂)
      (dlogWithin rep backend descriptionSizes factor description g g₂ inputWidth codeBudget) badTimeBudget badEpsilon) :
    𝒟[BLS.LazyAGM.game (Gₜ := Gₜ) g g₂ adv] {true} ≤
      goodEpsilon + badEpsilon + 1 / (Fintype.card F : ENNReal) := by
  have goodCertificate := goodProgram_within rep bd ports sampler boundary data cost primitive sampling
    control queryCost sizes lists lengths laws dataLaws primitiveBound mono routing dispatch R bound hrun recovery
    backend descriptionSizes factor description allowance descriptionLaws descriptionData descriptionDispatch
    inputWidth width outputWidth routeWidth cap fuel messageWidth comparisonTime scalarTime opTime
    handlerAdapterTime solverAdapterTime dynamicTime callerTickTime extractionTickTime
    hh hcap values ops handlerCaps solverCaps dynamicSamples hroute (by omega) hcomparison
    hrequest hstate hhead hsample hcallerTick hextractionTick hfuel sourceProgram hprogram adv hsource
    instructionSize handlerPortSize solverPortSize instructionDescriptions handlerDescriptions solverDescriptions
  have hgood := goodHardness (BLS.LazyAGM.Reduction.goodReductionList adv)
    ⟨hchallenge, Within.mono backend descriptionSizes factor description goodCertificate hcode hgoodTime⟩
  have badCertificate := badProgram_within rep bd ports sampler boundary data cost primitive sampling
    control queryCost sizes lists lengths laws dataLaws primitiveBound mono routing dispatch R bound hrun recovery
    backend descriptionSizes factor description allowance descriptionLaws descriptionData descriptionDispatch
    inputWidth width outputWidth routeWidth cap fuel messageWidth comparisonTime scalarTime opTime
    handlerAdapterTime solverAdapterTime dynamicTime callerTickTime extractionTickTime
    hh hcap values ops handlerCaps solverCaps dynamicSamples hroute hhandlerComparison hcomparison
    hrequest hstate hhead hsample hcallerTick hextractionTick hfuel sourceProgram hprogram adv hsource
    instructionSize handlerPortSize solverPortSize instructionDescriptions handlerDescriptions solverDescriptions
  have hbad := badHardness (BLS.LazyAGM.Reduction.badReductionList adv)
    ⟨hchallenge, Within.mono backend descriptionSizes factor description badCertificate hcode hbadTime⟩
  exact (BLS.LazyAGM.Reduction.security_arbitrary_messages_list g g₂ adv hgen hpair).trans
    (add_le_add (add_le_add hgood hbad) le_rfl)

end Signatures.Runtime.LazyAGM.NativeSolver
