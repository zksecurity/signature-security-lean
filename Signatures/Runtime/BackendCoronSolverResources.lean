import Signatures.Runtime.BackendCoronCallerResources

/-! General-attacker instantiation of the native solver certificate. An upstream
quantitative resource bound supplies caller reachability, sizes, local/query
budgets, and termination. A representation recovery law supplies decoded message
sizes. No attacker-specific invariant or completed-reduction budget is assumed. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Coron.NativeSolver

open BackendProgram ReplyCompiler

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
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂ (M × G₁))
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (mono : Monotone overhead) (routing : RoutingCostLaws control overhead)
  (localLaws : LocalCostLaws Q overhead) (dispatchLaws : DispatchCostLaws (Q := Q) overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (backend : Backend.{v, w, x} Q unifSpec iface control queryCost)
  (descriptionSizes : DescriptionSize Q) (factor : Nat)
  (description : backend.DescriptionBound descriptionSizes factor)
  (allowance : Nat) (descriptionLaws : LocalDescriptionLaws descriptionSizes allowance)
  (descriptionData : DataDescriptionLaws descriptionSizes rep.data data allowance)
  (descriptionDispatch : DispatchDescriptionLaws (Q := Q) descriptionSizes allowance)

include sizes lists mono routing localLaws dispatchLaws dataLaws
  descriptionLaws descriptionData descriptionDispatch

set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] PFunctor.Idx

theorem program_within_of_resources
    (qS inputWidth messageWidth width scalarWidth coinWidth groupWidth cap routeWidth fuel tickTime : Nat)
    (comparisonTime scalarTime coinTime opTime handlerAdapterTime solverAdapterTime dynamicTime : Nat)
    (hh : header ≤ width) (hm : messageWidth ≤ width) (hroute : 8 * width ≤ routeWidth) (hcap : fuel ≤ cap)
    (hf : ∀ y : F, Q.size (rep.ty scalar) y ≤ scalarWidth)
    (hc : ∀ y : Fin (qS + 1), Q.size (rep.ty (boundedNat qS)) y ≤ coinWidth)
    (hg : ∀ y : G₁, Q.size (rep.ty point₁) y ≤ groupWidth)
    (hw : storeWidth header messageWidth scalarWidth coinWidth groupWidth cap ≤ width)
    (handlerCaps : NativeHandler.PortCaps rep bd ports width handlerAdapterTime)
    (solverCaps : PortCaps rep bd boundary inputWidth routeWidth solverAdapterTime)
    (dynamicSamples : NativeHandler.DynamicSamplingCaps rep bd ports sampler control queryCost width dynamicTime)
    (values : NativeValueCaps (Q := Q) rep qS width)
    (ops : NativeInstructionCaps rep cost primitive primitiveBound qS width comparisonTime opTime)
    (samples : NativeSamplingCaps rep samplingCode control queryCost qS scalarTime coinTime)
    (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
    (recovery : BoundaryRecovery (Q := Q) rep bd)
    (hdecoded : recovery.recover bound.peakHeadSize ≤ messageWidth)
    (hstate : bound.peakStateSize ≤ routeWidth) (hhead : bound.peakHeadSize ≤ routeWidth)
    (hfuel : bound.queries ≤ fuel)
    (htick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ tickTime)
    (sourceProgram : G₂ → OracleComp (generalSpec M G₁ randomBound) (M × G₁))
    (hprogram : R.machine.Implements sourceProgram)
    (adv : BLS.CoCDH.Tight.TightAdvPK M G₁ G₂)
    (hsource : ∀ pk, simulateQ (generalSource randomBound) (sourceProgram pk) = adv pk)
    (instructionSize handlerPortSize solverPortSize : Nat)
    (instructionDescriptions : NativeInstructionDescriptions rep cost primitive descriptionSizes qS instructionSize)
    (handlerDescriptions : NativeHandler.PortDescriptions rep bd ports descriptionSizes handlerPortSize)
    (solverDescriptions : PortDescriptions rep bd boundary descriptionSizes solverPortSize) :
    Within backend descriptionSizes factor description (rep.env inputTypes) (rep.ty point₁) inputWidth
      (factor * (descriptionSizes.localSize R.initCode + 2 * descriptionSizes.localSize R.headCode +
        descriptionSizes.localSize R.updateCode + fuel + 3 * samplingCode.scalar.descriptionSize descriptionSizes +
        3 * (samplingCode.uniform qS).descriptionSize descriptionSizes + sampler.code.descriptionSize descriptionSizes +
        4000 * allowance + 40 * instructionSize + 4 * handlerPortSize + 3 * solverPortSize + 500))
      (nativeSolverTime overhead inputWidth width routeWidth cap fuel (bound.work + 2 * bound.queries + 2) tickTime (fun _ => bound.queries)
        comparisonTime scalarTime coinTime opTime handlerAdapterTime solverAdapterTime dynamicTime)
      (fun input => BLS.CoCDH.coronReductionLazyPK (F := F) qS (BLS.CoCDH.Tight.cacheForgeryPK adv)
        input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2.1) := by
  apply program_within rep bd ports sampler boundary data samplingCode cost primitive control queryCost
    sizes lists mono routing localLaws dispatchLaws dataLaws primitiveBound R backend descriptionSizes factor
    description allowance descriptionLaws descriptionData descriptionDispatch
    qS inputWidth messageWidth width scalarWidth coinWidth groupWidth cap routeWidth fuel
    (bound.work + 2 * bound.queries + 2) tickTime (fun _ => bound.queries)
    comparisonTime scalarTime coinTime opTime handlerAdapterTime solverAdapterTime dynamicTime
    hh hm hroute hcap hf hc hg hw handlerCaps solverCaps dynamicSamples values ops samples
    (fun _ => GeneralCaller.Reachable R)
    (fun _ state hs i next hv => resource_step rep bd sizes R recovery bound hrun messageWidth width hm hdecoded
      state hs i next hv)
    (fun _ state hs =>
      let widths := GeneralCaller.reachable_sizes R bound hrun state hs
      ⟨widths.1.trans hstate, widths.2.trans hhead⟩)
    (fun _ state hs out hv => (reachable_message rep bd sizes R recovery bound hrun state hs out hv).trans hdecoded)
    htick
    (fun pk _ => ⟨GeneralCaller.reachable_init R pk,
      GeneralCaller.budget_of_resources R bound hrun (generalReplies M G₁ randomBound) generalKind fuel pk⟩)
    sourceProgram (GeneralCaller.implementsWithin_of_resources R bound hrun sourceProgram hprogram fuel hfuel)
    adv hsource instructionSize handlerPortSize solverPortSize instructionDescriptions handlerDescriptions solverDescriptions

end Signatures.Runtime.Coron.NativeSolver
