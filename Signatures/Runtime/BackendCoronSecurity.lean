import Signatures.Runtime.BackendCoronSolverResources
import Signatures.Runtime.BackendCoCDH
import Signatures.BLS.CoCDH.Proofs.ArbitraryMessages

/-! Concrete BLS security from a general realized attacker. The solver resource
certificate is constructed from measured caller resources and primitive backend
contracts, then supplied to hardness in that same backend. The exact probability
transport now allows arbitrary message types. No conventional-machine adequacy
theorem is asserted. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Coron.NativeSolver

open BackendProgram ReplyCompiler AlgebraicGroupModel

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ M : Type} [Field F] [SampleableType F] [Fintype F]
  [SampleableType G₁] [Fintype G₁]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]
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

theorem security_of_resources
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
    (solverDescriptions : PortDescriptions rep bd boundary descriptionSizes solverPortSize)
    (g : G₁) (g₂ : G₂)
    (hgen : Function.Bijective (fun r : F => r • g))
    (hinj : Function.Injective (fun z : G₁ => pairing (F := F) (Gₜ := Gₜ) z g₂))
    (hqs : ∀ r : F, IsQueryBoundP (adv (r • g₂)) (fun i => Sum.isRight i = true) qS)
    (hchallenge : ∀ r : F, ∀ h : G₁,
      Q.size (rep.env inputTypes) (g, g₂, r • g, r • g₂, h, ()) ≤ inputWidth)
    (codeBudget timeBudget : Nat) (epsilon : ENNReal)
    (hcode : factor * (descriptionSizes.localSize R.initCode + 2 * descriptionSizes.localSize R.headCode +
        descriptionSizes.localSize R.updateCode + fuel + 3 * samplingCode.scalar.descriptionSize descriptionSizes +
        3 * (samplingCode.uniform qS).descriptionSize descriptionSizes + sampler.code.descriptionSize descriptionSizes +
        4000 * allowance + 40 * instructionSize + 4 * handlerPortSize + 3 * solverPortSize + 500) ≤ codeBudget)
    (htime : nativeSolverTime overhead inputWidth width routeWidth cap fuel (bound.work + 2 * bound.queries + 2)
        tickTime (fun _ => bound.queries) comparisonTime scalarTime coinTime opTime
        handlerAdapterTime solverAdapterTime dynamicTime ≤ timeBudget)
    (hardness : Model.HardWithin (Model.coCDHAdvantage (F := F) g g₂)
      (coCDHWithin rep backend descriptionSizes factor description g g₂ inputWidth codeBudget) timeBudget epsilon) :
    𝒟[BLS.CoCDH.Tight.blsEufLazyPK (F := F) (Gₜ := Gₜ) g g₂ adv] {true} ≤
      Model.coronFactor qS * epsilon := by
  have certificate := program_within_of_resources rep bd ports sampler boundary data samplingCode cost primitive
    control queryCost sizes lists mono routing localLaws dispatchLaws dataLaws primitiveBound R
    backend descriptionSizes factor description allowance descriptionLaws descriptionData descriptionDispatch
    qS inputWidth messageWidth width scalarWidth coinWidth groupWidth cap routeWidth fuel tickTime
    comparisonTime scalarTime coinTime opTime handlerAdapterTime solverAdapterTime dynamicTime hh hm hroute hcap
    hf hc hg hw handlerCaps solverCaps dynamicSamples values ops samples bound hrun recovery hdecoded hstate hhead
    hfuel htick sourceProgram hprogram adv hsource instructionSize handlerPortSize solverPortSize
    instructionDescriptions handlerDescriptions solverDescriptions
  have hsolver := hardness (BLS.CoCDH.coronReductionLazyPK (F := F) qS (BLS.CoCDH.Tight.cacheForgeryPK adv))
    ⟨hchallenge, Within.mono backend descriptionSizes factor description certificate hcode htime⟩
  refine (BLS.CoCDH.Proofs.security_arbitrary_messages g g₂ qS adv hgen hinj hqs).trans ?_
  gcongr

end Signatures.Runtime.Coron.NativeSolver
