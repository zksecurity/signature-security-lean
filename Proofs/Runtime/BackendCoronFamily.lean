import Proofs.Runtime.BackendCoronSolverResources
import Proofs.Runtime.BackendCoronPolynomial
import Proofs.Runtime.BackendFamily

/-! Nonuniform BLS solver families from general caller and primitive contracts.
Scalar/group/message types and their encodings may vary with the security
parameter. The computational backend and its description measure stay fixed.
No completed-solver runtime or polynomiality premise is supplied. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Coron.NativeSolver.Family

open BackendProgram ReplyCompiler

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ M : Nat → Type}
  [∀ n, Field (F n)] [∀ n, SampleableType (F n)]
  [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G₁ n)] [∀ n, DecidableEq (G₂ n)]
  [∀ n, AddCommGroup (G₁ n)] [∀ n, Module (F n) (G₁ n)]
  [∀ n, AddCommGroup (G₂ n)] [∀ n, Module (F n) (G₂ n)] [∀ n, DecidableEq (M n)]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat → Nat}
  (rep : ∀ n, LanguageRepresentation C (cryptoBase (F n) (G₁ n) (G₂ n) (M n) (M n)))
  (bd : ∀ n, Boundary C (generalSpec (M n) (G₁ n) (randomBound n)).toPFunctor (G₂ n) (M n × G₁ n))
  (ports : ∀ n, NativePorts (Q := Q) (rep n) (bd n))
  (sampler : ∀ n, BoundedSampler (rep n) (bd n) (ports n) (iface := iface))
  (boundary : ∀ n, DataPorts (Q := Q) (rep n) (bd n))
  (data : ∀ n, DataCode Q (rep n).data)
  (samplingCode : ∀ n, MachineCompiler.SamplingImplementation Q iface (rep n))
  (cost : Nat → PrimitiveCosts)
  (primitive : ∀ n, {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer ((rep n).ty a) ((rep n).ty b) ((arithmetic (F n) (G₁ n) (G₂ n) (M n) (M n) (cost n)).execute instr))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  {header : Nat → Nat} (sizes : ∀ n, SizeLaws Q (header n))
  (lists : ∀ n, ListSizeLaws Q (rep n).data (header n))
  {overhead : Nat → Nat} (mono : Monotone overhead) (routing : RoutingCostLaws control overhead)
  (localLaws : LocalCostLaws Q overhead) (dispatchLaws : DispatchCostLaws (Q := Q) overhead)
  (dataLaws : ∀ n, DataCostLaws (rep n).data (data n) overhead)
  (primitiveBound : ∀ n, {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive n instr))
  (R : ∀ n, GeneralCaller.Caller (Q := Q) (bd := bd n))
  (backend : Backend.{v, w, x} Q unifSpec iface control queryCost)
  (descriptionSizes : DescriptionSize Q) (factor : Nat)
  (description : backend.DescriptionBound descriptionSizes factor)
  (allowance : Nat → Nat) (descriptionLaws : ∀ n, LocalDescriptionLaws descriptionSizes (allowance n))
  (descriptionData : ∀ n, DataDescriptionLaws descriptionSizes (rep n).data (data n) (allowance n))
  (descriptionDispatch : ∀ n, DispatchDescriptionLaws (Q := Q) descriptionSizes (allowance n))
  (qS inputWidth messageWidth width scalarWidth coinWidth groupWidth cap routeWidth fuel tickTime : Nat → Nat)
  (comparisonTime scalarTime coinTime opTime handlerAdapterTime solverAdapterTime dynamicTime : Nat → Nat)
  (bound : Nat → ExecutionCost)
  (instructionSize handlerPortSize solverPortSize : Nat → Nat)
  (adv : ∀ n, BLS.ROM.AdversaryPK (M n) (G₁ n) (G₂ n))

def codeBudget (n : Nat) : Nat :=
  factor * (descriptionSizes.localSize (R n).initCode + 2 * descriptionSizes.localSize (R n).headCode +
    descriptionSizes.localSize (R n).updateCode + fuel n +
    3 * (samplingCode n).scalar.descriptionSize descriptionSizes +
    3 * ((samplingCode n).uniform (qS n)).descriptionSize descriptionSizes +
    (sampler n).code.descriptionSize descriptionSizes + 4000 * allowance n + 40 * instructionSize n +
    4 * handlerPortSize n + 3 * solverPortSize n + 500)

def timeBudget (n : Nat) : Nat :=
  nativeSolverTime overhead (inputWidth n) (width n) (routeWidth n) (cap n) (fuel n)
    ((bound n).work + 2 * (bound n).queries + 2) (tickTime n) (fun _ => (bound n).queries)
    (comparisonTime n) (scalarTime n) (coinTime n) (opTime n) (handlerAdapterTime n)
    (solverAdapterTime n) (dynamicTime n)

noncomputable def algorithm (n : Nat) (input : Env (cryptoBase (F n) (G₁ n) (G₂ n) (M n) (M n)) inputTypes) :
    ProbComp (G₁ n) :=
  BLS.CoCDH.coronReductionLazyPK (F := F n) (qS n) (BLS.ROM.cacheForgeryPK (adv n))
    input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2.1

variable
  (hh : ∀ n, header n ≤ width n) (hm : ∀ n, messageWidth n ≤ width n)
  (hroute : ∀ n, 8 * width n ≤ routeWidth n) (hcap : ∀ n, fuel n ≤ cap n)
  (hf : ∀ n (y : F n), Q.size ((rep n).ty scalar) y ≤ scalarWidth n)
  (hc : ∀ n (y : Fin (qS n + 1)), Q.size ((rep n).ty (boundedNat (qS n))) y ≤ coinWidth n)
  (hg : ∀ n (y : G₁ n), Q.size ((rep n).ty point₁) y ≤ groupWidth n)
  (hw : ∀ n, storeWidth (header n) (messageWidth n) (scalarWidth n) (coinWidth n) (groupWidth n) (cap n) ≤ width n)
  (handlerCaps : ∀ n, NativeHandler.PortCaps (rep n) (bd n) (ports n) (width n) (handlerAdapterTime n))
  (solverCaps : ∀ n, PortCaps (rep n) (bd n) (boundary n) (inputWidth n) (routeWidth n) (solverAdapterTime n))
  (dynamicSamples : ∀ n, NativeHandler.DynamicSamplingCaps (rep n) (bd n) (ports n) (sampler n)
    control queryCost (width n) (dynamicTime n))
  (values : ∀ n, NativeValueCaps (Q := Q) (rep n) (qS n) (width n))
  (ops : ∀ n, NativeInstructionCaps (rep n) (cost n) (primitive n) (primitiveBound n)
    (qS n) (width n) (comparisonTime n) (opTime n))
  (samples : ∀ n, NativeSamplingCaps (rep n) (samplingCode n) control queryCost (qS n) (scalarTime n) (coinTime n))
  (hrun : ∀ n, (R n).RunsWithin (fun _ => bound n))
  (recovery : ∀ n, BoundaryRecovery (Q := Q) (rep n) (bd n))
  (hdecoded : ∀ n, (recovery n).recover (bound n).peakHeadSize ≤ messageWidth n)
  (hstate : ∀ n, (bound n).peakStateSize ≤ routeWidth n)
  (hhead : ∀ n, (bound n).peakHeadSize ≤ routeWidth n)
  (hfuel : ∀ n, (bound n).queries ≤ fuel n)
  (htick : ∀ n k, k ≤ fuel n → ∀ encoded ≤ 3 * routeWidth n, control.loop k encoded ≤ tickTime n)
  (sourceProgram : ∀ n, G₂ n → OracleComp (generalSpec (M n) (G₁ n) (randomBound n)) (M n × G₁ n))
  (hprogram : ∀ n, (R n).machine.Implements (sourceProgram n))
  (hsource : ∀ n pk, simulateQ (generalSource (randomBound n)) (sourceProgram n pk) = adv n pk)
  (instructionDescriptions : ∀ n, NativeInstructionDescriptions (rep n) (cost n) (primitive n)
    descriptionSizes (qS n) (instructionSize n))
  (handlerDescriptions : ∀ n, NativeHandler.PortDescriptions (rep n) (bd n) (ports n) descriptionSizes (handlerPortSize n))
  (solverDescriptions : ∀ n, PortDescriptions (rep n) (bd n) (boundary n) descriptionSizes (solverPortSize n))

include sizes lists mono routing localLaws dispatchLaws dataLaws descriptionLaws descriptionData descriptionDispatch
  hh hm hroute hcap hf hc hg hw handlerCaps solverCaps dynamicSamples values ops samples hrun hdecoded hstate hhead
  hfuel htick hprogram hsource instructionDescriptions handlerDescriptions solverDescriptions

theorem within_at (n : Nat) :
    Within backend descriptionSizes factor description ((rep n).env inputTypes) ((rep n).ty point₁) (inputWidth n)
      (codeBudget rep bd ports sampler samplingCode R descriptionSizes factor allowance qS fuel
        instructionSize handlerPortSize solverPortSize n)
      (timeBudget inputWidth width cap routeWidth fuel tickTime comparisonTime scalarTime coinTime opTime
        handlerAdapterTime solverAdapterTime dynamicTime bound (overhead := overhead) n)
      (algorithm qS adv n) := by
  exact program_within_of_resources (rep n) (bd n) (ports n) (sampler n) (boundary n) (data n) (samplingCode n)
    (cost n) (primitive n) control queryCost (sizes n) (lists n) mono routing localLaws dispatchLaws (dataLaws n)
    (primitiveBound n) (R n) backend descriptionSizes factor description (allowance n) (descriptionLaws n)
    (descriptionData n) (descriptionDispatch n) (qS n) (inputWidth n) (messageWidth n) (width n) (scalarWidth n)
    (coinWidth n) (groupWidth n) (cap n) (routeWidth n) (fuel n) (tickTime n) (comparisonTime n) (scalarTime n)
    (coinTime n) (opTime n) (handlerAdapterTime n) (solverAdapterTime n) (dynamicTime n)
    (hh n) (hm n) (hroute n) (hcap n) (hf n) (hc n) (hg n) (hw n) (handlerCaps n) (solverCaps n)
    (dynamicSamples n) (values n) (ops n) (samples n) (bound n) (hrun n) (recovery n) (hdecoded n)
    (hstate n) (hhead n) (hfuel n) (htick n) (sourceProgram n) (hprogram n) (adv n) (hsource n)
    (instructionSize n) (handlerPortSize n) (solverPortSize n)
    (instructionDescriptions n) (handlerDescriptions n) (solverDescriptions n)

theorem nonuniform_within
    (hOverhead : PolynomialOverhead (fun _ => overhead))
    (hInput : PolynomiallyBounded inputWidth) (hWidth : PolynomiallyBounded width)
    (hRoute : PolynomiallyBounded routeWidth) (hCap : PolynomiallyBounded cap)
    (hFuel : PolynomiallyBounded fuel) (hWork : PolynomiallyBounded (fun n => (bound n).work))
    (hQueries : PolynomiallyBounded (fun n => (bound n).queries)) (hTick : PolynomiallyBounded tickTime)
    (hCompare : PolynomiallyBounded comparisonTime) (hScalar : PolynomiallyBounded scalarTime)
    (hCoin : PolynomiallyBounded coinTime) (hOp : PolynomiallyBounded opTime)
    (hHandler : PolynomiallyBounded handlerAdapterTime) (hSolver : PolynomiallyBounded solverAdapterTime)
    (hDynamic : PolynomiallyBounded dynamicTime)
    (hInitCode : PolynomiallyBounded (fun n => descriptionSizes.localSize (R n).initCode))
    (hHeadCode : PolynomiallyBounded (fun n => descriptionSizes.localSize (R n).headCode))
    (hUpdateCode : PolynomiallyBounded (fun n => descriptionSizes.localSize (R n).updateCode))
    (hScalarCode : PolynomiallyBounded (fun n => (samplingCode n).scalar.descriptionSize descriptionSizes))
    (hCoinCode : PolynomiallyBounded (fun n => ((samplingCode n).uniform (qS n)).descriptionSize descriptionSizes))
    (hDynamicCode : PolynomiallyBounded (fun n => (sampler n).code.descriptionSize descriptionSizes))
    (hStructuralCode : PolynomiallyBounded allowance) (hInstructionCode : PolynomiallyBounded instructionSize)
    (hHandlerCode : PolynomiallyBounded handlerPortSize) (hSolverCode : PolynomiallyBounded solverPortSize) :
    NonuniformWithin backend descriptionSizes factor description
      (fun n => (rep n).env inputTypes) (fun n => (rep n).ty point₁) inputWidth (algorithm qS adv) := by
  have hcode := description_polynomial (fun _ => factor)
    (fun n => descriptionSizes.localSize (R n).initCode) (fun n => descriptionSizes.localSize (R n).headCode)
    (fun n => descriptionSizes.localSize (R n).updateCode) fuel
    (fun n => (samplingCode n).scalar.descriptionSize descriptionSizes)
    (fun n => ((samplingCode n).uniform (qS n)).descriptionSize descriptionSizes)
    (fun n => (sampler n).code.descriptionSize descriptionSizes) allowance instructionSize handlerPortSize solverPortSize
    (PolynomiallyBounded.const factor) hInitCode hHeadCode hUpdateCode hFuel hScalarCode hCoinCode hDynamicCode
    hStructuralCode hInstructionCode hHandlerCode hSolverCode
  have hlocal := (hWork.add ((PolynomiallyBounded.const 2).mul hQueries)).add (PolynomiallyBounded.const 2)
  have htime := nativeSolverTime_polynomial (fun _ => overhead) inputWidth width routeWidth cap fuel
    (fun n => (bound n).work + 2 * (bound n).queries + 2) tickTime (fun _ n => (bound n).queries)
    comparisonTime scalarTime coinTime opTime handlerAdapterTime solverAdapterTime dynamicTime
    hOverhead hInput hWidth hRoute hCap hFuel hlocal hTick (fun _ => hQueries) hCompare hScalar hCoin hOp hHandler hSolver hDynamic
  refine NonuniformWithin.of_pointwise backend descriptionSizes factor description _ _ inputWidth _ _ _ hInput hcode htime ?_
  intro n
  exact within_at rep bd ports sampler boundary data samplingCode cost primitive control queryCost sizes lists mono routing
    localLaws dispatchLaws dataLaws primitiveBound R backend descriptionSizes factor description allowance descriptionLaws
    descriptionData descriptionDispatch qS inputWidth messageWidth width scalarWidth coinWidth groupWidth cap routeWidth
    fuel tickTime comparisonTime scalarTime coinTime opTime handlerAdapterTime solverAdapterTime dynamicTime bound
    instructionSize handlerPortSize solverPortSize adv hh hm hroute hcap hf hc hg hw handlerCaps solverCaps dynamicSamples
    values ops samples hrun recovery hdecoded hstate hhead hfuel htick sourceProgram hprogram hsource
    instructionDescriptions handlerDescriptions solverDescriptions n

end Signatures.Runtime.Coron.NativeSolver.Family
