import Proofs.Runtime.BackendCoronFamily
import Proofs.Runtime.BackendCoCDHFamily
import Proofs.Model.CoronLoss
import Proofs.BLS.CoCDH.ArbitraryMessages

/-! Asymptotic BLS security from general caller resources. Actual compiled solver
families have polynomial time and polynomial stored code/advice by the derived
native budgets. Message types may be infinite: the probability proof uses an
exact finite-domain transport, with no message-universe enumeration at runtime.
This is conditional on a fixed quantitative backend and its primitive contracts;
it does not claim a conventional-machine adequacy theorem. -/

open BilinearGroup

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Coron.NativeSolver.Family

open BackendProgram ReplyCompiler AlgebraicGroupModel

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ M : Nat → Type}
  [∀ n, Field (F n)] [∀ n, SampleableType (F n)]
  [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G₁ n)] [∀ n, DecidableEq (G₂ n)]
  [∀ n, AddCommGroup (G₁ n)] [∀ n, Module (F n) (G₁ n)]
  [∀ n, AddCommGroup (G₂ n)] [∀ n, Module (F n) (G₂ n)] [∀ n, DecidableEq (M n)]
  [∀ n, Fintype (F n)]
  [∀ n, SampleableType (G₁ n)] [∀ n, Fintype (G₁ n)]
  [∀ n, AddCommGroup (Gₜ n)] [∀ n, Module (F n) (Gₜ n)]
  [∀ n, BilinearPairing (F n) (G₁ n) (G₂ n) (Gₜ n)] [∀ n, DecidableEq (Gₜ n)]
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

theorem security_of_resources
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
    (hHandlerCode : PolynomiallyBounded handlerPortSize) (hSolverCode : PolynomiallyBounded solverPortSize)
    (hSigning : PolynomiallyBounded qS) (g : ∀ n, G₁ n) (g₂ : ∀ n, G₂ n)
    (hgen : ∀ n, Function.Bijective (fun r : F n => r • g n))
    (hinj : ∀ n, Function.Injective (fun z : G₁ n => pairing (F := F n) (Gₜ := Gₜ n) z (g₂ n)))
    (hqs : ∀ n (r : F n), IsQueryBoundP (adv n (r • g₂ n)) (fun i => Sum.isRight i = true) (qS n))
    (hchallenge : ∀ n (r : F n) (h : G₁ n),
      Q.size ((rep n).env inputTypes) (g n, g₂ n, r • g n, r • g₂ n, h, ()) ≤ inputWidth n)
    (hardness : coCDHNonuniformHardness rep backend descriptionSizes factor description g g₂ inputWidth) :
    negligible (fun n => 𝒟[BLS.CoCDH.Tight.blsEufLazyPK (F := F n) (Gₜ := Gₜ n) (g n) (g₂ n) (adv n)] {true}) := by
  have certificate := nonuniform_within rep bd ports sampler boundary data samplingCode cost primitive control queryCost sizes lists mono routing
    localLaws dispatchLaws dataLaws primitiveBound R backend descriptionSizes factor description allowance descriptionLaws
    descriptionData descriptionDispatch qS inputWidth messageWidth width scalarWidth coinWidth groupWidth cap routeWidth
    fuel tickTime comparisonTime scalarTime coinTime opTime handlerAdapterTime solverAdapterTime dynamicTime bound
    instructionSize handlerPortSize solverPortSize adv hh hm hroute hcap hf hc hg hw handlerCaps solverCaps dynamicSamples
    values ops samples hrun recovery hdecoded hstate hhead hfuel htick sourceProgram hprogram hsource
    instructionDescriptions handlerDescriptions solverDescriptions
    hOverhead hInput hWidth hRoute hCap hFuel hWork hQueries hTick hCompare hScalar hCoin hOp
    hHandler hSolver hDynamic hInitCode hHeadCode hUpdateCode hScalarCode hCoinCode hDynamicCode
    hStructuralCode hInstructionCode hHandlerCode hSolverCode
  have hsolver := hardness (algorithm qS adv) ⟨hchallenge, certificate⟩
  apply Model.negligible_of_coron_bound hSigning hsolver
  intro n
  exact BLS.CoCDH.Proofs.security_arbitrary_messages (g n) (g₂ n) (qS n) (adv n) (hgen n) (hinj n) (hqs n)

end Signatures.Runtime.Coron.NativeSolver.Family
