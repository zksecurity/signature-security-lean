import Proofs.Runtime.GeneralSyncWrapRuns
import Proofs.Runtime.GeneralSyncWrapDescription
import Proofs.Runtime.GeneralWeightedParameters
import Proofs.SynchronizedPS.WrappedSecurity

/-! # Parameters of the general synchronized PS reduction

One fixed backend, the attacker's own interface and allowances, executed correction, final-scalar
and key routines of the two weighted schemes at every known key, and the pipeline's components at
the wrapper's outer boundary. The four pipeline parameter records, two schemes with their known
key sampled, are derived: the wrapper's execution, code and query allowances are computed from the
attacker's. -/

open BilinearGroup
open OracleComp OracleSpec PFunctor AlgebraicGroupModel
open PFunctor.DynSystem PFunctor.DynSystem.DynComputation
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.WeightedAGM Signatures.Runtime.WeightedAGM.NativeHandler
open Signatures.Runtime.WeightedAGM.NativeSolver

namespace Signatures.Runtime.SyncWrapGeneral

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]

attribute [local implicit_reducible] PFunctor.Idx

/-- The inner ports read as ports of the wrapper's outer boundary, which shares the request and
reply encodings. -/
def outerPorts {randomBound : Nat} {rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M)}
    {bdI : Boundary C (generalSpec (key.Value (cryptoBase F G₁ G₂ K M))
      (Weights.syncMessage.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor (G₂ × G₂)
      (OutTy.Value (cryptoBase F G₁ G₂ K M))}
    (ports : NativePorts (Q := Q) rep key Weights.syncMessage bdI) :
    NativePorts (Q := Q) rep key Weights.syncMessage (outerBoundary rep (bdI := bdI)) where
  randomReply := ports.randomReply
  request := ports.request
  randomTag := ports.randomTag
  hashTag := ports.hashTag
  signTag := ports.signTag

/-- The inner request recovery read at the outer boundary. -/
def outerRecovery {randomBound : Nat} {rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M)}
    {bdI : Boundary C (generalSpec (key.Value (cryptoBase F G₁ G₂ K M))
      (Weights.syncMessage.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor (G₂ × G₂)
      (OutTy.Value (cryptoBase F G₁ G₂ K M))}
    (recovery : RequestRecovery (Q := Q) rep key Weights.syncMessage bdI) :
    RequestRecovery (Q := Q) rep key Weights.syncMessage (outerBoundary rep (bdI := bdI)) where
  recover := recovery.recover
  monotone := recovery.monotone
  request := recovery.request

/-- The wrapped attacker's allowance: its own randomness and signing requests, and one hash per
own hash, per signing request and for the final period. -/
def outerQueries (q : Model.QueryAllowance) : Model.QueryAllowance :=
  ⟨q.random, q.hash + q.sign + 1, q.sign⟩

/-- The wrapper's query budget: one per attacker query, per signing request and the final hash. -/
def wrapCap (q : Model.QueryAllowance) (execution : ExecutionCost) : Nat := execution.queries + q.sign + 1

/-- A fixed backend with the attacker's interface and allowances, both schemes' routines at every
known key, and the pipeline's components at the wrapper's boundary. -/
structure Parameters (generator : G₁) (keyGenerator : G₂) where
  generates : Function.Bijective (fun r : F => r • generator)
  pairingInjective : Function.Injective (fun c : F => c • (pairing (F := F) generator keyGenerator : Gₜ))
  innerQueries : Model.QueryAllowance
  innerExecution : ExecutionCost
  innerQueryCapacity : innerExecution.queries ≤ innerQueries.total
  innerCodeLimit : Nat
  randomBound : Nat
  iface : Interface (C := C) unifSpec
  rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M)
  bdI : Boundary C (generalSpec (key.Value (cryptoBase F G₁ G₂ K M))
    (Weights.syncMessage.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor (G₂ × G₂)
    (OutTy.Value (cryptoBase F G₁ G₂ K M))
  ports : NativePorts (Q := Q) rep key Weights.syncMessage bdI
  wports : WrapPorts rep ports
  scheme₁ : ∀ k : F, SchemeCode (Q := Q) rep (SynchronizedPS.Wrapped.correction₁ k) (SynchronizedPS.Wrapped.final₁ k) (fun pk => (pk, k • keyGenerator))
  scheme₂ : ∀ k : F, SchemeCode (Q := Q) rep (SynchronizedPS.Wrapped.correction₂ k) (SynchronizedPS.Wrapped.final₂ k) (fun pk => (k • keyGenerator, pk))
  sampler : BoundedSampler rep key Weights.syncMessage (outerBoundary rep (bdI := bdI)) (outerPorts ports) (iface := iface)
  boundary : ∀ b : Bool, DataPorts (Q := Q) rep (.sync b) (outerBoundary rep (bdI := bdI))
  data : DataCode Q rep.data
  cost : PrimitiveCosts
  primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr)
  sampling : MachineCompiler.SamplingImplementation Q iface rep
  control : ControlCosts
  queryCost : (i : Nat) → unifSpec.Range i → Nat
  header : Nat
  sizes : SizeLaws Q header
  lists : ListSizeLaws Q rep.data header
  lengths : ListLengthLaws Q rep.data
  overhead : Nat → Nat
  laws : LocalCostLaws Q overhead
  dataLaws : DataCostLaws rep.data data overhead
  primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr)
  mono : Monotone overhead
  routing : RoutingCostLaws control overhead
  dispatch : DispatchCostLaws (Q := Q) overhead
  optLaws : OptionCostLaws (Q := Q) overhead
  recovery : RequestRecovery (Q := Q) rep key Weights.syncMessage bdI
  backend : Backend.{v, w, x} Q unifSpec iface control queryCost
  descriptionSizes : DescriptionSize Q
  factor : Nat
  description : backend.DescriptionBound descriptionSizes factor
  allowance : Nat
  descriptionLaws : LocalDescriptionLaws descriptionSizes allowance
  descriptionData : DataDescriptionLaws descriptionSizes rep.data data allowance
  descriptionDispatch : DispatchDescriptionLaws (Q := Q) descriptionSizes allowance
  optDescriptions : OptionDescriptionLaws (Q := Q) descriptionSizes allowance
  inputWidth : Nat
  width : Nat
  wrapWidth : Nat
  outputWidth : Nat
  routeWidth : Nat
  keyWidth : Nat
  finishedRoute : Nat
  comparisonTime : Nat
  scalarTime : Nat
  opTime : Nat
  handlerAdapterTime : Nat
  solverAdapterTime : Nat
  dynamicTime : Nat
  handlerTickTime : Nat
  callerTickTime : Nat
  extractionTickTime : Nat
  routineTime : Nat
  headerWidth : header ≤ width
  wrapHeader : header ≤ wrapWidth
  inputCapacity : 9 * width ≤ inputWidth
  values : ∀ b : Bool, ValueCaps (Q := Q) rep (.sync b) width (outerQueries innerQueries).total
  wrapValues : ValueCaps (Q := Q) rep (.sync false) wrapWidth (wrapCap innerQueries innerExecution)
  ops : ∀ b : Bool, OperationCaps rep (.sync b) cost primitive primitiveBound (outerQueries innerQueries).total keyWidth
    opTime comparisonTime
  wrapKeyWidth : 8 * wrapWidth ≤ keyWidth
  handlerCaps : NativeHandler.PortCaps rep key Weights.syncMessage (outerBoundary rep (bdI := bdI)) (outerPorts ports) width
    handlerAdapterTime
  wrapHandlerCaps : NativeHandler.PortCaps rep key Weights.syncMessage bdI ports wrapWidth handlerAdapterTime
  wrapPortCaps : WrapPortCaps rep ports wports wrapWidth routeWidth outputWidth
    (finishedWidth wrapWidth (wrapCap innerQueries innerExecution) outputWidth) finishedRoute handlerAdapterTime
  scheme₁Caps : ∀ k : F, SchemeCaps (Q := Q) rep (SynchronizedPS.Wrapped.correction₁ k) (SynchronizedPS.Wrapped.final₁ k)
    (fun pk => (pk, k • keyGenerator)) (scheme₁ k) wrapWidth routineTime
  scheme₂Caps : ∀ k : F, SchemeCaps (Q := Q) rep (SynchronizedPS.Wrapped.correction₂ k) (SynchronizedPS.Wrapped.final₂ k)
    (fun pk => (k • keyGenerator, pk)) (scheme₂ k) wrapWidth routineTime
  outputKey : outputWidth ≤ wrapWidth
  headRoute : innerExecution.peakHeadSize ≤ routeWidth
  innerRequestWidth : recovery.recover innerExecution.peakHeadSize ≤ wrapWidth
  solverCaps : ∀ b : Bool, NativeSolver.PortCaps rep (.sync b) (outerBoundary rep (bdI := bdI)) (boundary b) width outputWidth
    routeWidth solverAdapterTime
  dynamicSamples : NativeHandler.DynamicSamplingCaps rep key Weights.syncMessage (outerBoundary rep (bdI := bdI))
    (outerPorts ports) sampler control queryCost width dynamicTime
  storeCapacity : ∀ b : Bool, handlerStoreWidth (.sync b) width (outerQueries innerQueries).total ≤ routeWidth
  goodHandlerComparison : ∀ b : Bool, Reply.goodSignEvaluationWidth (.sync b)
    (handlerStoreWidth (.sync b) width (outerQueries innerQueries).total)
    ((outerQueries innerQueries).total * ((Index.sync b).bound + 1)) ≤ keyWidth
  badHandlerComparison : ∀ b : Bool, 3 * Reply.badSignEvaluationWidth (.sync b)
    (handlerStoreWidth (.sync b) width (outerQueries innerQueries).total)
    ((outerQueries innerQueries).total * ((Index.sync b).bound + 1)) ≤ keyWidth
  extractionComparison : ∀ b : Bool, 3 * Extract.extractionWidth (.sync b)
    (extractionEntryWidth width (outerQueries innerQueries).total outputWidth)
    (outerQueries innerQueries).total (outerQueries innerQueries).total outputWidth
    ((outerQueries innerQueries).total * ((Index.sync b).bound + 1)) ≤ keyWidth
  wrapRequestWidth : recovery.recover (9 * wrapWidth + finishedRoute) ≤ width
  wrapStateCapacity : stateWidth wrapWidth (wrapCap innerQueries innerExecution) innerExecution.peakStateSize routeWidth ≤ routeWidth
  wrapHeadCapacity : 9 * wrapWidth + finishedRoute ≤ routeWidth
  sampleTime : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime
  callerTick : ∀ n ≤ (outerQueries innerQueries).total, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ callerTickTime
  goodHandlerTick : ∀ b : Bool, ∀ n ≤ (Index.sync b).bound + 1,
    ∀ encoded ≤ 7 * Reply.goodSignEvaluationWidth (.sync b) (handlerStoreWidth (.sync b) width (outerQueries innerQueries).total)
      ((outerQueries innerQueries).total * ((Index.sync b).bound + 1)), control.loop n encoded ≤ handlerTickTime
  badHandlerTick : ∀ b : Bool, ∀ n ≤ (Index.sync b).bound + 1,
    ∀ encoded ≤ 7 * Reply.badSignEvaluationWidth (.sync b) (handlerStoreWidth (.sync b) width (outerQueries innerQueries).total)
      ((outerQueries innerQueries).total * ((Index.sync b).bound + 1)), control.loop n encoded ≤ handlerTickTime
  extractionTick : ∀ b : Bool, ∀ n ≤ rowCap (.sync b) (outerQueries innerQueries).total,
    ∀ encoded ≤ 7 * Extract.extractionWidth (.sync b) (extractionEntryWidth width (outerQueries innerQueries).total outputWidth)
      (outerQueries innerQueries).total (outerQueries innerQueries).total outputWidth
      ((outerQueries innerQueries).total * ((Index.sync b).bound + 1)),
      control.loop n encoded ≤ extractionTickTime
  instructionSize : Nat
  handlerPortSize : Nat
  solverPortSize : Nat
  routineSize : Nat
  instructionDescriptions : ∀ {a b} (instr : CryptoOp a b), descriptionSizes.localSize (primitive instr) ≤ instructionSize
  handlerDescriptions : ∀ b : Bool, HandlerPortDescriptions rep (.sync b) (outerBoundary rep (bdI := bdI)) (outerPorts ports)
    descriptionSizes handlerPortSize
  wrapDescriptions : WrapPortDescriptions rep ports wports descriptionSizes handlerPortSize
  scheme₁Descriptions : ∀ k : F, SchemeDescriptions rep (SynchronizedPS.Wrapped.correction₁ k) (SynchronizedPS.Wrapped.final₁ k)
    (fun pk => (pk, k • keyGenerator)) (scheme₁ k) descriptionSizes routineSize
  scheme₂Descriptions : ∀ k : F, SchemeDescriptions rep (SynchronizedPS.Wrapped.correction₂ k) (SynchronizedPS.Wrapped.final₂ k)
    (fun pk => (k • keyGenerator, pk)) (scheme₂ k) descriptionSizes routineSize
  solverDescriptions : ∀ b : Bool, PortDescriptions rep (.sync b) (outerBoundary rep (bdI := bdI)) (boundary b) descriptionSizes
    solverPortSize

namespace Parameters

variable {generator : G₁} {keyGenerator : G₂}
  (P : Parameters (Q := Q) (F := F) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) (K := K) (M := M) generator keyGenerator)

/-- The wrapper's query budget. -/
abbrev cap : Nat := wrapCap P.innerQueries P.innerExecution

/-- The wrapped attacker's allowance. -/
abbrev queries : Model.QueryAllowance := outerQueries P.innerQueries

/-- The wrapper's execution budget. -/
def execution : ExecutionCost :=
  wrapExecution P.overhead P.wrapWidth P.cap P.innerExecution.peakStateSize P.routeWidth P.outputWidth P.finishedRoute
    P.handlerAdapterTime P.routineTime P.opTime P.comparisonTime P.innerExecution.work

/-- The wrapper's stored-code budget. -/
def callerCodeLimit : Nat :=
  wrapCodeLimit P.allowance P.handlerPortSize P.routineSize P.instructionSize P.innerCodeLimit

theorem cap_le_total : P.cap ≤ P.queries.total := by
  have := P.innerQueryCapacity
  unfold Model.QueryAllowance.total at *
  dsimp only [cap, wrapCap, queries, outerQueries] at *
  omega

/-- The pipeline parameters for one weighted scheme (`false`: `x•H(t)`, `true`: `y•(m•H(t))`). -/
def toGeneral (b : Bool) :
    General.Parameters (Q := Q) (F := F) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) (K := K) (M := M) (.sync b) where
  generator := generator
  keyGenerator := keyGenerator
  generates := P.generates
  pairingInjective := P.pairingInjective
  queries := P.queries
  execution := P.execution
  queryCapacity := P.cap_le_total
  callerCodeLimit := P.callerCodeLimit
  randomBound := P.randomBound
  iface := P.iface
  rep := P.rep
  bd := outerBoundary P.rep (bdI := P.bdI)
  ports := outerPorts P.ports
  sampler := P.sampler
  boundary := P.boundary b
  data := P.data
  cost := P.cost
  primitive := P.primitive
  sampling := P.sampling
  control := P.control
  queryCost := P.queryCost
  header := P.header
  sizes := P.sizes
  lists := P.lists
  lengths := P.lengths
  overhead := P.overhead
  laws := P.laws
  dataLaws := P.dataLaws
  primitiveBound := P.primitiveBound
  mono := P.mono
  routing := P.routing
  dispatch := P.dispatch
  recovery := outerRecovery P.recovery
  backend := P.backend
  descriptionSizes := P.descriptionSizes
  factor := P.factor
  description := P.description
  allowance := P.allowance
  descriptionLaws := P.descriptionLaws
  descriptionData := P.descriptionData
  descriptionDispatch := P.descriptionDispatch
  inputWidth := P.inputWidth
  width := P.width
  outputWidth := P.outputWidth
  routeWidth := P.routeWidth
  keyWidth := P.keyWidth
  comparisonTime := P.comparisonTime
  scalarTime := P.scalarTime
  opTime := P.opTime
  handlerAdapterTime := P.handlerAdapterTime
  solverAdapterTime := P.solverAdapterTime
  dynamicTime := P.dynamicTime
  handlerTickTime := P.handlerTickTime
  callerTickTime := P.callerTickTime
  extractionTickTime := P.extractionTickTime
  headerWidth := P.headerWidth
  inputCapacity := P.inputCapacity
  values := P.values b
  ops := P.ops b
  handlerCaps := P.handlerCaps
  solverCaps := P.solverCaps b
  dynamicSamples := P.dynamicSamples
  storeCapacity := P.storeCapacity b
  goodHandlerComparison := P.goodHandlerComparison b
  badHandlerComparison := P.badHandlerComparison b
  extractionComparison := P.extractionComparison b
  requestWidth := P.wrapRequestWidth
  stateWidth := P.wrapStateCapacity
  headWidth := P.wrapHeadCapacity
  sampleTime := P.sampleTime
  callerTick := P.callerTick
  goodHandlerTick := P.goodHandlerTick b
  badHandlerTick := P.badHandlerTick b
  extractionTick := P.extractionTick b
  instructionSize := P.instructionSize
  handlerPortSize := P.handlerPortSize
  solverPortSize := P.solverPortSize
  instructionDescriptions := P.instructionDescriptions
  handlerDescriptions := P.handlerDescriptions b
  solverDescriptions := P.solverDescriptions b

/-- The value and operation contracts of the finish, from the pipeline's. -/
theorem finishCaps : FinishCaps (header := P.header) P.rep P.cost P.primitive P.primitiveBound P.wrapWidth P.cap P.opTime := by
  have hcap := P.innerQueryCapacity
  refine ⟨P.wrapHeader, P.wrapValues.unit, P.wrapValues.bool, fun k hk => P.wrapValues.nat k ?_, P.wrapValues.scalar,
    fun k hk => (P.ops false).natEq k 0 ?_ ?_, fun k hk => (P.ops false).natSub k ?_,
    fun k hk => (P.ops false).natAdd k ?_, (P.ops false).zero, (P.ops false).mul, (P.ops false).neg⟩ <;>
  · dsimp only [rowCap, Index.bound, cap, queries, wrapCap, outerQueries, Model.QueryAllowance.total] at *
    omega

/-- The wrapper's cost contracts for one scheme's routines, at the pipeline's operation caps. -/
theorem caps (b : Bool) {correction finalFn : K × F → F} {keys : G₂ → G₂ × G₂}
    (code : SchemeCode (Q := Q) P.rep correction finalFn keys)
    (scaps : SchemeCaps (Q := Q) P.rep correction finalFn keys code P.wrapWidth P.routineTime) :
    Caps P.rep P.data P.cost P.primitive P.ports P.wports correction finalFn keys code P.primitiveBound P.overhead P.header
      P.wrapWidth P.cap P.innerExecution.peakStateSize P.innerExecution.peakHeadSize P.routeWidth P.outputWidth
      P.finishedRoute P.handlerAdapterTime P.routineTime P.opTime P.comparisonTime where
  laws := P.laws
  dispatch := P.dispatch
  optLaws := P.optLaws
  dataLaws := P.dataLaws
  mono := P.mono
  sizes := P.sizes
  lists := P.lists
  lens := P.lengths
  wcaps := P.wrapPortCaps
  pcaps := P.wrapHandlerCaps
  scaps := scaps
  fcaps := P.finishCaps
  point₁ := P.wrapValues.point₁
  point₂ := P.wrapValues.point₂
  outputKey := P.outputKey
  headRoute := P.headRoute
  keyEq x y hx hy := (P.ops b).keyEq x y (hx.trans P.wrapKeyWidth) (hy.trans P.wrapKeyWidth)
  scale₁ := (P.ops b).scale₁
  add₁ := (P.ops b).groupAdd

/-- The wrapper's description laws for one scheme's routines around an attacker caller. -/
theorem descriptions {correction finalFn : K × F → F} {keys : G₂ → G₂ × G₂}
    (code : SchemeCode (Q := Q) P.rep correction finalFn keys)
    (sdesc : SchemeDescriptions P.rep correction finalFn keys code P.descriptionSizes P.routineSize)
    (R : GeneralCaller.Caller (Q := Q) (bd := P.bdI)) :
    Descriptions (rep := P.rep) (data := P.data) (primitive := P.primitive) (ports := P.ports) (wports := P.wports)
      (code := code) (R := R) P.descriptionSizes P.allowance P.handlerPortSize P.routineSize P.instructionSize
      (P.descriptionSizes.localSize R.initCode) (P.descriptionSizes.localSize R.headCode)
      (P.descriptionSizes.localSize R.updateCode) where
  laws := P.descriptionLaws
  dataLaws := P.descriptionData
  dispatch := P.descriptionDispatch
  optLaws := P.optDescriptions
  wrapPorts := P.wrapDescriptions
  scheme := sdesc
  request := (P.handlerDescriptions false).request
  signTag := (P.handlerDescriptions false).signTag
  instructions := P.instructionDescriptions
  init := le_rfl
  head := le_rfl
  update := le_rfl

end Parameters

end Signatures.Runtime.SyncWrapGeneral
