import Signatures.Runtime.BackendWeightedDLog
import Signatures.Model.AdvantageBound

/-! Shared concrete resource contracts for weighted AGM signatures. The degree
or dimension is explicit. Parameters fix encodings, native implementations and
primitive prices before choosing a general attacker. The attacker supplies only
its own measured execution, code and query bounds and exact source realization.
The complete reduction budgets are derived, not assumed. -/

open BilinearGroup

open OracleComp OracleSpec PFunctor AlgebraicGroupModel
open PFunctor.DynSystem.DynComputation
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.WeightedAGM Signatures.Runtime.WeightedAGM.NativeHandler
open Signatures.Runtime.WeightedAGM.NativeSolver

namespace Signatures.Runtime.WeightedAGM.General

structure QueryAllowance where
  random : Nat
  hash : Nat
  sign : Nat

def QueryAllowance.total (q : QueryAllowance) : Nat := q.random + q.hash + q.sign

def queryKind {I N : Type} : (Nat ⊕ I) ⊕ N → Fin 3
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => 2

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq Gₜ] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]

/-- A fixed curve/backend and concrete allowances for a class of attackers.
All cost assumptions below concern implemented primitives or encodings. -/
structure Parameters (index : Index) where
  generator : G₁
  keyGenerator : G₂
  generates : Function.Bijective (fun r : F => r • generator)
  pairingInjective : Function.Injective (fun c : F => c • (pairing (F := F) generator keyGenerator : Gₜ))
  queries : QueryAllowance
  execution : ExecutionCost
  queryCapacity : execution.queries ≤ queries.total
  callerCodeLimit : Nat
  randomBound : Nat
  iface : Interface (C := C) unifSpec
  rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M)
  bd : Boundary C (generalSpec (index.ty.Value (cryptoBase F G₁ G₂ K M))
    (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor G₂
    ((AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M))
  ports : NativePorts (Q := Q) rep index.ty index.messageTy bd
  sampler : BoundedSampler rep index.ty index.messageTy bd ports (iface := iface)
  boundary : DataPorts (Q := Q) rep index bd
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
  recovery : NativeHandler.RequestRecovery (Q := Q) rep index.ty index.messageTy bd
  backend : Backend.{v, w, x} Q unifSpec iface control queryCost
  descriptionSizes : DescriptionSize Q
  factor : Nat
  description : backend.DescriptionBound descriptionSizes factor
  allowance : Nat
  descriptionLaws : LocalDescriptionLaws descriptionSizes allowance
  descriptionData : DataDescriptionLaws descriptionSizes rep.data data allowance
  descriptionDispatch : DispatchDescriptionLaws (Q := Q) descriptionSizes allowance
  inputWidth : Nat
  width : Nat
  outputWidth : Nat
  routeWidth : Nat
  keyWidth : Nat
  comparisonTime : Nat
  scalarTime : Nat
  opTime : Nat
  handlerAdapterTime : Nat
  solverAdapterTime : Nat
  dynamicTime : Nat
  handlerTickTime : Nat
  callerTickTime : Nat
  extractionTickTime : Nat
  headerWidth : header ≤ width
  inputCapacity : 9 * width ≤ inputWidth
  values : ValueCaps (Q := Q) rep index width queries.total
  ops : OperationCaps rep index cost primitive primitiveBound queries.total keyWidth opTime comparisonTime
  handlerCaps : NativeHandler.PortCaps rep index.ty index.messageTy bd ports width handlerAdapterTime
  solverCaps : PortCaps rep index bd boundary width outputWidth routeWidth solverAdapterTime
  dynamicSamples : NativeHandler.DynamicSamplingCaps rep index.ty index.messageTy bd ports sampler control queryCost width dynamicTime
  storeCapacity : handlerStoreWidth index width queries.total ≤ routeWidth
  goodHandlerComparison : Reply.goodSignEvaluationWidth index (handlerStoreWidth index width queries.total)
    (queries.total * (index.bound + 1)) ≤ keyWidth
  badHandlerComparison : 3 * Reply.badSignEvaluationWidth index (handlerStoreWidth index width queries.total)
    (queries.total * (index.bound + 1)) ≤ keyWidth
  extractionComparison : 3 * Extract.extractionWidth index (extractionEntryWidth width queries.total outputWidth)
    queries.total queries.total outputWidth (queries.total * (index.bound + 1)) ≤ keyWidth
  requestWidth : recovery.recover execution.peakHeadSize ≤ width
  stateWidth : execution.peakStateSize ≤ routeWidth
  headWidth : execution.peakHeadSize ≤ routeWidth
  sampleTime : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime
  callerTick : ∀ n ≤ queries.total, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ callerTickTime
  goodHandlerTick : ∀ n ≤ index.bound + 1,
    ∀ encoded ≤ 7 * Reply.goodSignEvaluationWidth index (handlerStoreWidth index width queries.total)
      (queries.total * (index.bound + 1)), control.loop n encoded ≤ handlerTickTime
  badHandlerTick : ∀ n ≤ index.bound + 1,
    ∀ encoded ≤ 7 * Reply.badSignEvaluationWidth index (handlerStoreWidth index width queries.total)
      (queries.total * (index.bound + 1)), control.loop n encoded ≤ handlerTickTime
  extractionTick : ∀ n ≤ rowCap index queries.total,
    ∀ encoded ≤ 7 * Extract.extractionWidth index (extractionEntryWidth width queries.total outputWidth)
      queries.total queries.total outputWidth (queries.total * (index.bound + 1)),
      control.loop n encoded ≤ extractionTickTime
  instructionSize : Nat
  handlerPortSize : Nat
  solverPortSize : Nat
  instructionDescriptions : ∀ {a b} (instr : CryptoOp a b), descriptionSizes.localSize (primitive instr) ≤ instructionSize
  handlerDescriptions : HandlerPortDescriptions rep index bd ports descriptionSizes handlerPortSize
  solverDescriptions : PortDescriptions rep index bd boundary descriptionSizes solverPortSize

variable {index : Index} (P : Parameters (Q := Q) (F := F) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) (K := K) (M := M) index)

/-- General local code with an algebraic output interface, identified with the
named game's adversary at every key. Code/advice and all supported execution
paths are bounded. Per-kind allowances refer to the actual source computation. -/
structure AlgebraicAdversary where
  source : Model.LazyAGM.Adversary F (index.ty.Value (cryptoBase F G₁ G₂ K M))
    (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ G₂
  program : G₂ → OracleComp (generalSpec (index.ty.Value (cryptoBase F G₁ G₂ K M))
    (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ P.randomBound)
    ((AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M))
  caller : GeneralCaller.Caller (Q := Q) (bd := P.bd)
  realizes : caller.machine.Implements program
  corresponds : ∀ pk, AGM.outputView <$> simulateQ (generalSource P.randomBound) (program pk) = source.main pk
  runs : caller.RunsWithin (fun _ => P.execution)
  storedCode : P.descriptionSizes.localSize caller.initCode + 2 * P.descriptionSizes.localSize caller.headCode +
    P.descriptionSizes.localSize caller.updateCode ≤ P.callerCodeLimit
  randomQueries : ∀ pk, IsQueryBoundP (source.main pk) (fun i => queryKind i = 0) P.queries.random
  hashQueries : ∀ pk, IsQueryBoundP (source.main pk) (fun i => queryKind i = 1) P.queries.hash
  signingQueries : ∀ pk, IsQueryBoundP (source.main pk) (fun i => queryKind i = 2) P.queries.sign

namespace Parameters

def solverCode : Nat :=
  P.factor * programDescription index.bound P.callerCodeLimit
    (P.sampling.scalar.descriptionSize P.descriptionSizes) (P.sampler.code.descriptionSize P.descriptionSizes)
    P.queries.total P.allowance P.instructionSize P.handlerPortSize P.solverPortSize

def goodTime : Nat :=
  goodProgramTime index P.overhead P.execution P.inputWidth P.width P.outputWidth P.routeWidth
    P.queries.total P.queries.total P.comparisonTime P.scalarTime P.opTime P.handlerAdapterTime P.solverAdapterTime
    P.dynamicTime P.handlerTickTime P.callerTickTime P.extractionTickTime

def badTime : Nat :=
  badProgramTime index P.overhead P.execution P.inputWidth P.width P.outputWidth P.routeWidth
    P.queries.total P.queries.total P.comparisonTime P.scalarTime P.opTime P.handlerAdapterTime P.solverAdapterTime
    P.dynamicTime P.handlerTickTime P.callerTickTime P.extractionTickTime

/-- Maximum DLog success among programs in this same fixed backend, at the
specified online time and the derived stored-code/input limits. -/
noncomputable def dlogBound (time : Nat) : ENNReal :=
  Model.advantageBound (Model.dlog11Advantage (F := F) P.generator P.keyGenerator)
    (dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description
      P.generator P.keyGenerator P.inputWidth P.solverCode time)

/-- The two reduction branches plus the original inverse-field-size loss. -/
noncomputable def securityBound [Fintype F] : ENNReal :=
  P.dlogBound P.goodTime + P.dlogBound P.badTime + 1 / (Fintype.card F : ENNReal)

end Parameters

end Signatures.Runtime.WeightedAGM.General
