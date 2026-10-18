import Signatures.Runtime.BackendLazyAGMSecurity
import Signatures.Model.AdvantageBound
import Signatures.BLS.QueryAllowance
import Signatures.Model.DirectAGM

/-! Supporting records for the concrete general-attacker BLS AGM statement.
`Parameters` fixes the curve, backend, query/resource allowances, and individual
operation contracts before choosing an attacker. `AlgebraicAdversary` supplies
only the attacker's actual realization and its own resource/query bounds.
Neither record assumes that a completed reduction meets a resource budget.

These are pointwise concrete parameters. A family can instantiate them at each
security parameter; calling an arbitrary family polynomial-time still requires
polynomial bounds on its allowances and primitive costs. -/

open BilinearGroup

open OracleComp OracleSpec PFunctor AlgebraicGroupModel
open PFunctor.DynSystem.DynComputation
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.Coron
open Signatures.Runtime.LazyAGM Signatures.Runtime.LazyAGM.NativeHandler
open Signatures.Runtime.LazyAGM.NativeSolver

namespace BLS.GeneralAGM

abbrev QueryAllowance := BLS.QueryAllowance

def QueryAllowance.total (q : QueryAllowance) : Nat := q.random + q.hash + q.sign

def queryKind {M : Type} : (Nat ⊕ M) ⊕ M → Fin 3
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => 2

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ M : Type} [Field F] [SampleableType F] [Fintype F]
  [SampleableType G₁] [Fintype G₁]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq Gₜ] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]

/-- A fixed curve/backend and concrete allowances for a class of attackers.
All cost assumptions below concern implemented primitives or encodings. -/
structure Parameters where
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
  rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M)
  bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂
    ((AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M))
  ports : NativePorts (Q := Q) rep bd
  sampler : BoundedSampler rep bd ports (iface := iface)
  boundary : DataPorts (Q := Q) rep bd
  data : DataCode Q rep.data
  cost : PrimitiveCosts
  primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr)
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
  recovery : SignatureHandler.RequestRecovery (Q := Q) rep bd
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
  messageWidth : Nat
  comparisonTime : Nat
  scalarTime : Nat
  opTime : Nat
  handlerAdapterTime : Nat
  solverAdapterTime : Nat
  dynamicTime : Nat
  callerTickTime : Nat
  extractionTickTime : Nat
  headerWidth : header ≤ width
  inputCapacity : 9 * width ≤ inputWidth
  values : ValueCaps (Q := Q) rep width queries.total
  ops : OperationCaps rep cost primitive primitiveBound queries.total messageWidth opTime comparisonTime
  handlerCaps : SignatureHandler.PortCaps rep bd ports width handlerAdapterTime
  solverCaps : PortCaps rep bd boundary width outputWidth routeWidth solverAdapterTime
  dynamicSamples : SignatureHandler.DynamicSamplingCaps rep bd ports sampler control queryCost width dynamicTime
  storeCapacity : handlerStoreWidth width queries.total ≤ routeWidth
  handlerComparison : 15 * handlerStoreWidth width queries.total ≤ messageWidth
  extractionComparison : 3 * extractionWidth (terminalInputWidth width outputWidth queries.total)
    queries.total outputWidth queries.total ≤ messageWidth
  requestWidth : recovery.recover execution.peakHeadSize ≤ width
  stateWidth : execution.peakStateSize ≤ routeWidth
  headWidth : execution.peakHeadSize ≤ routeWidth
  sampleTime : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime
  callerTick : ∀ n ≤ queries.total, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ callerTickTime
  extractionTick : ∀ n ≤ queries.total,
    ∀ encoded ≤ 7 * extractionWidth (terminalInputWidth width outputWidth queries.total)
      queries.total outputWidth queries.total, control.loop n encoded ≤ extractionTickTime
  instructionSize : Nat
  handlerPortSize : Nat
  solverPortSize : Nat
  instructionDescriptions : ∀ {a b} (instr : CryptoOp a b), descriptionSizes.localSize (primitive instr) ≤ instructionSize
  handlerDescriptions : HandlerPortDescriptions rep bd ports descriptionSizes handlerPortSize
  solverDescriptions : PortDescriptions rep bd boundary descriptionSizes solverPortSize

variable (P : Parameters (Q := Q) (F := F) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) (M := M))

/-- General local code with an algebraic output interface, identified with the
shared attacker's derived coefficient view at every key. The execution budget
includes producing this encoded output, including regrouping. Code/advice and all supported execution
paths are bounded. Per-kind allowances refer to the actual source computation. -/
structure AlgebraicAdversary where
  source : Model.DirectAGM.Adversary F M M G₁ G₂
  program : G₂ → OracleComp (generalSpec M G₁ P.randomBound)
    ((AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M))
  caller : GeneralCaller.Caller (Q := Q) (bd := P.bd)
  realizes : caller.machine.Implements program
  corresponds : ∀ pk, AGM.outputView <$> simulateQ (generalSource P.randomBound) (program pk) = (Model.DirectAGM.ProofView.adversary P.generator source).main pk
  runs : caller.RunsWithin (fun _ => P.execution)
  storedCode : P.descriptionSizes.localSize caller.initCode + 2 * P.descriptionSizes.localSize caller.headCode +
    P.descriptionSizes.localSize caller.updateCode ≤ P.callerCodeLimit
  randomQueries : ∀ pk, IsQueryBoundP (source.main (Model.LazyAGM.Interactive.initialInput P.generator pk))
    (fun i => queryKind i.value.data = 0) P.queries.random
  hashQueries : ∀ pk, IsQueryBoundP (source.main (Model.LazyAGM.Interactive.initialInput P.generator pk))
    (fun i => queryKind i.value.data = 1) P.queries.hash
  signingQueries : ∀ pk, IsQueryBoundP (source.main (Model.LazyAGM.Interactive.initialInput P.generator pk))
    (fun i => queryKind i.value.data = 2) P.queries.sign

/-- The reduction derives its coefficient representation from the shared attacker. -/
def AlgebraicAdversary.proofView (A : AlgebraicAdversary P) : Model.LazyAGM.Adversary F M M G₁ G₂ :=
  Model.DirectAGM.ProofView.adversary P.generator A.source

namespace Parameters

def solverCode : Nat :=
  P.factor * programDescription P.callerCodeLimit
    (P.sampling.scalar.descriptionSize P.descriptionSizes) (P.sampler.code.descriptionSize P.descriptionSizes)
    P.queries.total P.allowance P.instructionSize P.handlerPortSize P.solverPortSize

def goodTime : Nat :=
  goodProgramTime P.overhead P.execution P.inputWidth P.width P.outputWidth P.routeWidth
    P.queries.total P.queries.total P.comparisonTime P.scalarTime P.opTime P.handlerAdapterTime P.solverAdapterTime
    P.dynamicTime P.callerTickTime P.extractionTickTime

def badTime : Nat :=
  badProgramTime P.overhead P.execution P.inputWidth P.width P.outputWidth P.routeWidth
    P.queries.total P.queries.total P.comparisonTime P.scalarTime P.opTime P.handlerAdapterTime P.solverAdapterTime
    P.dynamicTime P.callerTickTime P.extractionTickTime

/-- Maximum DLog success among programs in this same fixed backend, at the
specified online time and the derived stored-code/input limits. -/
noncomputable def dlogBound (time : Nat) : ENNReal :=
  Model.advantageBound (Model.dlog11Advantage (F := F) P.generator P.keyGenerator)
    (dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description
      P.generator P.keyGenerator P.inputWidth P.solverCode time)

/-- The two reduction branches plus the original inverse-field-size loss. -/
noncomputable def securityBound : ENNReal :=
  P.dlogBound P.goodTime + P.dlogBound P.badTime + 1 / (Fintype.card F : ENNReal)

end Parameters

end BLS.GeneralAGM
