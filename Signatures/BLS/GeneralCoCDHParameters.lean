import Proofs.Runtime.BackendCoronSecurity
import Proofs.Model.AdvantageBound
import Signatures.BLS.QueryAllowance

/-! Resources for unrestricted BLS attackers and the native Coron co-CDH reduction.
The operation, representation and backend contracts are fixed before choosing an
attacker. Neither algebraic output nor completed-reduction efficiency is assumed. -/

open BilinearGroup

open OracleComp OracleSpec PFunctor AlgebraicGroupModel
open PFunctor.DynSystem.DynComputation
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.Coron
open Signatures.Runtime.Coron.NativeSolver

namespace BLS.GeneralCoCDH

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]

/-- Individual implementation contracts and concrete attacker allowances.
The co-CDH route has a plain message/signature output, with no AGM coefficients. -/
structure Parameters where
  generator : G₁
  keyGenerator : G₂
  generates : Function.Bijective (fun r : F => r • generator)
  pairingInjective : Function.Injective (fun z : G₁ => pairing (F := F) (Gₜ := Gₜ) z keyGenerator)
  queries : QueryAllowance
  execution : ExecutionCost
  queryCapacity : execution.queries ≤ queries.total
  callerCodeLimit : Nat
  randomBound : Nat
  iface : Interface (C := C) unifSpec
  rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M)
  bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂ (M × G₁)
  ports : NativePorts (Q := Q) rep bd
  sampler : BoundedSampler rep bd ports (iface := iface)
  boundary : DataPorts (Q := Q) rep bd
  data : DataCode Q rep.data
  sampling : MachineCompiler.SamplingImplementation Q iface rep
  cost : PrimitiveCosts
  primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr)
  control : ControlCosts
  queryCost : (i : Nat) → unifSpec.Range i → Nat
  header : Nat
  sizes : SizeLaws Q header
  lists : ListSizeLaws Q rep.data header
  overhead : Nat → Nat
  mono : Monotone overhead
  routing : RoutingCostLaws control overhead
  localLaws : LocalCostLaws Q overhead
  dispatchLaws : DispatchCostLaws (Q := Q) overhead
  dataLaws : DataCostLaws rep.data data overhead
  primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr)
  backend : Backend.{v, w, x} Q unifSpec iface control queryCost
  descriptionSizes : DescriptionSize Q
  factor : Nat
  description : backend.DescriptionBound descriptionSizes factor
  allowance : Nat
  descriptionLaws : LocalDescriptionLaws descriptionSizes allowance
  descriptionData : DataDescriptionLaws descriptionSizes rep.data data allowance
  descriptionDispatch : DispatchDescriptionLaws (Q := Q) descriptionSizes allowance
  inputWidth : Nat
  messageWidth : Nat
  width : Nat
  scalarWidth : Nat
  coinWidth : Nat
  groupWidth : Nat
  keyWidth : Nat
  routeWidth : Nat
  tickTime : Nat
  comparisonTime : Nat
  scalarTime : Nat
  coinTime : Nat
  opTime : Nat
  handlerAdapterTime : Nat
  solverAdapterTime : Nat
  dynamicTime : Nat
  headerWidth : header ≤ width
  messageCapacity : messageWidth ≤ width
  routeCapacity : 8 * width ≤ routeWidth
  scalarSize : ∀ y : F, Q.size (rep.ty scalar) y ≤ scalarWidth
  coinSize : ∀ y : Fin (queries.sign + 1), Q.size (rep.ty (boundedNat queries.sign)) y ≤ coinWidth
  groupSize : ∀ y : G₁, Q.size (rep.ty point₁) y ≤ groupWidth
  keySize : ∀ y : G₂, Q.size (rep.ty point₂) y ≤ keyWidth
  inputCapacity : 3 * groupWidth + 2 * keyWidth + width + 5 * header ≤ inputWidth
  storeCapacity : storeWidth header messageWidth scalarWidth coinWidth groupWidth queries.total ≤ width
  handlerCaps : NativeHandler.PortCaps rep bd ports width handlerAdapterTime
  solverCaps : PortCaps rep bd boundary inputWidth routeWidth solverAdapterTime
  dynamicSamples : NativeHandler.DynamicSamplingCaps rep bd ports sampler control queryCost width dynamicTime
  values : NativeValueCaps (Q := Q) rep queries.sign width
  ops : NativeInstructionCaps rep cost primitive primitiveBound queries.sign width comparisonTime opTime
  samples : NativeSamplingCaps rep sampling control queryCost queries.sign scalarTime coinTime
  recovery : BoundaryRecovery (Q := Q) rep bd
  requestWidth : recovery.recover execution.peakHeadSize ≤ messageWidth
  stateWidth : execution.peakStateSize ≤ routeWidth
  headWidth : execution.peakHeadSize ≤ routeWidth
  tick : ∀ n ≤ queries.total, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ tickTime
  instructionSize : Nat
  handlerPortSize : Nat
  solverPortSize : Nat
  instructionDescriptions : NativeInstructionDescriptions rep cost primitive descriptionSizes queries.sign instructionSize
  handlerDescriptions : NativeHandler.PortDescriptions rep bd ports descriptionSizes handlerPortSize
  solverDescriptions : PortDescriptions rep bd boundary descriptionSizes solverPortSize

variable (P : Parameters (Q := Q) (F := F) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) (M := M))

/-- Any realized attacker with its own code/execution/query bounds. It returns an
arbitrary group point; no algebraic representation of that point is required. -/
structure Adversary where
  source : BLS.ROM.AdversaryPK M G₁ G₂
  program : G₂ → OracleComp (generalSpec M G₁ P.randomBound) (M × G₁)
  caller : GeneralCaller.Caller (Q := Q) (bd := P.bd)
  realizes : caller.machine.Implements program
  corresponds : ∀ pk, simulateQ (generalSource P.randomBound) (program pk) = source pk
  runs : caller.RunsWithin (fun _ => P.execution)
  storedCode : P.descriptionSizes.localSize caller.initCode + 2 * P.descriptionSizes.localSize caller.headCode +
    P.descriptionSizes.localSize caller.updateCode ≤ P.callerCodeLimit
  randomQueries : ∀ pk, IsQueryBoundP (source pk) (fun i => BLS.queryKind i = 0) P.queries.random
  hashQueries : ∀ pk, IsQueryBoundP (source pk) (fun i => BLS.queryKind i = 1) P.queries.hash
  signingQueries : ∀ pk, IsQueryBoundP (source pk) (fun i => Sum.isRight i = true) P.queries.sign

namespace Parameters

/-- Stored code/advice, native sampling, handlers, setup, and extraction code. -/
def solverCode : Nat :=
  P.factor * (P.callerCodeLimit + P.queries.total + 3 * P.sampling.scalar.descriptionSize P.descriptionSizes +
    3 * (P.sampling.uniform P.queries.sign).descriptionSize P.descriptionSizes +
    P.sampler.code.descriptionSize P.descriptionSizes + 4000 * P.allowance + 40 * P.instructionSize +
    4 * P.handlerPortSize + 3 * P.solverPortSize + 500)

/-- Full Coron reduction time, including the caller's work and query simulation. -/
def solverTime : Nat :=
  nativeSolverTime P.overhead P.inputWidth P.width P.routeWidth P.queries.total P.queries.total
    (P.execution.work + 2 * P.execution.queries + 2) P.tickTime (fun _ => P.execution.queries)
    P.comparisonTime P.scalarTime P.coinTime P.opTime P.handlerAdapterTime P.solverAdapterTime P.dynamicTime

end Parameters

/-- Construct the actual native Coron executable and derive its complete budget. -/
theorem reduction_within (A : Adversary P) :
    coCDHWithin P.rep P.backend P.descriptionSizes P.factor P.description
      P.generator P.keyGenerator P.inputWidth P.solverCode P.solverTime
      (BLS.CoCDH.coronReductionLazyPK (F := F) P.queries.sign (BLS.ROM.cacheForgeryPK A.source)) := by
  have hchallenge : ∀ r : F, ∀ h : G₁,
      Q.size (P.rep.env inputTypes) (P.generator, P.keyGenerator, r • P.generator, r • P.keyGenerator, h, ()) ≤
        P.inputWidth := by
    intro r h
    exact (challenge_size P.rep P.sizes P.groupWidth P.keyWidth P.width
      P.groupSize P.keySize P.values.unit P.generator P.keyGenerator r h).trans P.inputCapacity
  have certificate := program_within_of_resources P.rep P.bd P.ports P.sampler P.boundary P.data P.sampling
    P.cost P.primitive P.control P.queryCost P.sizes P.lists P.mono P.routing P.localLaws P.dispatchLaws P.dataLaws
    P.primitiveBound A.caller P.backend P.descriptionSizes P.factor P.description P.allowance P.descriptionLaws
    P.descriptionData P.descriptionDispatch P.queries.sign P.inputWidth P.messageWidth P.width P.scalarWidth
    P.coinWidth P.groupWidth P.queries.total P.routeWidth P.queries.total P.tickTime P.comparisonTime
    P.scalarTime P.coinTime P.opTime P.handlerAdapterTime P.solverAdapterTime P.dynamicTime
    P.headerWidth P.messageCapacity P.routeCapacity le_rfl P.scalarSize P.coinSize P.groupSize P.storeCapacity
    P.handlerCaps P.solverCaps P.dynamicSamples P.values P.ops P.samples P.execution A.runs P.recovery P.requestWidth
    P.stateWidth P.headWidth P.queryCapacity P.tick A.program A.realizes A.source A.corresponds
    P.instructionSize P.handlerPortSize P.solverPortSize P.instructionDescriptions P.handlerDescriptions P.solverDescriptions
  refine ⟨hchallenge, Within.mono P.backend P.descriptionSizes P.factor P.description certificate ?_ le_rfl⟩
  apply Nat.mul_le_mul_left
  have h := A.storedCode
  dsimp only [Parameters.solverCode]
  omega

end BLS.GeneralCoCDH
