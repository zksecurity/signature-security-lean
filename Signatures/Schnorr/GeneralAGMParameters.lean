import Signatures.Runtime.BackendSchnorrAGMSecurity
import Signatures.Model.AdvantageBound
import Signatures.Schnorr.QueryAllowance

/-! Concrete contracts for general Schnorr AGM attackers. The parameters fix
the backend, encodings, primitive prices and attacker allowances before choosing
an attacker. The reduction's complete runtime and code size are derived from
these contracts. Its efficiency is not a field of either record. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.SchnorrAGM.Native
open Signatures.Runtime.SchnorrAGM.Native.Interface

namespace Schnorr.GeneralAGM

def randomRequest {F G M : Type} (q : SourceRequest F G M) : Bool :=
  match q.value.data with
  | .random _ => true
  | _ => false

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G M : Type} [Field F] [SampleableType F] [Fintype F]
  [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] [DecidableEq M]
  [DecidableEq (SourceRequest F G M)]

structure Parameters where
  generator : G
  generates : Function.Bijective (fun x : F => x • generator)
  queries : QueryAllowance
  execution : ExecutionCost
  queryCapacity : execution.queries ≤ queries.total
  callerCodeLimit : Nat
  iface : BackendProgram.Interface (C := C) unifSpec
  rep : LanguageRepresentation C (cryptoBase F G G M M)
  bd : Boundary C (sourceSpec F G M).toPFunctor (Solver.SourceInput G) (SourceForgery F G M)
  boundary : Solver.DataPorts (Q := Q) rep bd
  data : DataCode Q rep.data
  cost : PrimitiveCosts
  primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G G M M cost).execute instr)
  ports : Interface.Ports (Q := Q) rep bd
  randomPorts : UniformSampling.Ports (Q := Q) rep.data (iface := iface)
  sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar)
  sampleLaw : sampler.denote () = ($ᵗ F : ProbComp F)
  control : ControlCosts
  queryCost : (i : Nat) → unifSpec.Range i → Nat
  header : Nat
  sizes : SizeLaws Q header
  lists : ListSizeLaws Q rep.data header
  lengths : ListLengthLaws Q rep.data
  payloads : ListPayloadLaws Q rep.data
  overhead : Nat → Nat
  laws : LocalCostLaws Q overhead
  dataLaws : DataCostLaws rep.data data overhead
  primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr)
  mono : Monotone overhead
  routing : RoutingCostLaws control overhead
  dispatch : DispatchCostLaws (Q := Q) overhead
  recovery : Handler.RequestRecovery (Q := Q) rep bd
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
  arityCap : Nat
  portWidth : Nat
  tickTime : Nat
  adapterTime : Nat
  divisionTime : Nat
  times : Handler.Times
  headerWidth : header ≤ width
  inputCapacity : 5 * width ≤ inputWidth
  routeCapacity : Handler.frameWidth width queries.total (queries.total + 2) queries.total
    width width width portWidth ≤ routeWidth
  handlerCaps : Handler.PortCaps rep bd ports width width width width arityCap portWidth times.requestTime times.tagTime
  solverCaps : Solver.PortCaps rep bd boundary width outputWidth routeWidth adapterTime
  primitives : Handler.PrimitiveCaps rep cost primitive randomPorts sampler control queryCost primitiveBound
    width (queries.total + 2) arityCap times
  requestWidth : recovery.recover execution.peakHeadSize ≤ width
  randomArity : recovery.natural.capacity (recovery.recover execution.peakHeadSize) ≤ arityCap
  stateWidth : execution.peakStateSize ≤ routeWidth
  headWidth : execution.peakHeadSize ≤ routeWidth
  tick : ∀ n ≤ queries.total, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ tickTime
  oneTime : (primitiveBound .one).time () ≤ times.fieldTime
  messageComparison : ∀ a b : M, Q.size (rep.ty message) a ≤ 15 * max width outputWidth →
    Q.size (rep.ty message) b ≤ 15 * max width outputWidth → (primitiveBound .messageEq).time (a, b) ≤ times.messageTime
  pointComparison : ∀ a b : G, Q.size (rep.ty point₁) a ≤ 15 * max width outputWidth →
    Q.size (rep.ty point₁) b ≤ 15 * max width outputWidth → (primitiveBound .point₁Eq).time (a, b) ≤ times.pointTime
  subtractionTime : ∀ a b : F, (primitiveBound .sub).time (a, b) ≤ times.fieldTime
  fieldDivisionTime : ∀ a b : F, (primitiveBound .div).time (a, b) ≤ divisionTime
  instructionSize : Nat
  randomPortSize : Nat
  handlerPortSize : Nat
  solverPortSize : Nat
  instructionDescriptions : ∀ {a b} (instr : CryptoOp a b), descriptionSizes.localSize (primitive instr) ≤ instructionSize
  randomRequestDescription : descriptionSizes.localSize randomPorts.request ≤ randomPortSize
  randomResponseDescription : descriptionSizes.localSize randomPorts.response ≤ randomPortSize
  handlerDescriptions : descriptionSizes.localSize ports.request ≤ handlerPortSize ∧
    descriptionSizes.localSize ports.randomTag ≤ handlerPortSize ∧
    descriptionSizes.localSize (ports.scalarTag false) ≤ handlerPortSize ∧
    descriptionSizes.localSize (ports.scalarTag true) ≤ handlerPortSize
  solverDescriptions : descriptionSizes.localSize boundary.input ≤ solverPortSize ∧
    descriptionSizes.localSize boundary.output ≤ solverPortSize ∧
    descriptionSizes.localSize boundary.optional ≤ solverPortSize

variable (P : Parameters (Q := Q) (F := F) (G := G) (M := M))

/-- Arbitrary local backend code with the source game's algebraic interface.
Only the attacker's own execution, stored code/advice and query counts are
certified. Its implementation agrees with the source on every input. -/
structure AlgebraicAdversary where
  source : AGM.Adversary F G M
  caller : GeneralCaller.Caller (Q := Q) (bd := P.bd)
  realizes : caller.machine.Implements source.main
  runs : caller.RunsWithin (fun _ => P.execution)
  storedCode : P.descriptionSizes.localSize caller.initCode + 2 * P.descriptionSizes.localSize caller.headCode +
    P.descriptionSizes.localSize caller.updateCode ≤ P.callerCodeLimit
  randomQueries : ∀ pk, IsQueryBoundP (source.main (AGM.initial P.generator pk))
    (fun q => randomRequest q = true) P.queries.random
  hashQueries : ∀ pk, IsQueryBoundP (source.main (AGM.initial P.generator pk))
    (fun q => AGM.Reduction.hashRequest q = true) P.queries.hash
  signingQueries : ∀ pk, IsQueryBoundP (source.main (AGM.initial P.generator pk))
    (fun q => AGM.Reduction.signRequest q = true) P.queries.sign

namespace Parameters

/-- Complete compiled code bound, including caller code, sampling and adapters. -/
def solverCode : Nat :=
  P.factor * Solver.programDescription P.callerCodeLimit (P.sampler.descriptionSize P.descriptionSizes)
    P.randomPortSize P.handlerPortSize P.solverPortSize P.queries.total P.allowance P.instructionSize

/-- Derived setup, caller, oracle-simulation and extraction time. The cache and
history capacities depend on query counts, never on the message universe. -/
def solverTime : Nat :=
  Solver.programTime P.overhead P.execution P.inputWidth P.width P.outputWidth P.routeWidth
    P.queries.total (P.queries.total + 2) P.queries.total P.width P.width P.width P.portWidth
    P.queries.total P.tickTime P.adapterTime P.divisionTime P.times

/-- Maximum DLog success at the fixed backend's input, code and time bounds.
A separate hardness assumption is needed to make this supremum small. -/
noncomputable def dlogBound (time : Nat) : ENNReal :=
  Model.advantageBound (fun solver => 𝒟[DiffieHellman.dlogExperiment P.generator solver] {true})
    (Solver.dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description
      P.generator P.inputWidth P.solverCode time)

end Parameters

end Schnorr.GeneralAGM
