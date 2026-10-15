import Signatures.Runtime.BackendSchnorrROMSecurity
import Signatures.Runtime.BackendSchnorrROMDescriptionAllowance
import Signatures.Model.AdvantageBound
import Signatures.Schnorr.QueryAllowance

/-! Original component contracts and attacker allowances for ordinary-ROM
Schnorr. The model is fixed before the unrestricted attacker is chosen. Neither
the complete solver's efficiency nor its executable certificate is a field. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr ListROM RawTape
open Signatures.Runtime.Schnorr.ListROM.NativeInterface

namespace Schnorr.GeneralROM

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [QS : Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G M : Type} [Field F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] [DecidableEq M]

structure Parameters where
  generator : G
  generates : Function.Bijective (fun x : F => x • generator)
  queries : QueryAllowance
  execution : ExecutionCost
  queryCapacity : execution.queries ≤ queries.total
  callerCodeLimit : Nat
  iface : BackendProgram.Interface (C := C) unifSpec
  rep : LanguageRepresentation C (cryptoBase F G G M M)
  bd : Boundary C (sourceSpec F G M).toPFunctor G (M × G × F)
  boundary : NativePass.DataPorts (Q := Q) rep bd
  data : DataCode Q rep.data
  cost : PrimitiveCosts
  primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G G M M cost).execute instr)
  ports : NativeInterface.Ports (Q := Q) rep bd
  uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface)
  privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface)
  sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar)
  sampleLaw : sampler.denote () = ($ᵗ F : ProbComp F)
  control : ControlCosts
  queryCost : (i : Nat) → unifSpec.Range i → Nat
  header : Nat
  sizes : SizeLaws Q header
  lists : ListSizeLaws Q rep.data header
  overhead : Nat → Nat
  laws : LocalCostLaws Q overhead
  dataLaws : DataCostLaws rep.data data overhead
  primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr)
  mono : Monotone overhead
  routing : RoutingCostLaws control overhead
  dispatch : DispatchCostLaws (Q := Q) overhead
  recovery : NativeHandler.RequestRecovery (Q := Q) rep bd
  backend : Backend.{v, w, x} Q unifSpec iface control queryCost
  descriptionSizes : DescriptionSize Q
  factor : Nat
  description : backend.DescriptionBound descriptionSizes factor
  allowance : Nat
  descriptionLaws : LocalDescriptionLaws descriptionSizes allowance
  descriptionData : DataDescriptionLaws descriptionSizes rep.data data allowance
  descriptionDispatch : DispatchDescriptionLaws (Q := Q) descriptionSizes allowance
  inputWidth : Nat
  groupWidth : Nat
  width : Nat
  tapeWidth : Nat
  inputFits : inputWidth ≤ width
  groupSize : ∀ g : G, Q.size (rep.ty point₁) g ≤ groupWidth
  inputCapacity : 2 * groupWidth + tapeWidth + 2 * header ≤ inputWidth
  first : NativePass.Resources rep bd boundary ports cost primitive uniform privatePorts sampler primitiveBound
    control queryCost recovery execution (header := header) width tapeWidth queries.total queries.total 0 0 queries.total
  second : NativePass.Resources rep bd boundary ports cost primitive uniform privatePorts sampler primitiveBound
    control queryCost recovery execution (header := header) width tapeWidth queries.total queries.total
      (first.savedCap + 2) (first.savedCap + 2) queries.total
  scaleTime : Nat
  addTime : Nat
  messageTime : Nat
  pointTime : Nat
  incrementTime : Nat
  comparisonTime : Nat
  scalarComparisonTime : Nat
  subtractTime : Nat
  extractionScalarTime : Nat
  fieldSubTime : Nat
  divTime : Nat
  selectorOps : NativeSelection.Operations rep cost primitive primitiveBound width (queries.total + 1) queries.hash
    scaleTime addTime messageTime pointTime incrementTime comparisonTime
  extractionOps : NativeExtraction.Operations rep cost primitive primitiveBound width pointTime
    extractionScalarTime fieldSubTime divTime first.zeroTime
  indexSize : ∀ n ≤ max (queries.total + 1) queries.hash + 1, Q.size rep.data.nat n ≤ tapeWidth
  scalarComparison : ∀ f g, Q.size (rep.ty scalar) f ≤ tapeWidth → Q.size (rep.ty scalar) g ≤ tapeWidth →
    (primitiveBound .scalarEq).time (f, g) ≤ scalarComparisonTime
  indexSubtraction : ∀ n ≤ queries.hash, (primitiveBound .natSub).time (n, 1) ≤ subtractTime
  rejectionCost : Q.cost (QS.inl rep.data.unit (rep.ty (.pair NativePass.outputTy NativePass.outputTy))) () ≤
    overhead (Q.size rep.data.unit () +
      Q.size (StepClass.HasSum.sum rep.data.unit (rep.ty (.pair NativePass.outputTy NativePass.outputTy))) (.inl ()))
  acceptanceCost : ∀ p, Q.cost (QS.inr rep.data.unit (rep.ty (.pair NativePass.outputTy NativePass.outputTy))) p ≤
    overhead (Q.size (rep.ty (.pair NativePass.outputTy NativePass.outputTy)) p +
      Q.size (StepClass.HasSum.sum rep.data.unit (rep.ty (.pair NativePass.outputTy NativePass.outputTy))) (.inr p))

variable (P : Parameters (Q := Q) (F := F) (G := G) (M := M))

/-- Arbitrary local code implementing the ordinary source attacker. Only its
own execution, stored code/advice and query allowances are certified. -/
structure UnrestrictedAdversary [SampleableType G] where
  source : ROM.Adversary (F := F) (M := M) P.generator
  caller : GeneralCaller.Caller (Q := Q) (bd := P.bd)
  realizes : caller.machine.Implements source.main
  runs : caller.RunsWithin (fun _ => P.execution)
  storedCode : P.descriptionSizes.localSize caller.initCode + 2 * P.descriptionSizes.localSize caller.headCode +
    P.descriptionSizes.localSize caller.updateCode ≤ P.callerCodeLimit
  randomQueries : ∀ pk, IsQueryBoundP (source.main pk) (· matches .inl (.inl _)) P.queries.random
  signingQueries : ∀ pk, IsQueryBoundP (source.main pk) (· matches .inr _) P.queries.sign
  hashQueries : ∀ pk, IsQueryBoundP (source.main pk) (· matches .inl (.inr _)) P.queries.hash

namespace Parameters

/-- Original component descriptions with the declared caller allowance. -/
def descriptions : NativeSolver.DescriptionInputs where
  primitiveSize op := P.descriptionSizes.localSize (P.primitive op)
  samplerSize := P.sampler.descriptionSize P.descriptionSizes
  callerInit := P.callerCodeLimit
  callerHead := 0
  callerUpdate := 0
  inputPort := P.descriptionSizes.localSize P.boundary.input
  outputPort := P.descriptionSizes.localSize P.boundary.output
  optionalPort := P.descriptionSizes.localSize P.boundary.optional
  requestPort := P.descriptionSizes.localSize P.ports.request
  randomTag := P.descriptionSizes.localSize P.ports.randomTag
  hashTag := P.descriptionSizes.localSize P.ports.hashTag
  signingTag := P.descriptionSizes.localSize P.ports.signingTag
  uniformRequest := P.descriptionSizes.localSize P.uniform.request
  uniformResponse := P.descriptionSizes.localSize P.uniform.response
  privateArity := P.descriptionSizes.localSize P.privatePorts.arity
  privateReply := P.descriptionSizes.localSize P.privatePorts.reply
  rejectSize := P.descriptionSizes.localSize (QS.inl P.rep.data.unit (P.rep.ty (.pair NativePass.outputTy NativePass.outputTy)))
  acceptSize := P.descriptionSizes.localSize (QS.inr P.rep.data.unit (P.rep.ty (.pair NativePass.outputTy NativePass.outputTy)))

def solverCode : Nat := P.factor * P.descriptions.solver P.allowance P.queries.total P.queries.hash

/-- Complete setup, two executions, replay, selection, extraction and fallback. -/
def solverTime : Nat :=
  NativeSolver.resourcesTime P.overhead P.execution P.width P.tapeWidth P.queries.total P.queries.total
    P.queries.total P.first.timeInputs P.second.timeInputs P.scaleTime P.addTime P.messageTime P.pointTime
    P.incrementTime P.comparisonTime P.scalarComparisonTime P.subtractTime P.extractionScalarTime P.fieldSubTime P.divTime

/-- Maximum success among DLog solvers in the same fixed backend at the
derived input/code bounds and supplied time. Hardness can make it small. -/
noncomputable def dlogBound (time : Nat) : ENNReal :=
  Model.advantageBound (fun solver => 𝒟[DiffieHellman.dlogExperiment P.generator solver] {true})
    (NativeSolver.dlogWithin P.rep P.backend P.descriptionSizes P.factor P.description
      P.generator P.inputWidth P.solverCode time)

end Parameters

end Schnorr.GeneralROM
