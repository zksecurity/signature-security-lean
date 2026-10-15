import Signatures.Runtime.BackendSchnorrAGMHandlerRoutingBudget

/-! Complete runtime certificate for the executed indexed Schnorr AGM handler.
Its assumptions concern primitive instructions, scalar sampling, uniform-query
ports and the three actual request/reply adapters. The finished dispatcher is
not an efficiency assumption. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Handler

open BackendProgram Interface

structure Times where
  comparisonTime : Nat
  subtractTime : Nat
  incrementTime : Nat
  messageTime : Nat
  pointTime : Nat
  fieldTime : Nat
  mulTime : Nat
  equalityTime : Nat
  pointZeroTime : Nat
  scaleTime : Nat
  groupTime : Nat
  sampleTime : Nat
  randomRequestTime : Nat
  randomResponseTime : Nat
  drawTime : Nat
  requestTime : Nat
  tagTime : Nat

def adapterBudget (overhead : Nat → Nat) (width cap basisCap signedCap groupCap rowCap coeffCap : Nat) : Nat :=
  2061 * overhead (8192 * HandlerComponents.frameWidth width cap basisCap signedCap groupCap rowCap coeffCap)

def randomBudget (overhead : Nat → Nat) (width cap basisCap signedCap groupCap rowCap coeffCap : Nat) (t : Times) : Nat :=
  Random.randomTime overhead width cap basisCap signedCap groupCap rowCap coeffCap
    t.randomRequestTime t.randomResponseTime t.drawTime + adapterBudget overhead width cap basisCap signedCap groupCap rowCap coeffCap

def hashBudget (overhead : Nat → Nat) (width cap basisCap signedCap groupCap rowCap coeffCap : Nat) (t : Times) : Nat :=
  HashDispatch.dispatchTime overhead width cap (HandlerComponents.historyWidth width basisCap signedCap)
    basisCap groupCap rowCap coeffCap t.comparisonTime t.subtractTime t.incrementTime t.messageTime t.pointTime
    t.fieldTime t.mulTime t.equalityTime t.sampleTime t.pointZeroTime +
      adapterBudget overhead width cap basisCap signedCap groupCap rowCap coeffCap

def signingBudget (overhead : Nat → Nat) (width cap basisCap signedCap groupCap rowCap coeffCap : Nat) (t : Times) : Nat :=
  SigningDispatch.dispatchTime overhead width cap basisCap signedCap groupCap rowCap coeffCap
    t.fieldTime t.scaleTime t.groupTime t.messageTime t.pointTime t.sampleTime +
      adapterBudget overhead width cap basisCap signedCap groupCap rowCap coeffCap

def timeBudget (overhead : Nat → Nat) (width cap basisCap signedCap groupCap rowCap coeffCap portWidth : Nat) (t : Times) : Nat :=
  handlerTime overhead (frameWidth width cap basisCap signedCap groupCap rowCap coeffCap portWidth)
    (randomBudget overhead width cap basisCap signedCap groupCap rowCap coeffCap t)
    (hashBudget overhead width cap basisCap signedCap groupCap rowCap coeffCap t)
    (signingBudget overhead width cap basisCap signedCap groupCap rowCap coeffCap t) t.requestTime t.tagTime

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M Input Output : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (randomPorts : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))

structure PrimitiveCaps (width basisCap arityCap : Nat) (t : Times) : Prop where
  unit : Q.size rep.data.unit () ≤ width
  bool : ∀ b, Q.size rep.data.bool b ≤ width
  scalar : ∀ f : F, Q.size (rep.ty Signatures.Runtime.scalar) f ≤ width
  point : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width
  natural : ∀ n ≤ max (basisCap + 1) arityCap, Q.size rep.data.nat n ≤ width
  randomPosition : ∀ n ≤ arityCap, Q.size iface.position n ≤ width
  randomResponse : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.size iface.response ⟨n, r⟩ ≤ width
  randomRequestTime : ∀ n ≤ arityCap, Q.cost randomPorts.request n ≤ t.randomRequestTime
  randomResponseTime : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.cost randomPorts.response ⟨n, r⟩ ≤ t.randomResponseTime
  drawTime : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), queryCost n r +
    control.query (Q.size iface.position n) (Q.size iface.response ⟨n, r⟩) ≤ t.drawTime
  comparison : ∀ n ≤ basisCap, (primitiveBound .natEq).time (n, 0) ≤ t.comparisonTime
  subtract : ∀ n ≤ basisCap, (primitiveBound .natSub).time (n, 1) ≤ t.subtractTime
  increment : ∀ n ≤ basisCap, (primitiveBound .natAdd).time (n, 1) ≤ t.incrementTime
  messageEq : ∀ a b : M, Q.size (rep.ty message) a ≤ 15 * width → Q.size (rep.ty message) b ≤ 15 * width →
    (primitiveBound .messageEq).time (a, b) ≤ t.messageTime
  pointEq : ∀ a b : G₁, Q.size (rep.ty point₁) a ≤ 15 * width → Q.size (rep.ty point₁) b ≤ 15 * width →
    (primitiveBound .point₁Eq).time (a, b) ≤ t.pointTime
  zero : (primitiveBound .zero).time () ≤ t.fieldTime
  pointZero : (primitiveBound .zero₁).time () ≤ t.pointZeroTime
  add : ∀ a b : F, (primitiveBound .add).time (a, b) ≤ t.fieldTime
  mul : ∀ a b : F, (primitiveBound .mul).time (a, b) ≤ t.mulTime
  scalarEq : ∀ a b : F, (primitiveBound .scalarEq).time (a, b) ≤ t.equalityTime
  neg : ∀ f : F, (primitiveBound .neg).time f ≤ t.fieldTime
  scale : ∀ f : F, ∀ g : G₁, (primitiveBound .scale₁).time (f, g) ≤ t.scaleTime
  sub : ∀ g h : G₁, (primitiveBound .sub₁).time (g, h) ≤ t.groupTime
  sample : Bounds control queryCost sampler (fun _ => True)
    (fun f => Q.size (rep.ty Signatures.Runtime.scalar) f ≤ width) t.sampleTime

variable [C.HasOption] [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  [QD : Q.IsDistributive] [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output) (ports : Ports (Q := Q) rep bd)
  (data : DataCode Q rep.data)
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead) (mono : Monotone overhead)
  (routing : RoutingCostLaws control overhead) (dispatchLaws : DispatchCostLaws (Q := Q) overhead)

include sizes lists laws dataLaws mono routing dispatchLaws

theorem code_bound (width cap basisCap signedCap groupCap rowCap coeffCap arityCap portWidth : Nat) (t : Times)
    (hh : header ≤ width)
    (caps : PortCaps rep bd ports width groupCap rowCap coeffCap arityCap portWidth t.requestTime t.tagTime)
    (primitives : PrimitiveCaps rep cost primitive randomPorts sampler control queryCost primitiveBound width basisCap arityCap t) :
    Bounds control queryCost (code rep bd ports data cost primitive randomPorts sampler)
      (fun input => RequestBound (Q := Q) rep width groupCap rowCap coeffCap arityCap input.1 ∧
        HandlerComponents.StoreBound (Q := Q) rep width cap basisCap signedCap input.2)
      (fun output => Q.size bd.idx output.1 ≤ portWidth ∧
        HandlerComponents.StoreBound (Q := Q) rep width (cap + 1) (basisCap + 1) (signedCap + 1) output.2)
      (timeBudget overhead width cap basisCap signedCap groupCap rowCap coeffCap portWidth t) := by
  apply code_bound_of_components rep bd ports data cost primitive randomPorts sampler sizes lists laws mono control queryCost routing dispatchLaws
    width cap basisCap signedCap groupCap rowCap coeffCap arityCap portWidth t.requestTime t.tagTime
    (randomBudget overhead width cap basisCap signedCap groupCap rowCap coeffCap t)
    (hashBudget overhead width cap basisCap signedCap groupCap rowCap coeffCap t)
    (signingBudget overhead width cap basisCap signedCap groupCap rowCap coeffCap t)
    hh primitives.bool primitives.scalar primitives.point caps
  · exact HandlerComponents.random_bound rep data cost primitive sizes lists laws dataLaws mono control queryCost routing randomPorts
      width cap basisCap signedCap groupCap rowCap coeffCap arityCap t.randomRequestTime t.randomResponseTime t.drawTime
      hh primitives.unit primitives.bool primitives.scalar primitives.point
      (fun n hn => primitives.natural n (hn.trans (Nat.le_max_right _ _)))
      primitives.randomPosition primitives.randomResponse primitives.randomRequestTime primitives.randomResponseTime primitives.drawTime
  · exact HandlerComponents.hash_bound rep data cost primitive sizes lists laws dataLaws mono control queryCost routing primitiveBound sampler
      width cap basisCap signedCap groupCap rowCap coeffCap t.comparisonTime t.subtractTime t.incrementTime
      t.messageTime t.pointTime t.fieldTime t.mulTime t.equalityTime t.sampleTime t.pointZeroTime
      hh primitives.unit primitives.bool (fun n hn => primitives.natural n (hn.trans (Nat.le_max_left _ _)))
      primitives.scalar primitives.point primitives.comparison primitives.subtract primitives.increment
      primitives.messageEq primitives.pointEq primitives.zero primitives.pointZero primitives.add primitives.mul primitives.scalarEq primitives.sample
  · exact HandlerComponents.signing_bound rep data cost primitive sizes lists laws dataLaws mono control queryCost routing primitiveBound sampler
      width cap basisCap signedCap groupCap rowCap coeffCap t.fieldTime t.scaleTime t.groupTime t.messageTime t.pointTime t.sampleTime
      hh primitives.unit primitives.bool primitives.scalar primitives.point primitives.zero primitives.neg primitives.scale primitives.sub
      primitives.messageEq primitives.pointEq primitives.sample

end Signatures.Runtime.SchnorrAGM.Native.Handler
