import Proofs.Runtime.BackendWeightedOracleBudget
import Proofs.Runtime.BackendWeightedCallerBudget

/-! Complete native interaction-phase bounds for weighted AGM reductions. The
attacker supplies its own realized local-work/query resources and reachable
encoding bounds. Every dispatcher/reply cost is derived from primitive contracts;
caller control, request retention and accumulated private state are charged. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.WeightedAGM.NativeHandler

open BackendProgram Reply

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ K M Input Output : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (index : Index)
  (bd : Boundary C (generalSpec (index.ty.Value (cryptoBase F G₁ G₂ K M)) (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor Input Output)
  (ports : NativePorts (Q := Q) rep index.ty index.messageTy bd) (sampler : BoundedSampler rep index.ty index.messageTy bd ports (iface := iface))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead) (routing : RoutingCostLaws control overhead)
  (dispatchLaws : DispatchCostLaws (Q := Q) overhead)

  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

include sizes lists laws dataLaws primitiveBound mono routing dispatchLaws

theorem goodCaller_bound
    (width cap routeWidth fuel localTime callerTickTime natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime adapterTime dynamicTime : Nat)
    (queries : Fin 3 → Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hroute : handlerStoreWidth index width cap ≤ routeWidth)
    (hj : ∀ j : Fin (index.bound + 1), Q.size (rep.ty (boundedNat index.bound)) j ≤ width)
    (hn : ∀ k ≤ (index.bound + 1) + index.bound + 1, Q.size rep.data.nat k ≤ width)
    (hne : ∀ j k, j ≤ (index.bound + 1) + index.bound → k ≤ (index.bound + 1) + index.bound →
      (primitiveBound .natEq).time (j, k) ≤ natEqTime)
    (hns : ∀ k ≤ index.bound + 1, (primitiveBound .natSub).time (k, 1) ≤ natSubTime)
    (hna : ∀ k ≤ index.bound + 1, (primitiveBound .natAdd).time (k, 1) ≤ natAddTime)
    (he : ∀ x y : K, Q.size (rep.ty key) x ≤ Reply.goodSignEvaluationWidth index (handlerStoreWidth index width cap) (cap * (index.bound + 1)) →
      Q.size (rep.ty key) y ≤ Reply.goodSignEvaluationWidth index (handlerStoreWidth index width cap) (cap * (index.bound + 1)) → (primitiveBound .keyEq).time (x, y) ≤ topicTime)
    (hi : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ indexTime)
    (hdraw : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound .zero).time () ≤ zeroTime)
    (ha : ∀ x y : F, (primitiveBound .add).time (x, y) ≤ addTime)
    (hmul : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (htick : ∀ n ≤ index.bound + 1, ∀ encoded ≤ 7 * Reply.goodSignEvaluationWidth index
      (handlerStoreWidth index width cap) (cap * (index.bound + 1)), control.loop n encoded ≤ evaluatorTickTime)
    (hgen : ∀ k ≤ index.bound + 1, (primitiveBound (.finOfNat index.bound)).time k ≤ genIndexTime)
    (hfin : (primitiveBound (.finZero index.bound)).time () ≤ finZeroTime)
    (hone : (primitiveBound .one).time () ≤ oneTime)
    (hscale : ∀ r : F, ∀ g : G₁, (primitiveBound .scale₁).time (r, g) ≤ scaleTime)
    (caps : PortCaps rep index.ty index.messageTy bd ports width adapterTime)
    (samples : DynamicSamplingCaps rep index.ty index.messageTy bd ports sampler control queryCost width dynamicTime)
    (callerInv : Nat → R.machine.State → Prop)
    (hcallerStep : ∀ n state, callerInv (n + 1) state → ∀ i next,
      R.machine.view state = .inr ⟨i, next⟩ →
        RequestSized (Q := Q) rep index.ty index.messageTy width i ∧ ∀ answer, callerInv n (next answer))
    (hcallerWidth : ∀ n state, callerInv n state →
      Q.size R.state state ≤ routeWidth ∧ Q.size bd.head (R.machine.head state) ≤ routeWidth)
    (hcallerTick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ callerTickTime)
    (input : Input) (saved : (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy).Value (cryptoBase F G₁ G₂ K M))
    (hiCaller : callerInv fuel (R.machine.init input))
    (hiStore : ReservedState (Q := Q) rep index width cap fuel saved)
    (hiInput : Q.size bd.input input ≤ routeWidth)
    (hbudget : GeneralCaller.Budget R
      (generalReplies (index.ty.Value (cryptoBase F G₁ G₂ K M)) (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound)
      generalKind fuel input localTime queries)
    (z : Run (Option Output × (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy).Value (cryptoBase F G₁ G₂ K M)))
    (hz' : z ∈ support ((goodCaller rep index bd ports sampler data cost primitive sampling R fuel).run
      control queryCost (input, saved))) :
    (ReservedState (Q := Q) rep index width cap 0 z.value.2 ∧
      Q.size (rep.ty (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy)) z.value.2 ≤ handlerStoreWidth index width cap) ∧
      z.steps ≤ SignatureHandler.callerTime overhead routeWidth fuel localTime queries
        (goodHandlerTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime adapterTime dynamicTime) callerTickTime := by
  have h8 := handlerStoreWidth_ge index width cap
  have h := caller_bound rep index.ty index.messageTy bd ports sampler
    (rep.ty (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy))
    (Reply.goodHash rep data cost primitive sampling index) (Reply.goodSign rep data cost primitive sampling index)
    control queryCost sizes laws dispatchLaws mono routing R
    (fun n => ReservedState (Q := Q) rep index width cap n) (ReservedState (Q := Q) rep index width cap 0)
    width routeWidth fuel localTime
    (goodHandlerTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime adapterTime dynamicTime)
    callerTickTime queries (hh.trans ((by omega : width ≤ handlerStoreWidth index width cap).trans hroute)) (h8.trans hroute)
    (fun n saved hs => (goodReserved_size rep index sizes lists width cap n hh hf hg saved hs).trans hroute)
    (fun n => reserved_weaken rep index width cap 0 n (Nat.zero_le n))
    (fun n => goodCode_bound rep index bd ports sampler data cost primitive sampling control queryCost sizes lists laws dataLaws
      primitiveBound mono routing dispatchLaws width cap n natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime adapterTime dynamicTime
      hh hu hb hf hg hj hn hne hns hna he hi hdraw hz ha hmul htick hgen hfin hone hscale caps samples)
    callerInv hcallerStep hcallerWidth hcallerTick input saved hiCaller hiStore hiInput hbudget z hz'
  exact ⟨⟨h.1, goodReserved_size rep index sizes lists width cap 0 hh hf hg z.value.2 h.1⟩, h.2⟩

theorem badCaller_bound
    (width cap routeWidth fuel localTime callerTickTime natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime groupAddTime adapterTime dynamicTime : Nat)
    (queries : Fin 3 → Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hroute : handlerStoreWidth index width cap ≤ routeWidth)
    (hj : ∀ j : Fin (index.bound + 1), Q.size (rep.ty (boundedNat index.bound)) j ≤ width)
    (hn : ∀ k ≤ (index.bound + 1) + index.bound + 1, Q.size rep.data.nat k ≤ width)
    (hne : ∀ j k, j ≤ (index.bound + 1) + index.bound → k ≤ (index.bound + 1) + index.bound →
      (primitiveBound .natEq).time (j, k) ≤ natEqTime)
    (hns : ∀ k ≤ index.bound + 1, (primitiveBound .natSub).time (k, 1) ≤ natSubTime)
    (hna : ∀ k ≤ index.bound + 1, (primitiveBound .natAdd).time (k, 1) ≤ natAddTime)
    (he : ∀ x y : K, Q.size (rep.ty key) x ≤ 3 * Reply.badSignEvaluationWidth index (handlerStoreWidth index width cap) (cap * (index.bound + 1)) →
      Q.size (rep.ty key) y ≤ 3 * Reply.badSignEvaluationWidth index (handlerStoreWidth index width cap) (cap * (index.bound + 1)) → (primitiveBound .keyEq).time (x, y) ≤ topicTime)
    (hi : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ indexTime)
    (hdraw : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound .zero).time () ≤ zeroTime)
    (ha : ∀ x y : F, (primitiveBound .add).time (x, y) ≤ addTime)
    (hmul : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (htick : ∀ n ≤ index.bound + 1, ∀ encoded ≤ 7 * Reply.badSignEvaluationWidth index
      (handlerStoreWidth index width cap) (cap * (index.bound + 1)), control.loop n encoded ≤ evaluatorTickTime)
    (hgen : ∀ k ≤ index.bound + 1, (primitiveBound (.finOfNat index.bound)).time k ≤ genIndexTime)
    (hfin : (primitiveBound (.finZero index.bound)).time () ≤ finZeroTime)
    (hone : (primitiveBound .one).time () ≤ oneTime)
    (hscale : ∀ r : F, ∀ g : G₁, (primitiveBound .scale₁).time (r, g) ≤ scaleTime)
    (hadd : ∀ g h : G₁, (primitiveBound .add₁).time (g, h) ≤ groupAddTime)
    (caps : PortCaps rep index.ty index.messageTy bd ports width adapterTime)
    (samples : DynamicSamplingCaps rep index.ty index.messageTy bd ports sampler control queryCost width dynamicTime)
    (callerInv : Nat → R.machine.State → Prop)
    (hcallerStep : ∀ n state, callerInv (n + 1) state → ∀ i next,
      R.machine.view state = .inr ⟨i, next⟩ →
        RequestSized (Q := Q) rep index.ty index.messageTy width i ∧ ∀ answer, callerInv n (next answer))
    (hcallerWidth : ∀ n state, callerInv n state →
      Q.size R.state state ≤ routeWidth ∧ Q.size bd.head (R.machine.head state) ≤ routeWidth)
    (hcallerTick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ callerTickTime)
    (input : Input) (saved : (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy).Value (cryptoBase F G₁ G₂ K M))
    (hiCaller : callerInv fuel (R.machine.init input))
    (hiStore : ReservedState (Q := Q) rep index width cap fuel saved)
    (hiInput : Q.size bd.input input ≤ routeWidth)
    (hbudget : GeneralCaller.Budget R
      (generalReplies (index.ty.Value (cryptoBase F G₁ G₂ K M)) (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound)
      generalKind fuel input localTime queries)
    (z : Run (Option Output × (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy).Value (cryptoBase F G₁ G₂ K M)))
    (hz' : z ∈ support ((badCaller rep index bd ports sampler data cost primitive sampling R fuel).run
      control queryCost (input, saved))) :
    (ReservedState (Q := Q) rep index width cap 0 z.value.2 ∧
      Q.size (rep.ty (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy)) z.value.2 ≤ handlerStoreWidth index width cap) ∧
      z.steps ≤ SignatureHandler.callerTime overhead routeWidth fuel localTime queries
        (badHandlerTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime groupAddTime adapterTime dynamicTime) callerTickTime := by
  have h8 := handlerStoreWidth_ge index width cap
  have h := caller_bound rep index.ty index.messageTy bd ports sampler
    (rep.ty (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy))
    (Reply.badHash rep data cost primitive sampling index) (Reply.badSign rep data cost primitive sampling index)
    control queryCost sizes laws dispatchLaws mono routing R
    (fun n => ReservedState (Q := Q) rep index width cap n) (ReservedState (Q := Q) rep index width cap 0)
    width routeWidth fuel localTime
    (badHandlerTime index overhead width cap natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime groupAddTime adapterTime dynamicTime)
    callerTickTime queries (hh.trans ((by omega : width ≤ handlerStoreWidth index width cap).trans hroute)) (h8.trans hroute)
    (fun n saved hs => (badReserved_size rep index sizes lists width cap n hh hf hg saved hs).trans hroute)
    (fun n => reserved_weaken rep index width cap 0 n (Nat.zero_le n))
    (fun n => badCode_bound rep index bd ports sampler data cost primitive sampling control queryCost sizes lists laws dataLaws
      primitiveBound mono routing dispatchLaws width cap n natEqTime natSubTime natAddTime topicTime indexTime scalarTime zeroTime addTime mulTime evaluatorTickTime genIndexTime finZeroTime oneTime scaleTime groupAddTime adapterTime dynamicTime
      hh hu hb hf hg hj hn hne hns hna he hi hdraw hz ha hmul htick hgen hfin hone hscale hadd caps samples)
    callerInv hcallerStep hcallerWidth hcallerTick input saved hiCaller hiStore hiInput hbudget z hz'
  exact ⟨⟨h.1, badReserved_size rep index sizes lists width cap 0 hh hf hg z.value.2 h.1⟩, h.2⟩

end Signatures.Runtime.WeightedAGM.NativeHandler
