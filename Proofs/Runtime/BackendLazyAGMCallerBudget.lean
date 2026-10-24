import Proofs.Runtime.BackendLazyAGMHandlerBudget
import Proofs.Runtime.BackendSignatureCallerBudget

/-! Complete native caller-phase resource bounds for both lazy AGM branches.
Actual native dispatcher costs are derived from primitive contracts. The
attacker supplies only its own realization, local/query budget, and reachable
encoding bounds; its internal algorithm need not use the arithmetic language. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.LazyAGM.NativeHandler

open BackendProgram Coron

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ M Input Output : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor Input Output)
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
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
    (width cap routeWidth fuel localTime tickTime comparisonTime scalarTime zeroTime scaleTime adapterTime dynamicTime : Nat)
    (queries : Fin 3 → Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hroute : handlerStoreWidth width cap ≤ routeWidth)
    (he : ∀ x y : M,
      Q.size (rep.ty message) x ≤ 5 * handlerStoreWidth width cap →
      Q.size (rep.ty message) y ≤ 5 * handlerStoreWidth width cap →
      (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime)
    (hsample : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound CryptoOp.zero).time () ≤ zeroTime)
    (hscale : ∀ f : F, ∀ g : G₁, (primitiveBound CryptoOp.scale₁).time (f, g) ≤ scaleTime)
    (caps : SignatureHandler.PortCaps rep bd ports width adapterTime)
    (dynamicSamples : SignatureHandler.DynamicSamplingCaps rep bd ports sampler control queryCost width dynamicTime)
    (callerInv : Nat → R.machine.State → Prop)
    (hcallerStep : ∀ n state, callerInv (n + 1) state → ∀ i next,
      R.machine.view state = .inr ⟨i, next⟩ →
        SignatureHandler.RequestSized (Q := Q) rep width i ∧ ∀ answer, callerInv n (next answer))
    (hcallerWidth : ∀ n state, callerInv n state →
      Q.size R.state state ≤ routeWidth ∧ Q.size bd.head (R.machine.head state) ≤ routeWidth)
    (htick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ tickTime)
    (input : Input) (saved : (storeTy scalar goodConfigTy).Value (cryptoBase F G₁ G₂ M M))
    (hiCaller : callerInv fuel (R.machine.init input))
    (hiStore : ReservedState (Q := Q) rep width cap fuel saved)
    (hiInput : Q.size bd.input input ≤ routeWidth)
    (hbudget : GeneralCaller.Budget R (generalReplies M G₁ randomBound) generalKind fuel input localTime queries)
    (z : Run (Option Output × (storeTy scalar goodConfigTy).Value (cryptoBase F G₁ G₂ M M)))
    (hz' : z ∈ support ((goodCaller rep bd ports sampler data cost primitive sampling R fuel).run
      control queryCost (input, saved))) :
    (ReservedState (Q := Q) rep width cap 0 z.value.2 ∧
      Q.size (rep.ty (storeTy scalar goodConfigTy)) z.value.2 ≤ handlerStoreWidth width cap) ∧
      z.steps ≤ SignatureHandler.callerTime overhead routeWidth fuel localTime queries
        (goodHandlerTime overhead width cap comparisonTime scalarTime zeroTime scaleTime adapterTime dynamicTime) tickTime := by
  have h8 : 8 * width ≤ handlerStoreWidth width cap := by dsimp [handlerStoreWidth]; nlinarith
  have h := SignatureHandler.caller_bound rep bd ports sampler (rep.ty (storeTy scalar goodConfigTy))
    (backendGoodReply rep data cost primitive sampling) control queryCost sizes laws dispatchLaws mono routing R
    (fun n => ReservedState (Q := Q) rep width cap n) (ReservedState (Q := Q) rep width cap 0)
    width routeWidth fuel localTime (goodHandlerTime overhead width cap comparisonTime scalarTime zeroTime scaleTime adapterTime dynamicTime)
    tickTime queries (hh.trans ((by omega : width ≤ handlerStoreWidth width cap).trans hroute)) (h8.trans hroute)
    (fun n saved hs => (goodReserved_size rep sizes lists width cap n hh hf hg saved hs).trans hroute)
    (fun n => reserved_weaken rep width cap 0 n (Nat.zero_le n))
    (fun n => goodCode_bound rep bd ports sampler data cost primitive sampling control queryCost sizes lists laws dataLaws
      primitiveBound mono routing dispatchLaws width cap n comparisonTime scalarTime zeroTime scaleTime adapterTime dynamicTime
      hh hu hb hf hg he hsample hz hscale caps dynamicSamples)
    callerInv hcallerStep hcallerWidth htick input saved hiCaller hiStore hiInput hbudget z hz'
  exact ⟨⟨h.1, goodReserved_size rep sizes lists width cap 0 hh hf hg z.value.2 h.1⟩, h.2⟩

theorem badCaller_bound
    (width cap routeWidth fuel localTime tickTime comparisonTime scalarTime zeroTime scaleTime addTime adapterTime dynamicTime : Nat)
    (queries : Fin 3 → Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hroute : handlerStoreWidth width cap ≤ routeWidth)
    (he : ∀ x y : M,
      Q.size (rep.ty message) x ≤ 15 * handlerStoreWidth width cap →
      Q.size (rep.ty message) y ≤ 15 * handlerStoreWidth width cap →
      (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime)
    (hsample : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound CryptoOp.zero).time () ≤ zeroTime)
    (hscale : ∀ f : F, ∀ g : G₁, (primitiveBound CryptoOp.scale₁).time (f, g) ≤ scaleTime)
    (hadd : ∀ g h : G₁, (primitiveBound CryptoOp.add₁).time (g, h) ≤ addTime)
    (caps : SignatureHandler.PortCaps rep bd ports width adapterTime)
    (dynamicSamples : SignatureHandler.DynamicSamplingCaps rep bd ports sampler control queryCost width dynamicTime)
    (callerInv : Nat → R.machine.State → Prop)
    (hcallerStep : ∀ n state, callerInv (n + 1) state → ∀ i next,
      R.machine.view state = .inr ⟨i, next⟩ →
        SignatureHandler.RequestSized (Q := Q) rep width i ∧ ∀ answer, callerInv n (next answer))
    (hcallerWidth : ∀ n state, callerInv n state →
      Q.size R.state state ≤ routeWidth ∧ Q.size bd.head (R.machine.head state) ≤ routeWidth)
    (htick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ tickTime)
    (input : Input) (saved : (storeTy (.pair scalar scalar) badConfigTy).Value (cryptoBase F G₁ G₂ M M))
    (hiCaller : callerInv fuel (R.machine.init input))
    (hiStore : ReservedState (Q := Q) rep width cap fuel saved)
    (hiInput : Q.size bd.input input ≤ routeWidth)
    (hbudget : GeneralCaller.Budget R (generalReplies M G₁ randomBound) generalKind fuel input localTime queries)
    (z : Run (Option Output × (storeTy (.pair scalar scalar) badConfigTy).Value (cryptoBase F G₁ G₂ M M)))
    (hz' : z ∈ support ((badCaller rep bd ports sampler data cost primitive sampling R fuel).run
      control queryCost (input, saved))) :
    (ReservedState (Q := Q) rep width cap 0 z.value.2 ∧
      Q.size (rep.ty (storeTy (.pair scalar scalar) badConfigTy)) z.value.2 ≤ handlerStoreWidth width cap) ∧
      z.steps ≤ SignatureHandler.callerTime overhead routeWidth fuel localTime queries
        (badHandlerTime overhead width cap comparisonTime scalarTime zeroTime scaleTime addTime adapterTime dynamicTime) tickTime := by
  have h8 : 8 * width ≤ handlerStoreWidth width cap := by dsimp [handlerStoreWidth]; nlinarith
  have h := SignatureHandler.caller_bound rep bd ports sampler (rep.ty (storeTy (.pair scalar scalar) badConfigTy))
    (backendBadReply rep data cost primitive sampling) control queryCost sizes laws dispatchLaws mono routing R
    (fun n => ReservedState (Q := Q) rep width cap n) (ReservedState (Q := Q) rep width cap 0)
    width routeWidth fuel localTime (badHandlerTime overhead width cap comparisonTime scalarTime zeroTime scaleTime addTime adapterTime dynamicTime)
    tickTime queries (hh.trans ((by omega : width ≤ handlerStoreWidth width cap).trans hroute)) (h8.trans hroute)
    (fun n saved hs => (badReserved_size rep sizes lists width cap n hh hf hg saved hs).trans hroute)
    (fun n => reserved_weaken rep width cap 0 n (Nat.zero_le n))
    (fun n => badCode_bound rep bd ports sampler data cost primitive sampling control queryCost sizes lists laws dataLaws
      primitiveBound mono routing dispatchLaws width cap n comparisonTime scalarTime zeroTime scaleTime addTime adapterTime dynamicTime
      hh hu hb hf hg he hsample hz hscale hadd caps dynamicSamples)
    callerInv hcallerStep hcallerWidth htick input saved hiCaller hiStore hiInput hbudget z hz'
  exact ⟨⟨h.1, badReserved_size rep sizes lists width cap 0 hh hf hg z.value.2 h.1⟩, h.2⟩

end Signatures.Runtime.LazyAGM.NativeHandler
