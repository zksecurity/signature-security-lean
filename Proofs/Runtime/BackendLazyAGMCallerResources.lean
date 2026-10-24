import Proofs.Runtime.BackendLazyAGMCallerBudget
import Proofs.Runtime.BackendSignatureCallerResources

/-! Native AGM caller bounds from the attacker's own execution resources. The
actual dispatcher is charged from primitive contracts, and its store invariant
is preserved. No caller-specific invariant, arithmetic attacker program, or
finished reduction budget is required. -/

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
  (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
  (recovery : SignatureHandler.RequestRecovery (Q := Q) rep bd)

include sizes lists laws dataLaws primitiveBound mono routing dispatchLaws hrun recovery

theorem goodCaller_bound_of_resources
    (width cap routeWidth fuel tickTime comparisonTime scalarTime zeroTime scaleTime adapterTime dynamicTime : Nat)
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
    (hrequest : recovery.recover bound.peakHeadSize ≤ width)
    (hstate : bound.peakStateSize ≤ routeWidth) (hhead : bound.peakHeadSize ≤ routeWidth)
    (htick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ tickTime)
    (input : Input) (saved : (storeTy scalar goodConfigTy).Value (cryptoBase F G₁ G₂ M M))
    (hiStore : ReservedState (Q := Q) rep width cap fuel saved)
    (hiInput : Q.size bd.input input ≤ routeWidth)
    (z : Run (Option Output × (storeTy scalar goodConfigTy).Value (cryptoBase F G₁ G₂ M M)))
    (hz' : z ∈ support ((goodCaller rep bd ports sampler data cost primitive sampling R fuel).run
      control queryCost (input, saved))) :
    (ReservedState (Q := Q) rep width cap 0 z.value.2 ∧
      Q.size (rep.ty (storeTy scalar goodConfigTy)) z.value.2 ≤ handlerStoreWidth width cap) ∧
      z.steps ≤ SignatureHandler.callerTime overhead routeWidth fuel
        (bound.work + 2 * bound.queries + 2) (fun _ => bound.queries)
        (goodHandlerTime overhead width cap comparisonTime scalarTime zeroTime scaleTime adapterTime dynamicTime) tickTime := by
  exact goodCaller_bound rep bd ports sampler data cost primitive sampling control queryCost
    sizes lists laws dataLaws primitiveBound mono routing dispatchLaws R
    width cap routeWidth fuel (bound.work + 2 * bound.queries + 2) tickTime
    comparisonTime scalarTime zeroTime scaleTime adapterTime dynamicTime (fun _ => bound.queries)
    hh hu hb hf hg hroute he hsample hz hscale caps dynamicSamples
    (fun _ => GeneralCaller.Reachable R)
    (fun _ state hs i next hv =>
      SignatureHandler.resource_step rep bd sizes R recovery bound hrun width hrequest state hs i next hv)
    (fun _ state hs =>
      let widths := GeneralCaller.reachable_sizes R bound hrun state hs
      ⟨widths.1.trans hstate, widths.2.trans hhead⟩)
    htick input saved (GeneralCaller.reachable_init R input) hiStore hiInput
    (GeneralCaller.budget_of_resources R bound hrun (generalReplies M G₁ randomBound) generalKind fuel input) z hz'

theorem badCaller_bound_of_resources
    (width cap routeWidth fuel tickTime comparisonTime scalarTime zeroTime scaleTime addTime adapterTime dynamicTime : Nat)
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
    (hrequest : recovery.recover bound.peakHeadSize ≤ width)
    (hstate : bound.peakStateSize ≤ routeWidth) (hhead : bound.peakHeadSize ≤ routeWidth)
    (htick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ tickTime)
    (input : Input) (saved : (storeTy (.pair scalar scalar) badConfigTy).Value (cryptoBase F G₁ G₂ M M))
    (hiStore : ReservedState (Q := Q) rep width cap fuel saved)
    (hiInput : Q.size bd.input input ≤ routeWidth)
    (z : Run (Option Output × (storeTy (.pair scalar scalar) badConfigTy).Value (cryptoBase F G₁ G₂ M M)))
    (hz' : z ∈ support ((badCaller rep bd ports sampler data cost primitive sampling R fuel).run
      control queryCost (input, saved))) :
    (ReservedState (Q := Q) rep width cap 0 z.value.2 ∧
      Q.size (rep.ty (storeTy (.pair scalar scalar) badConfigTy)) z.value.2 ≤ handlerStoreWidth width cap) ∧
      z.steps ≤ SignatureHandler.callerTime overhead routeWidth fuel
        (bound.work + 2 * bound.queries + 2) (fun _ => bound.queries)
        (badHandlerTime overhead width cap comparisonTime scalarTime zeroTime scaleTime addTime adapterTime dynamicTime) tickTime := by
  exact badCaller_bound rep bd ports sampler data cost primitive sampling control queryCost
    sizes lists laws dataLaws primitiveBound mono routing dispatchLaws R
    width cap routeWidth fuel (bound.work + 2 * bound.queries + 2) tickTime
    comparisonTime scalarTime zeroTime scaleTime addTime adapterTime dynamicTime (fun _ => bound.queries)
    hh hu hb hf hg hroute he hsample hz hscale hadd caps dynamicSamples
    (fun _ => GeneralCaller.Reachable R)
    (fun _ state hs i next hv =>
      SignatureHandler.resource_step rep bd sizes R recovery bound hrun width hrequest state hs i next hv)
    (fun _ state hs =>
      let widths := GeneralCaller.reachable_sizes R bound hrun state hs
      ⟨widths.1.trans hstate, widths.2.trans hhead⟩)
    htick input saved (GeneralCaller.reachable_init R input) hiStore hiInput
    (GeneralCaller.budget_of_resources R bound hrun (generalReplies M G₁ randomBound) generalKind fuel input) z hz'

end Signatures.Runtime.LazyAGM.NativeHandler
