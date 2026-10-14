import Signatures.Runtime.BackendLazyAGMSolverSetup
import Signatures.Runtime.BackendLazyAGMSolverTerminal
import Signatures.Runtime.BackendLazyAGMCallerResources
import Signatures.Runtime.BackendSignatureCallerOutput

/-! Complete native AGM solver runtime bounds. Setup, the actual caller with
its measured resources, and extraction are composed with charged sequencing.
The only execution allowance for an adversary is its own `RunsWithin` bound;
no premise assumes the runtime of a completed solver or caller simulation. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.LazyAGM.NativeSolver

open BackendProgram Coron NativeHandler

def programJoinWidth (inputWidth width routeWidth cap : Nat) : Nat :=
  inputWidth + 2 * routeWidth + handlerStoreWidth width cap + 2 * width

def goodProgramTime (overhead : Nat → Nat) (bound : ExecutionCost)
    (inputWidth width outputWidth routeWidth cap fuel comparisonTime scalarTime opTime
      handlerAdapterTime solverAdapterTime dynamicTime callerTickTime extractionTickTime : Nat) : Nat :=
  (solverAdapterTime + 70 * overhead (128 * setupWidth inputWidth width routeWidth cap)) +
  SignatureHandler.callerTime overhead routeWidth fuel (bound.work + 2 * bound.queries + 2)
    (fun _ => bound.queries)
    (goodHandlerTime overhead width cap comparisonTime scalarTime opTime opTime handlerAdapterTime dynamicTime)
    callerTickTime +
  goodTerminalTime overhead width outputWidth routeWidth cap comparisonTime scalarTime opTime
    solverAdapterTime extractionTickTime +
  2 * overhead (32 * programJoinWidth inputWidth width routeWidth cap)

def badProgramTime (overhead : Nat → Nat) (bound : ExecutionCost)
    (inputWidth width outputWidth routeWidth cap fuel comparisonTime scalarTime opTime
      handlerAdapterTime solverAdapterTime dynamicTime callerTickTime extractionTickTime : Nat) : Nat :=
  (scalarTime + opTime + solverAdapterTime + 112 * overhead (512 * setupWidth inputWidth width routeWidth cap)) +
  SignatureHandler.callerTime overhead routeWidth fuel (bound.work + 2 * bound.queries + 2)
    (fun _ => bound.queries)
    (badHandlerTime overhead width cap comparisonTime scalarTime opTime opTime opTime handlerAdapterTime dynamicTime)
    callerTickTime +
  badTerminalTime overhead width outputWidth routeWidth cap comparisonTime scalarTime opTime
    solverAdapterTime extractionTickTime +
  2 * overhead (32 * programJoinWidth inputWidth width routeWidth cap)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂
    ((AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M)))
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (lengths : ListLengthLaws Q rep.data)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead) (routing : RoutingCostLaws control overhead)
  (dispatch : DispatchCostLaws (Q := Q) overhead)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
  (recovery : SignatureHandler.RequestRecovery (Q := Q) rep bd)

include sizes lists lengths laws dataLaws primitiveBound mono routing dispatch hrun recovery

set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] PFunctor.Idx

theorem goodProgram_bound
    (inputWidth width outputWidth routeWidth cap fuel messageWidth comparisonTime scalarTime opTime
      handlerAdapterTime solverAdapterTime dynamicTime callerTickTime extractionTickTime : Nat)
    (hh : header ≤ width) (hcap : fuel ≤ cap)
    (values : ValueCaps (Q := Q) rep width cap)
    (ops : OperationCaps rep cost primitive primitiveBound cap messageWidth opTime comparisonTime)
    (handlerCaps : SignatureHandler.PortCaps rep bd ports width handlerAdapterTime)
    (solverCaps : PortCaps rep bd boundary width outputWidth routeWidth solverAdapterTime)
    (dynamicSamples : SignatureHandler.DynamicSamplingCaps rep bd ports sampler control queryCost width dynamicTime)
    (hroute : handlerStoreWidth width cap ≤ routeWidth)
    (hhandlerComparison : 5 * handlerStoreWidth width cap ≤ messageWidth)
    (hcomparison : 3 * extractionWidth (terminalInputWidth width outputWidth cap) cap outputWidth cap ≤ messageWidth)
    (hrequest : recovery.recover bound.peakHeadSize ≤ width)
    (hstate : bound.peakStateSize ≤ routeWidth) (hhead : bound.peakHeadSize ≤ routeWidth)
    (hsample : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hcallerTick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ callerTickTime)
    (hextractionTick : ∀ n ≤ cap,
      ∀ encoded ≤ 7 * extractionWidth (terminalInputWidth width outputWidth cap) cap outputWidth cap,
      control.loop n encoded ≤ extractionTickTime)
    (g X : G₁) (g₂ pk : G₂)
    (hi : Q.size (rep.env inputTypes) (g, X, g₂, pk, ()) ≤ inputWidth) :
    Bounds control queryCost (goodProgram rep bd ports sampler boundary data cost primitive sampling R fuel)
      (fun input => input = (g, X, g₂, pk, ())) (fun out => Q.size (rep.ty scalar) out ≤ width)
      (goodProgramTime overhead bound inputWidth width outputWidth routeWidth cap fuel comparisonTime
        scalarTime opTime handlerAdapterTime solverAdapterTime dynamicTime callerTickTime extractionTickTime) := by
  let W := programJoinWidth inputWidth width routeWidth cap
  let initialized := fun p : G₂ × (storeTy scalar goodConfigTy).Value (cryptoBase F G₁ G₂ M M) =>
    Q.size bd.input p.1 ≤ routeWidth ∧ ReservedState (Q := Q) rep width cap fuel p.2
  let ready := fun p : Option ((AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M)) ×
      (storeTy scalar goodConfigTy).Value (cryptoBase F G₁ G₂ M M) =>
    ResultReady (Q := Q) bd routeWidth p.1 ∧ ReservedState (Q := Q) rep width cap 0 p.2
  let post := fun out : F => Q.size (rep.ty scalar) out ≤ width
  have hsetup₀ := setupGood_bound (iface := iface) rep bd boundary data cost primitive control queryCost
    sizes lists laws dataLaws primitiveBound mono routing inputWidth width outputWidth routeWidth cap
    solverAdapterTime hh values.unit values.scalar values.point₁ values.point₂ solverCaps
    g X g₂ pk hi
  have hsetup : Bounds control queryCost
      (setupGood (iface := iface) rep bd boundary data cost primitive)
      (fun input => input = (g, X, g₂, pk, ())) initialized
      (solverAdapterTime + 70 * overhead (128 * setupWidth inputWidth width routeWidth cap)) := by
    intro input hp z hz
    obtain ⟨hzValue, ht⟩ := hsetup₀ input hp z hz
    rw [hzValue]
    exact ⟨⟨(solverCaps.key _ (values.point₂ _)).1,
      initial_reserved rep scalar goodConfigTy width cap fuel hcap (g, X)⟩, ht⟩
  have hcaller : Bounds control queryCost
      (goodCaller rep bd ports sampler data cost primitive sampling R fuel) initialized ready
      (SignatureHandler.callerTime overhead routeWidth fuel (bound.work + 2 * bound.queries + 2)
        (fun _ => bound.queries)
        (goodHandlerTime overhead width cap comparisonTime scalarTime opTime opTime handlerAdapterTime dynamicTime)
        callerTickTime) := by
    intro input hp z hz
    have hc := goodCaller_bound_of_resources rep bd ports sampler data cost primitive sampling control queryCost
      sizes lists laws dataLaws primitiveBound mono routing dispatch R bound hrun recovery
      width cap routeWidth fuel callerTickTime comparisonTime scalarTime opTime opTime handlerAdapterTime dynamicTime
      hh values.unit values.bool values.scalar values.point₁ hroute
      (fun x y hx hy => ops.messageEq x y (hx.trans hhandlerComparison) (hy.trans hhandlerComparison))
      hsample ops.zero ops.scale₁ handlerCaps dynamicSamples hrequest hstate hhead hcallerTick
      input.1 input.2 hp.2 hp.1 z hz
    refine ⟨⟨?_, hc.1.1⟩, hc.2⟩
    intro out hout
    exact (SignatureHandler.caller_output_size_of_resources rep bd ports sampler
      (rep.ty (storeTy scalar goodConfigTy)) (backendGoodReply rep data cost primitive sampling)
      control queryCost R bound hrun sizes fuel input.1 input.2 z hz out hout).trans hhead
  have hterminal := goodTerminal_bound rep bd boundary data cost primitive sampling control queryCost
    sizes lists lengths laws dataLaws primitiveBound mono routing dispatch
    width outputWidth routeWidth cap messageWidth comparisonTime scalarTime opTime solverAdapterTime extractionTickTime
    hh values ops solverCaps hcomparison hsample hextractionTick
  have hinitial : ∀ p, initialized p →
      Q.size (StepClass.HasProd.prod bd.input (rep.ty (storeTy scalar goodConfigTy))) p ≤ W := by
    intro p hp
    have hs := goodReserved_size rep sizes lists width cap fuel hh values.scalar values.point₁ p.2 hp.2
    have hg := sizes.prod_le bd.input (rep.ty (storeTy scalar goodConfigTy)) p
    have hk := hp.1
    dsimp [W, programJoinWidth]
    omega
  have hready : ∀ p, ready p →
      Q.size (Caller.result (bd := bd) (rep.ty (storeTy scalar goodConfigTy))) p ≤ W := by
    intro p hp
    have hs := goodReserved_size rep sizes lists width cap 0 hh values.scalar values.point₁ p.2 hp.2
    have hg := sizes.prod_le (StepClass.HasOption.option bd.out) (rep.ty (storeTy scalar goodConfigTy)) p
    have ho : Q.size (StepClass.HasOption.option bd.out) p.1 ≤ routeWidth + header := by
      cases he : p.1 with
      | none => exact (sizes.none_le bd.out).trans (by omega)
      | some out =>
        have hr := hp.1 out he
        exact (sizes.some_le bd.out out).trans (by omega)
    change Q.size (StepClass.HasProd.prod (StepClass.HasOption.option bd.out)
      (rep.ty (storeTy scalar goodConfigTy))) p ≤ W
    dsimp [W, programJoinWidth]
    omega
  have hremaining := seq_bound_of_width mono control queryCost routing _ _ initialized ready post W _ _
    hinitial hready hcaller hterminal
  have hfull := seq_bound_of_width mono control queryCost routing _ _
    (fun input => input = (g, X, g₂, pk, ())) initialized post W _ _
    (by intro input he; subst input; exact hi.trans (by dsimp [W, programJoinWidth]; omega))
    hinitial hsetup hremaining
  intro input hp z hz
  have h := hfull input hp z hz
  refine ⟨h.1, ?_⟩
  dsimp only [goodProgramTime, W] at *
  omega

theorem badProgram_bound
    (inputWidth width outputWidth routeWidth cap fuel messageWidth comparisonTime scalarTime opTime
      handlerAdapterTime solverAdapterTime dynamicTime callerTickTime extractionTickTime : Nat)
    (hh : header ≤ width) (hcap : fuel ≤ cap)
    (values : ValueCaps (Q := Q) rep width cap)
    (ops : OperationCaps rep cost primitive primitiveBound cap messageWidth opTime comparisonTime)
    (handlerCaps : SignatureHandler.PortCaps rep bd ports width handlerAdapterTime)
    (solverCaps : PortCaps rep bd boundary width outputWidth routeWidth solverAdapterTime)
    (dynamicSamples : SignatureHandler.DynamicSamplingCaps rep bd ports sampler control queryCost width dynamicTime)
    (hroute : handlerStoreWidth width cap ≤ routeWidth)
    (hhandlerComparison : 15 * handlerStoreWidth width cap ≤ messageWidth)
    (hcomparison : 3 * extractionWidth (terminalInputWidth width outputWidth cap) cap outputWidth cap ≤ messageWidth)
    (hrequest : recovery.recover bound.peakHeadSize ≤ width)
    (hstate : bound.peakStateSize ≤ routeWidth) (hhead : bound.peakHeadSize ≤ routeWidth)
    (hsample : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hcallerTick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ callerTickTime)
    (hextractionTick : ∀ n ≤ cap,
      ∀ encoded ≤ 7 * extractionWidth (terminalInputWidth width outputWidth cap) cap outputWidth cap,
      control.loop n encoded ≤ extractionTickTime)
    (g X : G₁) (g₂ pk : G₂)
    (hi : Q.size (rep.env inputTypes) (g, X, g₂, pk, ()) ≤ inputWidth) :
    Bounds control queryCost (badProgram rep bd ports sampler boundary data cost primitive sampling R fuel)
      (fun input => input = (g, X, g₂, pk, ())) (fun out => Q.size (rep.ty scalar) out ≤ width)
      (badProgramTime overhead bound inputWidth width outputWidth routeWidth cap fuel comparisonTime
        scalarTime opTime handlerAdapterTime solverAdapterTime dynamicTime callerTickTime extractionTickTime) := by
  let W := programJoinWidth inputWidth width routeWidth cap
  let initialized := fun p : G₂ × (storeTy (.pair scalar scalar) badConfigTy).Value (cryptoBase F G₁ G₂ M M) =>
    Q.size bd.input p.1 ≤ routeWidth ∧ ReservedState (Q := Q) rep width cap fuel p.2
  let ready := fun p : Option ((AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M)) ×
      (storeTy (.pair scalar scalar) badConfigTy).Value (cryptoBase F G₁ G₂ M M) =>
    ResultReady (Q := Q) bd routeWidth p.1 ∧ ReservedState (Q := Q) rep width cap 0 p.2
  let post := fun out : F => Q.size (rep.ty scalar) out ≤ width
  have hsetup₀ := setupBad_bound rep bd boundary data cost primitive sampling control queryCost
    sizes lists laws dataLaws primitiveBound mono routing inputWidth width outputWidth routeWidth cap
    solverAdapterTime scalarTime opTime hh values.unit values.scalar values.point₁ values.point₂ solverCaps
    hsample ops.scale₂ g X g₂ pk hi
  have hsetup : Bounds control queryCost
      (setupBad rep bd boundary data cost primitive sampling)
      (fun input => input = (g, X, g₂, pk, ())) initialized
      (scalarTime + opTime + solverAdapterTime + 112 * overhead (512 * setupWidth inputWidth width routeWidth cap)) := by
    intro input hp z hz
    obtain ⟨hzValue, ht⟩ := hsetup₀ input hp z hz
    obtain ⟨kappa, hzValue⟩ := hzValue
    rw [hzValue]
    exact ⟨⟨(solverCaps.key _ (values.point₂ _)).1,
      initial_reserved rep (.pair scalar scalar) badConfigTy width cap fuel hcap (kappa, g, X)⟩, ht⟩
  have hcaller : Bounds control queryCost
      (badCaller rep bd ports sampler data cost primitive sampling R fuel) initialized ready
      (SignatureHandler.callerTime overhead routeWidth fuel (bound.work + 2 * bound.queries + 2)
        (fun _ => bound.queries)
        (badHandlerTime overhead width cap comparisonTime scalarTime opTime opTime opTime handlerAdapterTime dynamicTime)
        callerTickTime) := by
    intro input hp z hz
    have hc := badCaller_bound_of_resources rep bd ports sampler data cost primitive sampling control queryCost
      sizes lists laws dataLaws primitiveBound mono routing dispatch R bound hrun recovery
      width cap routeWidth fuel callerTickTime comparisonTime scalarTime opTime opTime opTime handlerAdapterTime dynamicTime
      hh values.unit values.bool values.scalar values.point₁ hroute
      (fun x y hx hy => ops.messageEq x y (hx.trans hhandlerComparison) (hy.trans hhandlerComparison))
      hsample ops.zero ops.scale₁ ops.groupAdd handlerCaps dynamicSamples hrequest hstate hhead hcallerTick
      input.1 input.2 hp.2 hp.1 z hz
    refine ⟨⟨?_, hc.1.1⟩, hc.2⟩
    intro out hout
    exact (SignatureHandler.caller_output_size_of_resources rep bd ports sampler
      (rep.ty (storeTy (.pair scalar scalar) badConfigTy)) (backendBadReply rep data cost primitive sampling)
      control queryCost R bound hrun sizes fuel input.1 input.2 z hz out hout).trans hhead
  have hterminal := badTerminal_bound rep bd boundary data cost primitive sampling control queryCost
    sizes lists lengths laws dataLaws primitiveBound mono routing dispatch
    width outputWidth routeWidth cap messageWidth comparisonTime scalarTime opTime solverAdapterTime extractionTickTime
    hh values ops solverCaps hcomparison hsample hextractionTick
  have hinitial : ∀ p, initialized p →
      Q.size (StepClass.HasProd.prod bd.input (rep.ty (storeTy (.pair scalar scalar) badConfigTy))) p ≤ W := by
    intro p hp
    have hs := badReserved_size rep sizes lists width cap fuel hh values.scalar values.point₁ p.2 hp.2
    have hg := sizes.prod_le bd.input (rep.ty (storeTy (.pair scalar scalar) badConfigTy)) p
    have hk := hp.1
    dsimp [W, programJoinWidth]
    omega
  have hready : ∀ p, ready p →
      Q.size (Caller.result (bd := bd) (rep.ty (storeTy (.pair scalar scalar) badConfigTy))) p ≤ W := by
    intro p hp
    have hs := badReserved_size rep sizes lists width cap 0 hh values.scalar values.point₁ p.2 hp.2
    have hg := sizes.prod_le (StepClass.HasOption.option bd.out) (rep.ty (storeTy (.pair scalar scalar) badConfigTy)) p
    have ho : Q.size (StepClass.HasOption.option bd.out) p.1 ≤ routeWidth + header := by
      cases he : p.1 with
      | none => exact (sizes.none_le bd.out).trans (by omega)
      | some out =>
        have hr := hp.1 out he
        exact (sizes.some_le bd.out out).trans (by omega)
    change Q.size (StepClass.HasProd.prod (StepClass.HasOption.option bd.out)
      (rep.ty (storeTy (.pair scalar scalar) badConfigTy))) p ≤ W
    dsimp [W, programJoinWidth]
    omega
  have hremaining := seq_bound_of_width mono control queryCost routing _ _ initialized ready post W _ _
    hinitial hready hcaller hterminal
  have hfull := seq_bound_of_width mono control queryCost routing _ _
    (fun input => input = (g, X, g₂, pk, ())) initialized post W _ _
    (by intro input he; subst input; exact hi.trans (by dsimp [W, programJoinWidth]; omega))
    hinitial hsetup hremaining
  intro input hp z hz
  have h := hfull input hp z hz
  refine ⟨h.1, ?_⟩
  dsimp only [badProgramTime, W] at *
  omega

end Signatures.Runtime.LazyAGM.NativeSolver
