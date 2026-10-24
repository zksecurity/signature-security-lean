import Proofs.Runtime.BackendWeightedSolverSetup
import Proofs.Runtime.BackendWeightedSolverTerminal
import Proofs.Runtime.BackendWeightedOracleCallerResources
import Proofs.Runtime.BackendWeightedCallerOutput
import Proofs.Runtime.BackendWeightedOracleCache

/-! Complete native AGM solver runtime bounds. Setup, the actual caller with
its measured resources, and extraction are composed with charged sequencing.
The only execution allowance for an adversary is its own `RunsWithin` bound;
no premise assumes the runtime of a completed solver or caller simulation. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.WeightedAGM.NativeSolver

open BackendProgram NativeHandler Reply

def programJoinWidth (index : Index) (inputWidth width routeWidth cap : Nat) : Nat :=
  inputWidth + 2 * routeWidth + handlerStoreWidth index width cap + 2 * width

def goodProgramTime (index : Index) (overhead : Nat → Nat) (bound : ExecutionCost)
    (inputWidth width outputWidth routeWidth cap fuel comparisonTime scalarTime opTime
      handlerAdapterTime solverAdapterTime dynamicTime handlerTickTime callerTickTime extractionTickTime : Nat) : Nat :=
  (solverAdapterTime + 70 * overhead (128 * setupWidth index inputWidth width routeWidth cap)) +
  SignatureHandler.callerTime overhead routeWidth fuel (bound.work + 2 * bound.queries + 2)
    (fun _ => bound.queries)
    (goodHandlerTime index overhead width cap opTime opTime opTime comparisonTime opTime scalarTime opTime opTime opTime handlerTickTime opTime opTime opTime opTime handlerAdapterTime dynamicTime)
    callerTickTime +
  goodTerminalTime index overhead width outputWidth routeWidth cap comparisonTime scalarTime opTime
    solverAdapterTime extractionTickTime +
  2 * overhead (32 * programJoinWidth index inputWidth width routeWidth cap)

def badProgramTime (index : Index) (overhead : Nat → Nat) (bound : ExecutionCost)
    (inputWidth width outputWidth routeWidth cap fuel comparisonTime scalarTime opTime
      handlerAdapterTime solverAdapterTime dynamicTime handlerTickTime callerTickTime extractionTickTime : Nat) : Nat :=
  (scalarTime + opTime + solverAdapterTime + 112 * overhead (512 * setupWidth index inputWidth width routeWidth cap)) +
  SignatureHandler.callerTime overhead routeWidth fuel (bound.work + 2 * bound.queries + 2)
    (fun _ => bound.queries)
    (badHandlerTime index overhead width cap opTime opTime opTime comparisonTime opTime scalarTime opTime opTime opTime handlerTickTime opTime opTime opTime opTime opTime handlerAdapterTime dynamicTime)
    callerTickTime +
  badTerminalTime index overhead width outputWidth routeWidth cap comparisonTime scalarTime opTime
    solverAdapterTime extractionTickTime +
  2 * overhead (32 * programJoinWidth index inputWidth width routeWidth cap)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (index : Index)
  (bd : Boundary C (generalSpec (index.ty.Value (cryptoBase F G₁ G₂ K M)) (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor G₂
    ((AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M)))
  (ports : NativePorts (Q := Q) rep index.ty index.messageTy bd) (sampler : BoundedSampler rep index.ty index.messageTy bd ports (iface := iface))
  (boundary : DataPorts (Q := Q) rep index bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
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
  (recovery : NativeHandler.RequestRecovery (Q := Q) rep index.ty index.messageTy bd)

  (sourceProgram : G₂ → OracleComp (generalSpec (index.ty.Value (cryptoBase F G₁ G₂ K M))
    (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound)
    ((AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M)))
  (hprogram : R.machine.Implements sourceProgram)

include sizes lists lengths laws dataLaws primitiveBound mono routing dispatch hrun recovery hprogram

attribute [local implicit_reducible] PFunctor.Idx

theorem goodProgram_bound
    (inputWidth width outputWidth routeWidth cap fuel keyWidth comparisonTime scalarTime opTime
      handlerAdapterTime solverAdapterTime dynamicTime handlerTickTime callerTickTime extractionTickTime : Nat)
    (hh : header ≤ width) (hcap : fuel ≤ cap) (hfuel : bound.queries ≤ fuel)
    (values : ValueCaps (Q := Q) rep index width cap)
    (ops : OperationCaps rep index cost primitive primitiveBound cap keyWidth opTime comparisonTime)
    (handlerCaps : NativeHandler.PortCaps rep index.ty index.messageTy bd ports width handlerAdapterTime)
    (solverCaps : PortCaps rep index bd boundary width outputWidth routeWidth solverAdapterTime)
    (dynamicSamples : NativeHandler.DynamicSamplingCaps rep index.ty index.messageTy bd ports sampler control queryCost width dynamicTime)
    (hroute : handlerStoreWidth index width cap ≤ routeWidth)
    (hhandlerComparison : Reply.goodSignEvaluationWidth index (handlerStoreWidth index width cap) (cap * (index.bound + 1)) ≤ keyWidth)
    (hcomparison : 3 * Extract.extractionWidth index (extractionEntryWidth width cap outputWidth) cap cap outputWidth (cap * (index.bound + 1)) ≤ keyWidth)
    (hrequest : recovery.recover bound.peakHeadSize ≤ width)
    (hstate : bound.peakStateSize ≤ routeWidth) (hhead : bound.peakHeadSize ≤ routeWidth)
    (hsample : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hcallerTick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ callerTickTime)
    (hhandlerTick : ∀ n ≤ index.bound + 1, ∀ encoded ≤ 7 * Reply.goodSignEvaluationWidth index
      (handlerStoreWidth index width cap) (cap * (index.bound + 1)), control.loop n encoded ≤ handlerTickTime)
    (hextractionTick : ∀ n ≤ rowCap index cap,
      ∀ encoded ≤ 7 * Extract.extractionWidth index (extractionEntryWidth width cap outputWidth) cap cap outputWidth (cap * (index.bound + 1)),
      control.loop n encoded ≤ extractionTickTime)
    (g X : G₁) (g₂ pk : G₂)
    (hi : Q.size (rep.env inputTypes) (g, X, g₂, pk, ()) ≤ inputWidth) :
    Bounds control queryCost (goodProgram rep index bd ports sampler boundary data cost primitive sampling R fuel)
      (fun input => input = (g, X, g₂, pk, ())) (fun out => Q.size (rep.ty scalar) out ≤ width)
      (goodProgramTime index overhead bound inputWidth width outputWidth routeWidth cap fuel comparisonTime
        scalarTime opTime handlerAdapterTime solverAdapterTime dynamicTime handlerTickTime callerTickTime extractionTickTime) := by
  let W := programJoinWidth index inputWidth width routeWidth cap
  let initialized := fun p : G₂ × (Reply.storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy).Value (cryptoBase F G₁ G₂ K M) =>
    Q.size bd.input p.1 ≤ routeWidth ∧ ReservedState (Q := Q) rep index width cap fuel p.2 ∧ p.2.2.2 = ([], [])
  let ready := fun p : Option ((AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M)) ×
      (Reply.storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy).Value (cryptoBase F G₁ G₂ K M) =>
    ResultReady (Q := Q) index bd routeWidth p.1 ∧ ExtractionReady (Q := Q) rep index cost scalar LazyAGM.goodConfigTy width cap p.2
  let post := fun out : F => Q.size (rep.ty scalar) out ≤ width
  have hsetup₀ := setupGood_bound (iface := iface) rep index bd boundary data cost primitive control queryCost
    sizes lists laws dataLaws primitiveBound mono routing inputWidth width outputWidth routeWidth cap
    solverAdapterTime hh values.unit values.scalar values.point₁ values.point₂ solverCaps
    g X g₂ pk hi
  have hsetup : Bounds control queryCost
      (setupGood (iface := iface) rep index bd boundary data cost primitive)
      (fun input => input = (g, X, g₂, pk, ())) initialized
      (solverAdapterTime + 70 * overhead (128 * setupWidth index inputWidth width routeWidth cap)) := by
    intro input hp z hz
    obtain ⟨hzValue, ht⟩ := hsetup₀ input hp z hz
    rw [hzValue]
    exact ⟨⟨(solverCaps.key _ (values.point₂ _)).1,
      initial_reserved rep index scalar LazyAGM.goodConfigTy width cap fuel hcap (g, X), rfl⟩, ht⟩
  have hcaller : Bounds control queryCost
      (goodCaller rep index bd ports sampler data cost primitive sampling R fuel) initialized ready
      (SignatureHandler.callerTime overhead routeWidth fuel (bound.work + 2 * bound.queries + 2)
        (fun _ => bound.queries)
        (goodHandlerTime index overhead width cap opTime opTime opTime comparisonTime opTime scalarTime opTime opTime opTime handlerTickTime opTime opTime opTime opTime handlerAdapterTime dynamicTime)
        callerTickTime) := by
    intro input hp z hz
    have hc := goodCaller_bound_of_resources rep index bd ports sampler data cost primitive sampling control queryCost
      sizes lists laws dataLaws primitiveBound mono routing dispatch R bound hrun recovery
      width cap routeWidth fuel callerTickTime opTime opTime opTime comparisonTime opTime scalarTime opTime opTime opTime
      handlerTickTime opTime opTime opTime opTime handlerAdapterTime dynamicTime
      hh values.unit values.bool values.scalar values.point₁ hroute values.index
      (fun n hn => values.nat n (by dsimp [rowCap]; omega))
      (fun j k hj hk => ops.natEq j k (by dsimp [rowCap]; omega) (by dsimp [rowCap]; omega))
      (fun n hn => ops.natSub n (by dsimp [rowCap]; omega)) (fun n hn => ops.natAdd n (by dsimp [rowCap]; omega))
      (fun x y hx hy => ops.keyEq x y (hx.trans hhandlerComparison) (hy.trans hhandlerComparison))
      ops.finVal hsample ops.zero ops.add ops.mul hhandlerTick ops.finOfNat ops.finZero ops.one ops.scale₁
      handlerCaps dynamicSamples hrequest hstate hhead hcallerTick input.1 input.2 hp.2.1 hp.1 z hz
    have hcache := goodCaller_cached_of_resources rep index bd ports sampler data cost primitive sampling
      R bound hrun control queryCost fuel hfuel sourceProgram hprogram input.1 input.2.1.1 input.2.1.2 input.2.2
      (by simp [hp.2.2, Model.LazyAGM.WeightedReduction.TranscriptCached, chronological]) z hz
    refine ⟨⟨?_, hc.1.1, hcache.2.2.2⟩, hc.2⟩
    intro out hout
    exact (NativeHandler.caller_output_size_of_resources rep index.ty index.messageTy bd ports sampler
      (rep.ty (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy))
      (Reply.goodHash rep data cost primitive sampling index) (Reply.goodSign rep data cost primitive sampling index)
      control queryCost R bound hrun sizes fuel input.1 input.2 z hz out hout).trans hhead
  have hterminal := goodTerminal_bound rep index bd boundary data cost primitive sampling control queryCost
    sizes lists lengths laws dataLaws primitiveBound mono routing dispatch
    width outputWidth routeWidth cap keyWidth comparisonTime scalarTime opTime solverAdapterTime extractionTickTime
    hh values ops solverCaps hcomparison hsample hextractionTick
  have hinitial : ∀ p, initialized p →
      Q.size (StepClass.HasProd.prod bd.input (rep.ty (Reply.storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy))) p ≤ W := by
    intro p hp
    have hs := goodReserved_size rep index sizes lists width cap fuel hh values.scalar values.point₁ p.2 hp.2.1
    have hg := sizes.prod_le bd.input (rep.ty (Reply.storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy)) p
    have hk := hp.1
    dsimp [W, programJoinWidth]
    omega
  have hready : ∀ p, ready p →
      Q.size (Caller.result (bd := bd) (rep.ty (Reply.storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy))) p ≤ W := by
    intro p hp
    have hs := goodReserved_size rep index sizes lists width cap 0 hh values.scalar values.point₁ p.2 hp.2.1
    have hg := sizes.prod_le (StepClass.HasOption.option bd.out) (rep.ty (Reply.storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy)) p
    have ho : Q.size (StepClass.HasOption.option bd.out) p.1 ≤ routeWidth + header := by
      cases he : p.1 with
      | none => exact (sizes.none_le bd.out).trans (by omega)
      | some out =>
        have hr := hp.1 out he
        exact (sizes.some_le bd.out out).trans (by omega)
    change Q.size (StepClass.HasProd.prod (StepClass.HasOption.option bd.out)
      (rep.ty (Reply.storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy))) p ≤ W
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
    (inputWidth width outputWidth routeWidth cap fuel keyWidth comparisonTime scalarTime opTime
      handlerAdapterTime solverAdapterTime dynamicTime handlerTickTime callerTickTime extractionTickTime : Nat)
    (hh : header ≤ width) (hcap : fuel ≤ cap) (hfuel : bound.queries ≤ fuel)
    (values : ValueCaps (Q := Q) rep index width cap)
    (ops : OperationCaps rep index cost primitive primitiveBound cap keyWidth opTime comparisonTime)
    (handlerCaps : NativeHandler.PortCaps rep index.ty index.messageTy bd ports width handlerAdapterTime)
    (solverCaps : PortCaps rep index bd boundary width outputWidth routeWidth solverAdapterTime)
    (dynamicSamples : NativeHandler.DynamicSamplingCaps rep index.ty index.messageTy bd ports sampler control queryCost width dynamicTime)
    (hroute : handlerStoreWidth index width cap ≤ routeWidth)
    (hhandlerComparison : 3 * Reply.badSignEvaluationWidth index (handlerStoreWidth index width cap) (cap * (index.bound + 1)) ≤ keyWidth)
    (hcomparison : 3 * Extract.extractionWidth index (extractionEntryWidth width cap outputWidth) cap cap outputWidth (cap * (index.bound + 1)) ≤ keyWidth)
    (hrequest : recovery.recover bound.peakHeadSize ≤ width)
    (hstate : bound.peakStateSize ≤ routeWidth) (hhead : bound.peakHeadSize ≤ routeWidth)
    (hsample : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hcallerTick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ callerTickTime)
    (hhandlerTick : ∀ n ≤ index.bound + 1, ∀ encoded ≤ 7 * Reply.badSignEvaluationWidth index
      (handlerStoreWidth index width cap) (cap * (index.bound + 1)), control.loop n encoded ≤ handlerTickTime)
    (hextractionTick : ∀ n ≤ rowCap index cap,
      ∀ encoded ≤ 7 * Extract.extractionWidth index (extractionEntryWidth width cap outputWidth) cap cap outputWidth (cap * (index.bound + 1)),
      control.loop n encoded ≤ extractionTickTime)
    (g X : G₁) (g₂ pk : G₂)
    (hi : Q.size (rep.env inputTypes) (g, X, g₂, pk, ()) ≤ inputWidth) :
    Bounds control queryCost (badProgram rep index bd ports sampler boundary data cost primitive sampling R fuel)
      (fun input => input = (g, X, g₂, pk, ())) (fun out => Q.size (rep.ty scalar) out ≤ width)
      (badProgramTime index overhead bound inputWidth width outputWidth routeWidth cap fuel comparisonTime
        scalarTime opTime handlerAdapterTime solverAdapterTime dynamicTime handlerTickTime callerTickTime extractionTickTime) := by
  let W := programJoinWidth index inputWidth width routeWidth cap
  let initialized := fun p : G₂ × (Reply.storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy).Value (cryptoBase F G₁ G₂ K M) =>
    Q.size bd.input p.1 ≤ routeWidth ∧ ReservedState (Q := Q) rep index width cap fuel p.2 ∧ p.2.2.2 = ([], [])
  let ready := fun p : Option ((AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M)) ×
      (Reply.storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy).Value (cryptoBase F G₁ G₂ K M) =>
    ResultReady (Q := Q) index bd routeWidth p.1 ∧ ExtractionReady (Q := Q) rep index cost (.pair scalar scalar) LazyAGM.badConfigTy width cap p.2
  let post := fun out : F => Q.size (rep.ty scalar) out ≤ width
  have hsetup₀ := setupBad_bound rep index bd boundary data cost primitive sampling control queryCost
    sizes lists laws dataLaws primitiveBound mono routing inputWidth width outputWidth routeWidth cap
    solverAdapterTime scalarTime opTime hh values.unit values.scalar values.point₁ values.point₂ solverCaps
    hsample ops.scale₂ g X g₂ pk hi
  have hsetup : Bounds control queryCost
      (setupBad rep index bd boundary data cost primitive sampling)
      (fun input => input = (g, X, g₂, pk, ())) initialized
      (scalarTime + opTime + solverAdapterTime + 112 * overhead (512 * setupWidth index inputWidth width routeWidth cap)) := by
    intro input hp z hz
    obtain ⟨hzValue, ht⟩ := hsetup₀ input hp z hz
    obtain ⟨kappa, hzValue⟩ := hzValue
    rw [hzValue]
    exact ⟨⟨(solverCaps.key _ (values.point₂ _)).1,
      initial_reserved rep index (.pair scalar scalar) LazyAGM.badConfigTy width cap fuel hcap (kappa, g, X), rfl⟩, ht⟩
  have hcaller : Bounds control queryCost
      (badCaller rep index bd ports sampler data cost primitive sampling R fuel) initialized ready
      (SignatureHandler.callerTime overhead routeWidth fuel (bound.work + 2 * bound.queries + 2)
        (fun _ => bound.queries)
        (badHandlerTime index overhead width cap opTime opTime opTime comparisonTime opTime scalarTime opTime opTime opTime handlerTickTime opTime opTime opTime opTime opTime handlerAdapterTime dynamicTime)
        callerTickTime) := by
    intro input hp z hz
    have hc := badCaller_bound_of_resources rep index bd ports sampler data cost primitive sampling control queryCost
      sizes lists laws dataLaws primitiveBound mono routing dispatch R bound hrun recovery
      width cap routeWidth fuel callerTickTime opTime opTime opTime comparisonTime opTime scalarTime opTime opTime opTime
      handlerTickTime opTime opTime opTime opTime opTime handlerAdapterTime dynamicTime
      hh values.unit values.bool values.scalar values.point₁ hroute values.index
      (fun n hn => values.nat n (by dsimp [rowCap]; omega))
      (fun j k hj hk => ops.natEq j k (by dsimp [rowCap]; omega) (by dsimp [rowCap]; omega))
      (fun n hn => ops.natSub n (by dsimp [rowCap]; omega)) (fun n hn => ops.natAdd n (by dsimp [rowCap]; omega))
      (fun x y hx hy => ops.keyEq x y (hx.trans hhandlerComparison) (hy.trans hhandlerComparison))
      ops.finVal hsample ops.zero ops.add ops.mul hhandlerTick ops.finOfNat ops.finZero ops.one ops.scale₁ ops.groupAdd
      handlerCaps dynamicSamples hrequest hstate hhead hcallerTick input.1 input.2 hp.2.1 hp.1 z hz
    have hcache := badCaller_cached_of_resources rep index bd ports sampler data cost primitive sampling
      R bound hrun control queryCost fuel hfuel sourceProgram hprogram input.1 input.2.1.2.1 input.2.1.2.2 input.2.1.1 input.2.2
      (by simp [hp.2.2, Model.LazyAGM.WeightedReduction.TranscriptCached, chronological]) z hz
    refine ⟨⟨?_, hc.1.1, hcache.2.2.2⟩, hc.2⟩
    intro out hout
    exact (NativeHandler.caller_output_size_of_resources rep index.ty index.messageTy bd ports sampler
      (rep.ty (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy))
      (Reply.badHash rep data cost primitive sampling index) (Reply.badSign rep data cost primitive sampling index)
      control queryCost R bound hrun sizes fuel input.1 input.2 z hz out hout).trans hhead
  have hterminal := badTerminal_bound rep index bd boundary data cost primitive sampling control queryCost
    sizes lists lengths laws dataLaws primitiveBound mono routing dispatch
    width outputWidth routeWidth cap keyWidth comparisonTime scalarTime opTime solverAdapterTime extractionTickTime
    hh values ops solverCaps hcomparison hsample hextractionTick
  have hinitial : ∀ p, initialized p →
      Q.size (StepClass.HasProd.prod bd.input (rep.ty (Reply.storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy))) p ≤ W := by
    intro p hp
    have hs := badReserved_size rep index sizes lists width cap fuel hh values.scalar values.point₁ p.2 hp.2.1
    have hg := sizes.prod_le bd.input (rep.ty (Reply.storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy)) p
    have hk := hp.1
    dsimp [W, programJoinWidth]
    omega
  have hready : ∀ p, ready p →
      Q.size (Caller.result (bd := bd) (rep.ty (Reply.storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy))) p ≤ W := by
    intro p hp
    have hs := badReserved_size rep index sizes lists width cap 0 hh values.scalar values.point₁ p.2 hp.2.1
    have hg := sizes.prod_le (StepClass.HasOption.option bd.out) (rep.ty (Reply.storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy)) p
    have ho : Q.size (StepClass.HasOption.option bd.out) p.1 ≤ routeWidth + header := by
      cases he : p.1 with
      | none => exact (sizes.none_le bd.out).trans (by omega)
      | some out =>
        have hr := hp.1 out he
        exact (sizes.some_le bd.out out).trans (by omega)
    change Q.size (StepClass.HasProd.prod (StepClass.HasOption.option bd.out)
      (rep.ty (Reply.storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy))) p ≤ W
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

end Signatures.Runtime.WeightedAGM.NativeSolver
