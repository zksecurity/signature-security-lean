import Proofs.Runtime.BackendCoronSolverSetup

/-! Complete native challenge-to-output runtime. The bound includes the caller's
measured local work, every implemented query, initialization, terminal extraction,
and composition costs. No runtime premise concerns the complete reduction. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Coron.NativeSolver

open BackendProgram ReplyCompiler

def nativeSolverTime (overhead : Nat → Nat)
    (inputWidth width routeWidth cap fuel localTime tickTime : Nat) (queries : Fin 3 → Nat)
    (comparisonTime scalarTime coinTime opTime handlerAdapterTime solverAdapterTime dynamicTime : Nat) : Nat :=
  localTime + (∑ k, queries k * NativeHandler.nativeHandlerTime overhead width cap comparisonTime
    scalarTime coinTime opTime handlerAdapterTime dynamicTime) +
  3 * overhead (32 * routeWidth) + (fuel + 1) * (42 * overhead (32 * routeWidth) + tickTime) +
  FinishCompiler.nativeFinishTime overhead width cap comparisonTime scalarTime coinTime opTime +
  opTime + 3 * solverAdapterTime +
  100 * overhead (32 * (inputWidth + routeWidth + writtenStoreWidth width cap))

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
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂ (M × G₁))
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (mono : Monotone overhead) (routing : RoutingCostLaws control overhead)
  (localLaws : LocalCostLaws Q overhead) (dispatchLaws : DispatchCostLaws (Q := Q) overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

include sizes lists mono routing localLaws dispatchLaws dataLaws

set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] PFunctor.Idx

theorem program_bound
    (qS inputWidth messageWidth width scalarWidth coinWidth groupWidth cap routeWidth fuel localTime tickTime : Nat)
    (queries : Fin 3 → Nat)
    (comparisonTime scalarTime coinTime opTime handlerAdapterTime solverAdapterTime dynamicTime : Nat)
    (hh : header ≤ width) (hm : messageWidth ≤ width) (hroute : 8 * width ≤ routeWidth) (hcap : fuel ≤ cap)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ scalarWidth)
    (hc : ∀ x : Fin (qS + 1), Q.size (rep.ty (boundedNat qS)) x ≤ coinWidth)
    (hg : ∀ x : G₁, Q.size (rep.ty point₁) x ≤ groupWidth)
    (hw : storeWidth header messageWidth scalarWidth coinWidth groupWidth cap ≤ width)
    (handlerCaps : NativeHandler.PortCaps rep bd ports width handlerAdapterTime)
    (solverCaps : PortCaps rep bd boundary inputWidth routeWidth solverAdapterTime)
    (dynamicSamples : NativeHandler.DynamicSamplingCaps rep bd ports sampler control queryCost width dynamicTime)
    (values : NativeValueCaps (Q := Q) rep qS width)
    (ops : NativeInstructionCaps rep cost primitive primitiveBound qS width comparisonTime opTime)
    (samples : NativeSamplingCaps rep samplingCode control queryCost qS scalarTime coinTime)
    (callerInv : Nat → R.machine.State → Prop)
    (hcallerStep : ∀ n state, callerInv (n + 1) state → ∀ i next,
      R.machine.view state = .inr ⟨i, next⟩ →
        NativeHandler.RequestSized (Q := Q) rep width i ∧
        NativeHandler.RequestMessages (fun m => Q.size (rep.ty message) m ≤ messageWidth) i ∧
        ∀ reply, callerInv n (next reply))
    (hcallerWidth : ∀ n state, callerInv n state →
      Q.size R.state state ≤ routeWidth ∧ Q.size bd.head (R.machine.head state) ≤ routeWidth)
    (hmessage : ∀ n state, callerInv n state → ∀ out, R.machine.view state = .inl out →
      Q.size (rep.ty message) out.1 ≤ messageWidth)
    (htick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ tickTime)
    (g : G₁) (g₂ : G₂) (X : G₁) (pk : G₂) (h : G₁)
    (hi : Q.size (rep.env inputTypes) (g, g₂, X, pk, h, ()) ≤ inputWidth)
    (hiCaller : callerInv fuel (R.machine.init pk))
    (hbudget : GeneralCaller.Budget R (generalReplies M G₁ randomBound) generalKind fuel pk localTime queries) :
    Bounds control queryCost (program rep bd ports sampler boundary data samplingCode cost primitive R qS fuel)
      (fun input => input = (g, g₂, X, pk, h, ())) (fun out => Q.size (rep.ty point₁) out ≤ width)
      (nativeSolverTime overhead inputWidth width routeWidth cap fuel localTime tickTime queries
        comparisonTime scalarTime coinTime opTime handlerAdapterTime solverAdapterTime dynamicTime) := by
  let saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M) :=
    machineState g X h (CacheState.empty : CacheState F M qS)
  let W := inputWidth + routeWidth + writtenStoreWidth width cap
  let fee := overhead (32 * W)
  let initialized := fun p : G₂ × (machineStore qS).Value (cryptoBase F G₁ G₂ M M) => p = (pk, saved)
  let terminalPre := fun p : Option (M × G₁) × (machineStore qS).Value (cryptoBase F G₁ G₂ M M) =>
    ResultReady (Q := Q) rep bd width routeWidth p.1 ∧ StateInvariant (Q := Q) rep qS width width cap p.2
  let post := fun out : G₁ => Q.size (rep.ty point₁) out ≤ width
  let callerTime := localTime + (∑ k, queries k * NativeHandler.nativeHandlerTime overhead width cap comparisonTime
    scalarTime coinTime opTime handlerAdapterTime dynamicTime) + 3 * overhead (32 * routeWidth) +
    (fuel + 1) * (42 * overhead (32 * routeWidth) + tickTime)
  let terminalTime := FinishCompiler.nativeFinishTime overhead width cap comparisonTime scalarTime coinTime opTime +
    opTime + 2 * solverAdapterTime + 20 * overhead (32 * terminalWidth width routeWidth cap)
  have hW : inputWidth + routeWidth + 8 * width ≤ W := by
    dsimp [W, writtenStoreWidth]; nlinarith
  have hs := initial_reserved rep sizes lists qS messageWidth width scalarWidth coinWidth groupWidth cap fuel
    hf hc hg hw hcap g X h
  have hk := (solverCaps.key pk ((input_key_size rep sizes g g₂ X pk h).trans hi)).1
  have hs0 : Q.size (rep.ty (machineStore qS)) saved ≤ width := hs.1
  have hsetup := setup_bound (iface := iface) rep sizes lists data cost primitive mono localLaws dataLaws
    primitiveBound bd boundary control queryCost routing qS inputWidth width routeWidth solverAdapterTime
    hh solverCaps g g₂ X pk h hi hs0
  have hcall : Bounds control queryCost
      (NativeHandler.caller rep bd ports sampler data samplingCode cost primitive R qS fuel)
      initialized terminalPre callerTime := by
    intro input he z hz
    change input = (pk, saved) at he
    subst input
    obtain ⟨hstate, ht⟩ := NativeHandler.caller_bound rep bd ports sampler data samplingCode cost primitive
      control queryCost sizes lists mono routing localLaws dispatchLaws dataLaws primitiveBound R
      qS messageWidth width scalarWidth coinWidth groupWidth cap routeWidth fuel localTime tickTime queries
      comparisonTime scalarTime coinTime opTime handlerAdapterTime dynamicTime hh hm hroute hf hc hg hw
      handlerCaps dynamicSamples values ops samples callerInv hcallerStep hcallerWidth htick pk saved hiCaller hs hk hbudget z hz
    refine ⟨⟨?_, StateInvariant.mono rep qS messageWidth width cap width width cap z.value.2 hstate hm le_rfl le_rfl⟩, ht⟩
    intro out ho
    have hb := caller_output_sizes rep bd ports sampler data samplingCode cost primitive control queryCost R
      callerInv (fun n state hs i next hv => (hcallerStep n state hs i next hv).2.2) sizes
      messageWidth routeWidth (fun n state hs => (hcallerWidth n state hs).2) hmessage qS fuel pk hiCaller saved z hz out ho
    exact ⟨hb.1, hb.2.trans hm⟩
  have hterminal := terminal_bound rep bd boundary data samplingCode cost primitive control queryCost sizes lists
    mono routing localLaws dispatchLaws dataLaws primitiveBound qS width routeWidth cap inputWidth comparisonTime
    scalarTime coinTime opTime solverAdapterTime hh solverCaps values ops samples
  have hp := sizes.prod_le bd.input (rep.ty (machineStore qS)) (pk, saved)
  have hremaining := Bounds.seq control queryCost _ _ initialized terminalPre post callerTime terminalTime fee
    hcall hterminal (by
      intro input hi value hv
      change input = (pk, saved) at hi
      subst input
      have hprod := sizes.prod_le (StepClass.HasOption.option bd.out) (rep.ty (machineStore qS)) value
      have hs' := hv.2.1
      have ho : Q.size (StepClass.HasOption.option bd.out) value.1 ≤ routeWidth + header := by
        cases he : value.1 with
        | none => exact (sizes.none_le bd.out).trans (by omega)
        | some out =>
            have hr := (hv.1 out he).1
            exact (sizes.some_le bd.out out).trans (by omega)
      exact (routing.sequence _ _).trans (mono (by
        change Q.size (StepClass.HasProd.prod bd.input (rep.ty (machineStore qS))) (pk, saved) +
          Q.size (StepClass.HasProd.prod (StepClass.HasOption.option bd.out) (rep.ty (machineStore qS))) value ≤ 32 * W
        dsimp only [terminalPre, Prod.fst, Prod.snd] at hp hs'
        omega)))
  have hb := Bounds.seq control queryCost _ _ (fun input => input = (g, g₂, X, pk, h, ()))
    initialized post _ _ fee hsetup hremaining (by
      intro input he value hv
      subst input
      change value = (pk, saved) at hv
      subst value
      exact (routing.sequence _ _).trans (mono (by
        dsimp only [Prod.fst, Prod.snd] at hp
        omega)))
  intro input he z hz
  obtain ⟨hout, ht⟩ := hb input he z hz
  have hsetupFee := mono (show 32 * (inputWidth + width + routeWidth) ≤ 32 * W by omega)
  have hterminalFee := mono (show 32 * terminalWidth width routeWidth cap ≤ 32 * W by
    dsimp [terminalWidth, W]; omega)
  dsimp only [fee, callerTime, terminalTime, nativeSolverTime, W] at *
  exact ⟨hout, by omega⟩

end Signatures.Runtime.Coron.NativeSolver
