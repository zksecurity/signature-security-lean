import Proofs.Runtime.BackendCoronSolverOutput

/-! Native terminal costs, including optional-value inspection, forgery decoding,
final extraction, output projection, and the explicit cutoff branch. Encoding
contracts concern actual local data code; the extraction budget is derived from
its primitive contracts. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Coron.NativeSolver

open BackendProgram ReplyCompiler

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂ (M × G₁))
  (boundary : DataPorts (Q := Q) rep bd)

def ForgeryReady (width routeWidth : Nat) (out : M × G₁) : Prop :=
  Q.size bd.out out ≤ routeWidth ∧ Q.size (rep.ty message) out.1 ≤ width

def ResultReady (width routeWidth : Nat) (result : Option (M × G₁)) : Prop :=
  ∀ out, result = some out → ForgeryReady (Q := Q) rep bd width routeWidth out

structure PortCaps (inputWidth routeWidth adapterTime : Nat) : Prop where
  key : ∀ pk, Q.size (rep.ty point₂) pk ≤ inputWidth → Q.size bd.input pk ≤ routeWidth ∧
    Q.cost boundary.key pk ≤ adapterTime
  forgery : ∀ out, Q.size bd.out out ≤ routeWidth → Q.cost boundary.forgery out ≤ adapterTime
  optional : ∀ result, (∀ out, result = some out → Q.size bd.out out ≤ routeWidth) →
    Q.cost boundary.optional result ≤ adapterTime

def terminalWidth (width routeWidth cap : Nat) : Nat := routeWidth + writtenStoreWidth width cap

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  [Field F] [SampleableType F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
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

include sizes lists mono routing localLaws dataLaws

omit QO QD OC in
theorem finishSome_bound (qS width routeWidth cap inputWidth comparisonTime scalarTime coinTime opTime adapterTime : Nat)
    (hh : header ≤ width) (caps : PortCaps rep bd boundary inputWidth routeWidth adapterTime)
    (values : NativeValueCaps (Q := Q) rep qS width)
    (ops : NativeInstructionCaps rep cost primitive primitiveBound qS width comparisonTime opTime)
    (samples : NativeSamplingCaps rep samplingCode control queryCost qS scalarTime coinTime) :
    Bounds control queryCost (finishSome rep bd boundary data samplingCode cost primitive qS)
      (fun p => ForgeryReady (Q := Q) rep bd width routeWidth p.1 ∧ StateInvariant (Q := Q) rep qS width width cap p.2)
      (fun out => Q.size (rep.ty point₁) out ≤ width)
      (FinishCompiler.nativeFinishTime overhead width cap comparisonTime scalarTime coinTime opTime + adapterTime +
        6 * overhead (32 * terminalWidth width routeWidth cap)) := by
  let B := writtenStoreWidth width cap
  let W := terminalWidth width routeWidth cap
  let fee := overhead (32 * W)
  let inv := StateInvariant (Q := Q) rep qS width width cap
  let after := StateInvariant (Q := Q) rep qS width B (cap + 1)
  let pre := fun p : (M × G₁) × (machineStore qS).Value (cryptoBase F G₁ G₂ M M) =>
    ForgeryReady (Q := Q) rep bd width routeWidth p.1 ∧ inv p.2
  let decoded := fun p : (M × G₁) × (machineStore qS).Value (cryptoBase F G₁ G₂ M M) =>
    Q.size (rep.ty message) p.1.1 ≤ width ∧ inv p.2
  let finished := fun p : G₁ × (machineStore qS).Value (cryptoBase F G₁ G₂ M M) =>
    Q.size (rep.ty point₁) p.1 ≤ width ∧ after p.2
  have hB : 8 * width ≤ B := by dsimp [B, writtenStoreWidth]; nlinarith
  have hBW : B ≤ W := by dsimp [W, terminalWidth, B]; omega
  have hrW : routeWidth ≤ W := by dsimp [W, terminalWidth]; omega
  have hforgery : ∀ out : M × G₁, Q.size (rep.ty message) out.1 ≤ width →
      Q.size (rep.ty (.pair message point₁)) out ≤ 3 * width := by
    intro out hm
    have hp := sizes.prod_le (rep.ty message) (rep.ty point₁) out
    have hg := values.point out.2
    change Q.size (StepClass.HasProd.prod (rep.ty message) (rep.ty point₁)) out ≤ 3 * width
    omega
  have hd := firstAtomic_bound_of_width (iface := iface) mono control queryCost routing
    (rep.ty (machineStore qS)) boundary.forgery (ForgeryReady (Q := Q) rep bd width routeWidth)
    (fun out => Q.size (rep.ty message) out.1 ≤ width) inv W adapterTime
    (fun out ho => ho.1.trans hrW) (fun saved hs => hs.1.trans (by omega))
    (fun out ho => ⟨ho.2, (hforgery out ho.2).trans (by omega), caps.forgery out ho.1⟩)
  have hf := FinishCompiler.backendFinish_bound rep data samplingCode cost primitive localLaws dataLaws
    primitiveBound sizes lists mono control queryCost routing qS width cap comparisonTime scalarTime coinTime opTime hh values ops samples
  have hp : Bounds control queryCost (.atomic (iface := iface) (QP.fst (rep.ty point₁) (rep.ty (machineStore qS))))
      finished (fun out => Q.size (rep.ty point₁) out ≤ width) (2 * fee) := by
    apply Bounds.atomic
    intro p hs
    have hsize := sizes.prod_le (rep.ty point₁) (rep.ty (machineStore qS)) p
    have hg := hs.1
    have hw := hs.2.1
    have hc := localLaws.fst (rep.ty point₁) (rep.ty (machineStore qS)) p
    have hcall := routing.localCall
      (Q.size (StepClass.HasProd.prod (rep.ty point₁) (rep.ty (machineStore qS))) p) (Q.size (rep.ty point₁) p.1)
    have hn := mono (show Q.size (StepClass.HasProd.prod (rep.ty point₁) (rep.ty (machineStore qS))) p +
      Q.size (rep.ty point₁) p.1 ≤ 32 * W by dsimp only [finished, after] at *; omega)
    exact ⟨hs.1, by dsimp only [fee]; omega⟩
  have ht := Bounds.seq control queryCost _ _ decoded finished (fun out => Q.size (rep.ty point₁) out ≤ width)
    _ (2 * fee) fee hf hp (by
      intro input hi value hv
      have h1 := sizes.prod_le (rep.ty (.pair message point₁)) (rep.ty (machineStore qS)) input
      have h2 := sizes.prod_le (rep.ty point₁) (rep.ty (machineStore qS)) value
      have hm := hforgery input.1 hi.1
      have hs := hi.2.1
      have hg := hv.1
      have hw := hv.2.1
      exact (routing.sequence _ _).trans (mono (by dsimp only [decoded, finished, inv, after] at *; omega)))
  have h := Bounds.seq control queryCost _ _ pre decoded (fun out => Q.size (rep.ty point₁) out ≤ width)
    (adapterTime + 2 * fee) _ fee hd ht (by
      intro input hi value hv
      have h1 := sizes.prod_le bd.out (rep.ty (machineStore qS)) input
      have h2 := sizes.prod_le (rep.ty (.pair message point₁)) (rep.ty (machineStore qS)) value
      have hb := hi.1.1
      have hs := hi.2.1
      have hm := hforgery value.1 hv.1
      have hw := hv.2.1
      exact (routing.sequence _ _).trans (mono (by dsimp only [pre, decoded, inv, ForgeryReady] at *; omega)))
  intro input hi z hz
  obtain ⟨hout, htime⟩ := h input hi z hz
  dsimp only [fee, W] at *
  exact ⟨hout, by omega⟩

omit lists QO QD OC [SampleableType F] in
theorem cutoff_bound (qS width routeWidth cap comparisonTime opTime : Nat) (hh : header ≤ width)
    (values : NativeValueCaps (Q := Q) rep qS width)
    (ops : NativeInstructionCaps rep cost primitive primitiveBound qS width comparisonTime opTime) :
    Bounds control queryCost (cutoff (iface := iface) rep data cost primitive qS)
      (fun p => StateInvariant (Q := Q) rep qS width width cap p.2)
      (fun out => Q.size (rep.ty point₁) out ≤ width)
      (opTime + 3 * overhead (32 * terminalWidth width routeWidth cap)) := by
  intro input hi z hz
  simp only [cutoff, Code.run, support_pure, Set.mem_singleton_iff] at hz
  subst z
  have hlocal := (LocalBound.compose localLaws
    (dataLaws.unitBound (StepClass.HasProd.prod rep.data.unit (rep.ty (machineStore qS))))
    (primitiveBound CryptoOp.zero₁)).cost_le input
  have hp := sizes.prod_le rep.data.unit (rep.ty (machineStore qS)) input
  have hu : Q.size rep.data.unit input.1 ≤ width := by cases input.1; exact values.unit
  have hs := hi.1
  have hz := values.point (0 : G₁)
  have hu' := values.unit
  have ht := ops.pointZero
  have hcall := routing.localCall
    (Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty (machineStore qS))) input)
    (Q.size (rep.ty point₁) (0 : G₁))
  have hw : width ≤ terminalWidth width routeWidth cap := by
    dsimp [terminalWidth, writtenStoreWidth]; nlinarith
  dsimp only [LocalBound.compose, DataCostLaws.unitBound] at hlocal
  change Q.cost (Q.compose (data.unit (StepClass.HasProd.prod rep.data.unit (rep.ty (machineStore qS))))
    (primitive CryptoOp.zero₁)) input ≤
      overhead (Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty (machineStore qS))) input + Q.size rep.data.unit ()) +
      (primitiveBound CryptoOp.zero₁).time () +
      overhead (Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty (machineStore qS))) input +
        Q.size rep.data.unit () + Q.size (rep.ty point₁) (0 : G₁)) at hlocal
  have h1 := mono (show Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty (machineStore qS))) input +
    Q.size rep.data.unit () ≤ 32 * terminalWidth width routeWidth cap by omega)
  have h2 := mono (show Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty (machineStore qS))) input +
    Q.size rep.data.unit () + Q.size (rep.ty point₁) (0 : G₁) ≤ 32 * terminalWidth width routeWidth cap by omega)
  have h3 := mono (show Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty (machineStore qS))) input +
    Q.size (rep.ty point₁) (0 : G₁) ≤ 32 * terminalWidth width routeWidth cap by omega)
  refine ⟨hz, ?_⟩
  change Q.cost (Q.compose (data.unit (StepClass.HasProd.prod rep.data.unit (rep.ty (machineStore qS))))
      (primitive CryptoOp.zero₁)) input +
    control.localCall (Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty (machineStore qS))) input)
      (Q.size (rep.ty point₁) (0 : G₁)) ≤ _
  omega

include dispatchLaws in
theorem terminal_bound (qS width routeWidth cap inputWidth comparisonTime scalarTime coinTime opTime adapterTime : Nat)
    (hh : header ≤ width) (caps : PortCaps rep bd boundary inputWidth routeWidth adapterTime)
    (values : NativeValueCaps (Q := Q) rep qS width)
    (ops : NativeInstructionCaps rep cost primitive primitiveBound qS width comparisonTime opTime)
    (samples : NativeSamplingCaps rep samplingCode control queryCost qS scalarTime coinTime) :
    Bounds control queryCost (terminal rep bd boundary data samplingCode cost primitive qS)
      (fun p => ResultReady (Q := Q) rep bd width routeWidth p.1 ∧ StateInvariant (Q := Q) rep qS width width cap p.2)
      (fun out => Q.size (rep.ty point₁) out ≤ width)
      (FinishCompiler.nativeFinishTime overhead width cap comparisonTime scalarTime coinTime opTime +
        opTime + 2 * adapterTime + 20 * overhead (32 * terminalWidth width routeWidth cap)) := by
  let W := terminalWidth width routeWidth cap
  let fee := overhead (32 * W)
  let inv := StateInvariant (Q := Q) rep qS width width cap
  let ready := ForgeryReady (Q := Q) rep bd width routeWidth
  let viewed : Unit ⊕ (M × G₁) → Prop := Sum.elim (fun _ => True) ready
  let pre := fun p : Option (M × G₁) × (machineStore qS).Value (cryptoBase F G₁ G₂ M M) =>
    ResultReady (Q := Q) rep bd width routeWidth p.1 ∧ inv p.2
  let middle := fun p : (Unit ⊕ (M × G₁)) × (machineStore qS).Value (cryptoBase F G₁ G₂ M M) =>
    viewed p.1 ∧ inv p.2
  let post := fun out : G₁ => Q.size (rep.ty point₁) out ≤ width
  have hW : routeWidth + 8 * width ≤ W := by dsimp [W, terminalWidth, writtenStoreWidth]; nlinarith
  have hiSize : ∀ result, ResultReady (Q := Q) rep bd width routeWidth result →
      Q.size (StepClass.HasOption.option bd.out) result ≤ W := by
    intro result hr
    cases result with
    | none => exact (sizes.none_le bd.out).trans (by omega)
    | some out =>
        have ho := (hr out rfl).1
        have hs := sizes.some_le bd.out out
        omega
  have hvSize : ∀ value, viewed value → Q.size (StepClass.HasSum.sum rep.data.unit bd.out) value ≤ W := by
    intro value hv
    have hs := sizes.sum_le rep.data.unit bd.out value
    cases value with
    | inl u =>
        have hu : Q.size rep.data.unit u ≤ width := by cases u; exact values.unit
        dsimp only [Sum.elim_inl] at hs
        omega
    | inr out => have ho := hv.1; dsimp only [Sum.elim_inr] at hs; omega
  have hd := firstAtomic_bound_of_width (iface := iface) mono control queryCost routing
    (rep.ty (machineStore qS)) boundary.optional (ResultReady (Q := Q) rep bd width routeWidth)
    viewed inv W adapterTime hiSize (fun saved hs => hs.1.trans (by omega)) (by
      intro result hr
      have hv : viewed (optionView result) := by
        cases result with
        | none => trivial
        | some out => exact hr out rfl
      exact ⟨hv, hvSize _ hv, caps.optional result (fun out ho => (hr out ho).1)⟩)
  have hl := cutoff_bound (iface := iface) rep data cost primitive control queryCost sizes mono routing localLaws dataLaws
    primitiveBound qS width routeWidth cap comparisonTime opTime hh values ops
  have hr := finishSome_bound rep bd boundary data samplingCode cost primitive control queryCost sizes lists
    mono routing localLaws dataLaws primitiveBound qS width routeWidth cap inputWidth comparisonTime scalarTime
    coinTime opTime adapterTime hh caps values ops samples
  have hb := branchStore_bound_of_width sizes mono control queryCost routing dispatchLaws
    (rep.ty (machineStore qS)) (cutoff rep data cost primitive qS)
    (finishSome rep bd boundary data samplingCode cost primitive qS)
    (fun p => inv p.2) (fun p => ready p.1 ∧ inv p.2) post W _ _ (by omega)
    (by
      intro p hp
      have hu : Q.size rep.data.unit p.1 ≤ width := by cases p.1; exact values.unit
      exact ⟨hu.trans (by omega), hp.1.trans (by omega)⟩)
    (fun p hp => ⟨hp.1.1.trans (by omega), hp.2.1.trans (by omega)⟩) hl hr
  have hb' : Bounds control queryCost
      (.seq (.atomic (QD.distribute rep.data.unit bd.out (rep.ty (machineStore qS))))
        (.branch (cutoff rep data cost primitive qS) (finishSome rep bd boundary data samplingCode cost primitive qS)))
      middle post (max (opTime + 3 * fee)
        (FinishCompiler.nativeFinishTime overhead width cap comparisonTime scalarTime coinTime opTime +
          adapterTime + 6 * fee) + 4 * fee) := by
    intro p hp z hz
    apply hb p _ z hz
    obtain ⟨value, saved⟩ := p
    cases value with
    | inl u => exact hp.2
    | inr out => exact hp
  have h := Bounds.seq control queryCost _ _ pre middle post (adapterTime + 2 * fee) _ fee hd hb' (by
    intro input hi value hv
    have h1 := sizes.prod_le (StepClass.HasOption.option bd.out) (rep.ty (machineStore qS)) input
    have h2 := sizes.prod_le (StepClass.HasSum.sum rep.data.unit bd.out) (rep.ty (machineStore qS)) value
    have ho := hiSize input.1 hi.1
    have hs := hi.2.1
    have ht := hvSize value.1 hv.1
    have hw := hv.2.1
    exact (routing.sequence _ _).trans (mono (by dsimp only [pre, middle, inv] at *; omega)))
  intro input hi z hz
  obtain ⟨hout, ht⟩ := h input hi z hz
  dsimp only [fee, W] at *
  exact ⟨hout, by omega⟩

end Signatures.Runtime.Coron.NativeSolver
