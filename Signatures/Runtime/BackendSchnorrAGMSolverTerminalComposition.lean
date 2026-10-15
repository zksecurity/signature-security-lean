import Signatures.Runtime.BackendSchnorrAGMSolverLocalCost
import Signatures.Runtime.BackendSchnorrAGMSolverPorts
import Signatures.Runtime.BackendWidthBudget

/-! Composition around an extractor whose primitive-derived budget is supplied
by the following terminal theorem. Actual output conversion, state retention,
optional-result inspection, cutoff and scalar projection are all charged here. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Solver

open BackendProgram Interface

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type}
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor (SourceInput G₁) (SourceForgery F G₁ M))
  (boundary : DataPorts (Q := Q) rep bd)
  {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes laws mono routing

theorem finishSome_bound_of_extractor
    (extractor : Code Q unifSpec iface (rep.ty Extraction.inputTy) (rep.ty Read.outputTy))
    (keep : EncodedState F G₁ M → Prop) (width routeWidth outputWidth adapterTime extractTime : Nat)
    (hh : header ≤ width) (hr : routeWidth ≤ width) (ho : outputWidth ≤ width)
    (hconvert : ∀ out, Q.size bd.out out ≤ routeWidth →
      Q.size (rep.ty forgeryTy) (encodeForgery out) ≤ outputWidth ∧ Q.cost boundary.output out ≤ adapterTime)
    (he : Bounds control queryCost extractor
      (fun p => Q.size (rep.ty forgeryTy) p.1 ≤ outputWidth ∧ Q.size (rep.ty stateTy) p.2 ≤ width ∧ keep p.2)
      (fun p => Q.size (rep.ty Read.outputTy) p ≤ width) extractTime) :
    Bounds control queryCost (finishSome rep bd boundary extractor)
      (fun p => Q.size bd.out p.1 ≤ routeWidth ∧ Q.size (rep.ty storeTy) p.2 ≤ width ∧ keep p.2.2)
      (fun out => Q.size (rep.ty scalar) out ≤ width)
      (extractTime + adapterTime + 13 * overhead (128 * width)) := by
  let pre := fun p : SourceForgery F G₁ M × ((G₁ × G₁) × EncodedState F G₁ M) =>
    Q.size bd.out p.1 ≤ routeWidth ∧ Q.size (rep.ty storeTy) p.2 ≤ width ∧ keep p.2.2
  let decoded := fun p : Extraction.inputTy.Value (cryptoBase F G₁ G₂ K M) =>
    Q.size (rep.ty forgeryTy) p.1 ≤ outputWidth ∧ Q.size (rep.ty stateTy) p.2 ≤ width ∧ keep p.2
  let finished := fun p : Read.outputTy.Value (cryptoBase F G₁ G₂ K M) => Q.size (rep.ty Read.outputTy) p ≤ width
  let post := fun out : F => Q.size (rep.ty scalar) out ≤ width
  have hpre (p) (hp : pre p) : Q.size (StepClass.HasProd.prod bd.out (rep.ty storeTy)) p ≤ 4 * width := by
    have ht := sizes.prod_le bd.out (rep.ty storeTy) p
    have ho := hp.1
    have hs := hp.2.1
    omega
  have hdecoded (p) (hp : decoded p) : Q.size (rep.ty Extraction.inputTy) p ≤ 4 * width := by
    have ht := sizes.prod_le (rep.ty forgeryTy) (rep.ty stateTy) p
    have ho := hp.1
    have hs := hp.2.1
    change Q.size (StepClass.HasProd.prod (rep.ty forgeryTy) (rep.ty stateTy)) p ≤ _
    omega
  have ha := adaptOutput_bound_with_widths (iface := iface) rep bd boundary.output sizes laws mono control queryCost routing
    width routeWidth outputWidth adapterTime hh hr ho keep hconvert
  have hp := projection_bound (iface := iface) rep sizes laws mono control queryCost routing width
  have hep := seq_bound_of_width mono control queryCost routing extractor _ decoded finished post (4 * width)
    extractTime (2 * overhead (32 * width)) hdecoded (fun _ h => h.trans (by omega)) he hp
  have hall := seq_bound_of_width mono control queryCost routing _ _ pre decoded post (4 * width)
    (adapterTime + 9 * overhead (32 * width)) _ hpre hdecoded ha hep
  intro input hi z hz
  obtain ⟨hout, ht⟩ := hall input hi z hz
  have hfee := mono (show 32 * width ≤ 128 * width by omega)
  exact ⟨hout, by norm_num only [← Nat.mul_assoc] at ht; omega⟩

variable [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))

include dataLaws primitiveBound

theorem cutoff_bound_of_store (width zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width) (hzero : (primitiveBound .zero).time () ≤ zeroTime) :
    Bounds control queryCost (cutoff (iface := iface) rep data cost primitive)
      (fun p => Q.size (rep.ty storeTy) p.2 ≤ width)
      (fun out => Q.size (rep.ty scalar) out ≤ width)
      (zeroTime + 3 * overhead (128 * width)) := by
  apply Bounds.atomic
  intro input hi
  have hu' : Q.size rep.data.unit input.1 ≤ width := by cases input.1; exact hu
  have hin : Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty storeTy)) input ≤ 4 * width :=
    (sizes.prod_le rep.data.unit (rep.ty storeTy) input).trans (by omega)
  have ht := cutoff_cost rep data cost primitive laws dataLaws primitiveBound mono input (4 * width) zeroTime
    (hu.trans (by omega)) (hz.trans (by omega)) hin hzero
  have hc := (routing.localCall _ _).trans (mono (show
    Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty storeTy)) input + Q.size (rep.ty scalar) (0 : F) ≤
      128 * width by omega))
  refine ⟨hz, ?_⟩
  change Q.cost (Q.compose (data.unit (StepClass.HasProd.prod rep.data.unit (rep.ty storeTy))) (primitive CryptoOp.zero)) input +
    control.localCall (Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty storeTy)) input) (Q.size (rep.ty scalar) (0 : F)) ≤ _
  norm_num only [← Nat.mul_assoc] at ht
  omega

variable [Q.HasOption] [OptionCode (Q := Q)] [QD : Q.IsDistributive]
  (dispatch : DispatchCostLaws (Q := Q) overhead)

include dispatch

theorem terminal_bound_of_extractor
    (extractor : Code Q unifSpec iface (rep.ty Extraction.inputTy) (rep.ty Read.outputTy))
    (keep : EncodedState F G₁ M → Prop)
    (width baseWidth routeWidth outputWidth adapterTime extractTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hr : routeWidth ≤ width) (ho : outputWidth ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width) (hzero : (primitiveBound .zero).time () ≤ zeroTime)
    (caps : PortCaps rep bd boundary baseWidth outputWidth routeWidth adapterTime)
    (he : Bounds control queryCost extractor
      (fun p => Q.size (rep.ty forgeryTy) p.1 ≤ outputWidth ∧ Q.size (rep.ty stateTy) p.2 ≤ width ∧ keep p.2)
      (fun p => Q.size (rep.ty Read.outputTy) p ≤ width) extractTime) :
    Bounds control queryCost (terminal rep bd boundary data cost primitive extractor)
      (fun p => ResultReady (Q := Q) bd routeWidth p.1 ∧ Q.size (rep.ty storeTy) p.2 ≤ width ∧ keep p.2.2)
      (fun out => Q.size (rep.ty scalar) out ≤ width)
      (extractTime + zeroTime + 2 * adapterTime + 23 * overhead (4096 * width)) := by
  let B := 128 * width
  let fee := overhead (32 * B)
  let inv := fun saved : (G₁ × G₁) × EncodedState F G₁ M => Q.size (rep.ty storeTy) saved ≤ width ∧ keep saved.2
  let viewed : Unit ⊕ SourceForgery F G₁ M → Prop :=
    Sum.elim (fun _ => True) (fun out => Q.size bd.out out ≤ routeWidth)
  let pre := fun p : Option (SourceForgery F G₁ M) × ((G₁ × G₁) × EncodedState F G₁ M) =>
    ResultReady (Q := Q) bd routeWidth p.1 ∧ inv p.2
  let middle := fun p : (Unit ⊕ SourceForgery F G₁ M) × ((G₁ × G₁) × EncodedState F G₁ M) => viewed p.1 ∧ inv p.2
  let post := fun out : F => Q.size (rep.ty scalar) out ≤ width
  have hiSize (result) (hready : ResultReady (Q := Q) bd routeWidth result) :
      Q.size (StepClass.HasOption.option bd.out) result ≤ 2 * width := by
    cases result with
    | none => exact (sizes.none_le bd.out).trans (by omega)
    | some out =>
        have hb := hready out rfl
        have hs := sizes.some_le bd.out out
        omega
  have hvSize (value) (hv : viewed value) :
      Q.size (StepClass.HasSum.sum rep.data.unit bd.out) value ≤ 2 * width := by
    have hsum := sizes.sum_le rep.data.unit bd.out value
    cases value with
    | inl u =>
        have hu' : Q.size rep.data.unit u ≤ width := by cases u; exact hu
        dsimp only [Sum.elim_inl] at hsum
        omega
    | inr out =>
        change Q.size bd.out out ≤ routeWidth at hv
        dsimp only [Sum.elim_inr] at hsum
        omega
  have hpre (p) (hp : pre p) : Q.size (Caller.result (bd := bd) (rep.ty storeTy)) p ≤ B := by
    have hprod := sizes.prod_le (StepClass.HasOption.option bd.out) (rep.ty storeTy) p
    have ho := hiSize p.1 hp.1
    have hs := hp.2.1
    dsimp only [Caller.result, B]
    omega
  have hmid (p) (hp : middle p) :
      Q.size (StepClass.HasProd.prod (StepClass.HasSum.sum rep.data.unit bd.out) (rep.ty storeTy)) p ≤ B := by
    have hprod := sizes.prod_le (StepClass.HasSum.sum rep.data.unit bd.out) (rep.ty storeTy) p
    have ho := hvSize p.1 hp.1
    have hs := hp.2.1
    dsimp only [B]
    omega
  have hd := firstAtomic_bound_of_width (iface := iface) mono control queryCost routing
    (rep.ty storeTy) boundary.optional (ResultReady (Q := Q) bd routeWidth) viewed inv B adapterTime
    (fun result hr => (hiSize result hr).trans (by dsimp [B]; omega))
    (fun _ hs => hs.1.trans (by dsimp [B]; omega)) (by
      intro result hr'
      have hv : viewed (optionView result) := by
        cases result with
        | none => trivial
        | some out => exact hr' out rfl
      exact ⟨hv, (hvSize _ hv).trans (by dsimp [B]; omega), caps.optional result hr'⟩)
  have hl : Bounds control queryCost (cutoff (iface := iface) rep data cost primitive)
      (fun p => inv p.2) post (zeroTime + 3 * fee) := by
    intro p hp z hz'
    obtain ⟨hout, ht⟩ := cutoff_bound_of_store rep sizes laws mono control queryCost routing data cost primitive
      dataLaws primitiveBound width zeroTime hh hu hz hzero p hp.1 z hz'
    have hm := mono (show 128 * width ≤ 32 * B by dsimp [B]; omega)
    exact ⟨hout, by dsimp only [fee]; omega⟩
  have hright : Bounds control queryCost (finishSome rep bd boundary extractor)
      (fun p => Q.size bd.out p.1 ≤ routeWidth ∧ inv p.2) post (extractTime + adapterTime + 13 * fee) := by
    intro p hp z hz'
    obtain ⟨hout, ht⟩ := finishSome_bound_of_extractor rep bd boundary sizes laws mono control queryCost routing
      extractor keep width routeWidth outputWidth adapterTime extractTime hh hr ho caps.output he p hp z hz'
    have hm := mono (show 128 * width ≤ 32 * B by dsimp [B]; omega)
    exact ⟨hout, by dsimp only [fee]; omega⟩
  have hb := branchStore_bound_of_width sizes mono control queryCost routing dispatch
    (rep.ty storeTy) (cutoff rep data cost primitive) (finishSome rep bd boundary extractor)
    (fun p => inv p.2) (fun p => Q.size bd.out p.1 ≤ routeWidth ∧ inv p.2) post B _ _
    (by dsimp [B]; omega)
    (by intro p hp; have hu' : Q.size rep.data.unit p.1 ≤ width := by cases p.1; exact hu
        exact ⟨hu'.trans (by dsimp [B]; omega), hp.1.trans (by dsimp [B]; omega)⟩)
    (fun p hp => ⟨hp.1.trans (by dsimp [B]; omega), hp.2.1.trans (by dsimp [B]; omega)⟩) hl hright
  have hb' : Bounds control queryCost
      (.seq (.atomic (QD.distribute rep.data.unit bd.out (rep.ty storeTy)))
        (.branch (cutoff rep data cost primitive) (finishSome rep bd boundary extractor)))
      middle post (max (zeroTime + 3 * fee) (extractTime + adapterTime + 13 * fee) + 4 * fee) := by
    intro p hp z hz'
    apply hb p _ z hz'
    obtain ⟨tag, saved⟩ := p
    cases tag with
    | inl u => exact hp.2
    | inr out => exact hp
  have hall := seq_bound_of_width mono control queryCost routing _ _ pre middle post B
    (adapterTime + 2 * fee) _ hpre hmid hd hb'
  intro input hi z hz'
  obtain ⟨hout, ht⟩ := hall input hi z hz'
  exact ⟨hout, by norm_num only [fee, B, ← Nat.mul_assoc] at ht; omega⟩

end Signatures.Runtime.SchnorrAGM.Native.Solver
