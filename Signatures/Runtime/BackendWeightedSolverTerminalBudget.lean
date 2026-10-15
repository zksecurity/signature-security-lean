import Signatures.Runtime.BackendWeightedSolverLocalCost
import Signatures.Runtime.BackendWeightedSolverPorts
import Signatures.Runtime.BackendWidthBudget

/-! Native terminal composition around an actual extractor. The component
extractor budget is instantiated by the primitive-derived good/bad certificates.
This module derives all output decoding, argument construction, projection,
option inspection, and cutoff costs, retaining the full encoded data. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.WeightedAGM.NativeSolver

open BackendProgram NativeHandler Reply

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (index : Index)
  (bd : Boundary C (generalSpec (index.ty.Value (cryptoBase F G₁ G₂ K M)) (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor G₂
    ((AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M)))
  (boundary : DataPorts (Q := Q) rep index bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead) (routing : RoutingCostLaws control overhead)

include sizes laws dataLaws primitiveBound mono routing

theorem finishSome_bound_of_extractor (value config : Ty CryptoAtom)
    (extractor : Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.env [AGM.outputTy index.messageTy, (Reply.transcriptTy index.ty index.messageTy)]) (rep.ty (Reply.cacheTy index.ty value)))
      (rep.ty (.pair scalar (Reply.cacheTy index.ty value))))
    (inv : (Reply.storeTy index.ty index.messageTy value config).Value (cryptoBase F G₁ G₂ K M) → Prop)
    (width keyWidth outputWidth routeWidth adapterTime extractTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (ho : outputWidth ≤ width) (hr : routeWidth ≤ width)
    (caps : PortCaps rep index bd boundary keyWidth outputWidth routeWidth adapterTime)
    (hs : ∀ saved, inv saved → Q.size (rep.ty (Reply.storeTy index.ty index.messageTy value config)) saved ≤ width)
    (he : ∀ out saved, Q.size (rep.ty (AGM.outputTy index.messageTy)) out ≤ outputWidth → inv saved →
      ∀ z ∈ support (extractor.run control queryCost ((out, saved.2.2, ()), saved.2.1)),
        (Q.size (rep.ty scalar) z.value.1 ≤ width ∧ Q.size (rep.ty (Reply.cacheTy index.ty value)) z.value.2 ≤ width) ∧
          z.steps ≤ extractTime) :
    Bounds control queryCost (finishSome rep index bd boundary data cost primitive value config extractor)
      (fun p => Q.size bd.out p.1 ≤ routeWidth ∧ inv p.2)
      (fun out => Q.size (rep.ty scalar) out ≤ width)
      (extractTime + adapterTime + 144 * overhead (4096 * width)) := by
  let B := 128 * width
  let fee := overhead (32 * B)
  let raw := fun p : (AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M) ×
      (Reply.storeTy index.ty index.messageTy value config).Value (cryptoBase F G₁ G₂ K M) => Q.size bd.out p.1 ≤ routeWidth ∧ inv p.2
  let decoded := fun p : (AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M) ×
      (Reply.storeTy index.ty index.messageTy value config).Value (cryptoBase F G₁ G₂ K M) =>
    Q.size (rep.ty (AGM.outputTy index.messageTy)) p.1 ≤ outputWidth ∧ inv p.2
  let args := fun p : Env (cryptoBase F G₁ G₂ K M) [AGM.outputTy index.messageTy, (Reply.transcriptTy index.ty index.messageTy)] ×
      (Reply.cacheTy index.ty value).Value (cryptoBase F G₁ G₂ K M) =>
    ∃ out saved, decoded (out, saved) ∧ p = ((out, saved.2.2, ()), saved.2.1)
  let finished := fun p : F × (Reply.cacheTy index.ty value).Value (cryptoBase F G₁ G₂ K M) =>
    Q.size (rep.ty scalar) p.1 ≤ width ∧ Q.size (rep.ty (Reply.cacheTy index.ty value)) p.2 ≤ width
  let post := fun out : F => Q.size (rep.ty scalar) out ≤ width
  have hraw : ∀ p, raw p → Q.size (StepClass.HasProd.prod bd.out (rep.ty (Reply.storeTy index.ty index.messageTy value config))) p ≤ B := by
    intro p hp
    have ht := sizes.prod_le bd.out (rep.ty (Reply.storeTy index.ty index.messageTy value config)) p
    have hstore := hs p.2 hp.2
    have hout := hp.1
    dsimp only [B] at *
    omega
  have hdecoded : ∀ p, decoded p →
      Q.size (rep.ty (.pair (AGM.outputTy index.messageTy) (Reply.storeTy index.ty index.messageTy value config))) p ≤ 3 * width := by
    intro p hp
    have ht := sizes.prod_le (rep.ty (AGM.outputTy index.messageTy)) (rep.ty (Reply.storeTy index.ty index.messageTy value config)) p
    have hstore := hs p.2 hp.2
    have hout := hp.1
    change Q.size (StepClass.HasProd.prod (rep.ty (AGM.outputTy index.messageTy)) (rep.ty (Reply.storeTy index.ty index.messageTy value config))) p ≤ _
    omega
  have hargs : ∀ p, args p →
      Q.size (StepClass.HasProd.prod (rep.env [AGM.outputTy index.messageTy, (Reply.transcriptTy index.ty index.messageTy)]) (rep.ty (Reply.cacheTy index.ty value))) p ≤ B := by
    rintro p ⟨out, saved, hd, rfl⟩
    have hstore := hs saved hd.2
    have hout := hd.1
    have hprod := @sizes.prod_le
    have hfst := @sizes.fst_le
    have hsnd := @sizes.snd_le
    dsimp only [B, LanguageRepresentation.env, LanguageRepresentation.ty, Reply.storeTy] at *
    grind only
  have hfinished : ∀ p, finished p → Q.size (rep.ty (.pair scalar (Reply.cacheTy index.ty value))) p ≤ B := by
    intro p hp
    have ht := sizes.prod_le (rep.ty scalar) (rep.ty (Reply.cacheTy index.ty value)) p
    have hf := hp.1
    have hc := hp.2
    change Q.size (StepClass.HasProd.prod (rep.ty scalar) (rep.ty (Reply.cacheTy index.ty value))) p ≤ _
    dsimp only [B]
    omega
  have hd := firstAtomic_bound_of_width (iface := iface) mono control queryCost routing
    (rep.ty (Reply.storeTy index.ty index.messageTy value config)) boundary.output (fun out => Q.size bd.out out ≤ routeWidth)
    (fun out => Q.size (rep.ty (AGM.outputTy index.messageTy)) out ≤ outputWidth) inv B adapterTime
    (fun out hout => hout.trans (by dsimp [B]; omega))
    (fun saved hstore => (hs saved hstore).trans (by dsimp [B]; omega))
    (fun out hout => let hc := caps.output out hout
      ⟨hc.1, hc.1.trans (by dsimp [B]; omega), hc.2⟩)
  have ha := atomic_bound_of_width (iface := iface) mono control queryCost routing
    (extractionArgsCode rep index data cost primitive value config) decoded args B (136 * fee)
    (fun p hp => (hdecoded p hp).trans (by dsimp [B]; omega)) (by
      intro p hp
      have harg : args ((p.1, p.2.2.2, ()), p.2.2.1) := ⟨p.1, p.2, hp, rfl⟩
      refine ⟨harg, hargs _ harg, ?_⟩
      have ht := extractionArgsCode_cost rep index data cost primitive sizes laws dataLaws primitiveBound mono
        value config (3 * width) (by omega) (by omega) p (hdecoded p hp)
      exact ht.trans (Nat.mul_le_mul_left 136 (mono (by dsimp [B]; omega))))
  have he' : Bounds control queryCost extractor args finished extractTime := by
    rintro p ⟨out, saved, hd, rfl⟩ z hz
    exact he out saved hd.1 hd.2 z hz
  have hp := atomic_bound_of_width (iface := iface) mono control queryCost routing
    (QP.fst (rep.ty scalar) (rep.ty (Reply.cacheTy index.ty value))) finished post B fee hfinished (by
      intro p hp
      refine ⟨hp.1, hp.1.trans (by dsimp [B]; omega), ?_⟩
      exact (laws.fst _ _ p).trans (mono (by
        have ht := sizes.prod_le (rep.ty scalar) (rep.ty (Reply.cacheTy index.ty value)) p
        have hf := hp.1
        have hc := hp.2
        dsimp only [B]
        omega)))
  have hep := seq_bound_of_width mono control queryCost routing extractor _ args finished post B
    extractTime (fee + fee) hargs hfinished he' hp
  have hae := seq_bound_of_width mono control queryCost routing _ _ decoded args post B
    (136 * fee + fee) _ (fun p hp => (hdecoded p hp).trans (by dsimp [B]; omega)) hargs ha hep
  have h := seq_bound_of_width mono control queryCost routing _ _ raw decoded post B
    (adapterTime + 2 * fee) _ hraw (fun p hp => (hdecoded p hp).trans (by dsimp [B]; omega)) hd hae
  intro input hi z hz
  obtain ⟨hout, ht⟩ := h input hi z hz
  exact ⟨hout, by norm_num only [fee, B, ← Nat.mul_assoc] at ht; omega⟩

theorem cutoff_bound (value config : Ty CryptoAtom)
    (inv : (Reply.storeTy index.ty index.messageTy value config).Value (cryptoBase F G₁ G₂ K M) → Prop)
    (width zeroTime : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hzero : (primitiveBound CryptoOp.zero).time () ≤ zeroTime)
    (hs : ∀ saved, inv saved → Q.size (rep.ty (Reply.storeTy index.ty index.messageTy value config)) saved ≤ width) :
    Bounds control queryCost (cutoff (iface := iface) rep index data cost primitive value config)
      (fun p => inv p.2) (fun out => Q.size (rep.ty scalar) out ≤ width)
      (zeroTime + 3 * overhead (4096 * width)) := by
  intro input hi z hz'
  simp only [cutoff, Code.run, support_pure, Set.mem_singleton_iff] at hz'
  subst z
  have ht := (LocalBound.compose laws
    (dataLaws.unitBound (StepClass.HasProd.prod rep.data.unit (rep.ty (Reply.storeTy index.ty index.messageTy value config))))
    (primitiveBound CryptoOp.zero)).cost_le input
  have hp := sizes.prod_le rep.data.unit (rep.ty (Reply.storeTy index.ty index.messageTy value config)) input
  have hu' : Q.size rep.data.unit input.1 ≤ width := by cases input.1; exact hu
  have hs' := hs input.2 hi
  have hc := routing.localCall
    (Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty (Reply.storeTy index.ty index.messageTy value config))) input)
    (Q.size (rep.ty scalar) (0 : F))
  have hfee : ∀ n ≤ 4096 * width, overhead n ≤ overhead (4096 * width) := fun _ hn => mono hn
  refine ⟨hz, ?_⟩
  dsimp only [LocalBound.compose, DataCostLaws.unitBound, arithmetic,
    LanguageRepresentation.ty, Reply.storeTy] at *
  grind only

variable [QO : Q.HasOption] [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  (dispatch : DispatchCostLaws (Q := Q) overhead)

include dispatch

theorem terminal_bound_of_extractor (value config : Ty CryptoAtom)
    (extractor : Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.env [AGM.outputTy index.messageTy, (Reply.transcriptTy index.ty index.messageTy)]) (rep.ty (Reply.cacheTy index.ty value)))
      (rep.ty (.pair scalar (Reply.cacheTy index.ty value))))
    (inv : (Reply.storeTy index.ty index.messageTy value config).Value (cryptoBase F G₁ G₂ K M) → Prop)
    (width keyWidth outputWidth routeWidth adapterTime extractTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (ho : outputWidth ≤ width) (hr : routeWidth ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hzero : (primitiveBound CryptoOp.zero).time () ≤ zeroTime)
    (caps : PortCaps rep index bd boundary keyWidth outputWidth routeWidth adapterTime)
    (hs : ∀ saved, inv saved → Q.size (rep.ty (Reply.storeTy index.ty index.messageTy value config)) saved ≤ width)
    (he : ∀ out saved, Q.size (rep.ty (AGM.outputTy index.messageTy)) out ≤ outputWidth → inv saved →
      ∀ z ∈ support (extractor.run control queryCost ((out, saved.2.2, ()), saved.2.1)),
        (Q.size (rep.ty scalar) z.value.1 ≤ width ∧ Q.size (rep.ty (Reply.cacheTy index.ty value)) z.value.2 ≤ width) ∧
          z.steps ≤ extractTime) :
    Bounds control queryCost (terminal rep index bd boundary data cost primitive value config extractor)
      (fun p => ResultReady (Q := Q) index bd routeWidth p.1 ∧ inv p.2)
      (fun out => Q.size (rep.ty scalar) out ≤ width)
      (extractTime + zeroTime + 2 * adapterTime + 160 * overhead (4096 * width)) := by
  let B := 128 * width
  let fee := overhead (32 * B)
  let viewed : Unit ⊕ ((AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M)) → Prop :=
    Sum.elim (fun _ => True) (fun out => Q.size bd.out out ≤ routeWidth)
  let pre := fun p : Option ((AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M)) ×
      (Reply.storeTy index.ty index.messageTy value config).Value (cryptoBase F G₁ G₂ K M) =>
    ResultReady (Q := Q) index bd routeWidth p.1 ∧ inv p.2
  let middle := fun p : (Unit ⊕ ((AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M))) ×
      (Reply.storeTy index.ty index.messageTy value config).Value (cryptoBase F G₁ G₂ K M) => viewed p.1 ∧ inv p.2
  let post := fun out : F => Q.size (rep.ty scalar) out ≤ width
  have hiSize : ∀ result, ResultReady (Q := Q) index bd routeWidth result →
      Q.size (StepClass.HasOption.option bd.out) result ≤ 2 * width := by
    intro result hready
    cases result with
    | none => exact (sizes.none_le bd.out).trans (by omega)
    | some out =>
        have hb := hready out rfl
        have hs := sizes.some_le bd.out out
        omega
  have hvSize : ∀ value, viewed value →
      Q.size (StepClass.HasSum.sum rep.data.unit bd.out) value ≤ 2 * width := by
    intro value hv
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
  have hpre : ∀ p, pre p → Q.size (Caller.result (bd := bd) (rep.ty (Reply.storeTy index.ty index.messageTy value config))) p ≤ B := by
    intro p hp
    have hprod := sizes.prod_le (StepClass.HasOption.option bd.out) (rep.ty (Reply.storeTy index.ty index.messageTy value config)) p
    have ho := hiSize p.1 hp.1
    have hstore := hs p.2 hp.2
    dsimp only [Caller.result, B]
    omega
  have hmid : ∀ p, middle p →
      Q.size (StepClass.HasProd.prod (StepClass.HasSum.sum rep.data.unit bd.out) (rep.ty (Reply.storeTy index.ty index.messageTy value config))) p ≤ B := by
    intro p hp
    have hprod := sizes.prod_le (StepClass.HasSum.sum rep.data.unit bd.out) (rep.ty (Reply.storeTy index.ty index.messageTy value config)) p
    have ho := hvSize p.1 hp.1
    have hstore := hs p.2 hp.2
    dsimp only [B]
    omega
  have hd := firstAtomic_bound_of_width (iface := iface) mono control queryCost routing
    (rep.ty (Reply.storeTy index.ty index.messageTy value config)) boundary.optional (ResultReady (Q := Q) index bd routeWidth) viewed inv B adapterTime
    (fun result hr => (hiSize result hr).trans (by dsimp [B]; omega))
    (fun saved hs' => (hs saved hs').trans (by dsimp [B]; omega)) (by
      intro result hr'
      have hv : viewed (optionView result) := by
        cases result with
        | none => trivial
        | some out => exact hr' out rfl
      exact ⟨hv, (hvSize _ hv).trans (by dsimp [B]; omega), caps.optional result hr'⟩)
  have hl : Bounds control queryCost (cutoff (iface := iface) rep index data cost primitive value config)
      (fun p => inv p.2) post (zeroTime + 3 * fee) := by
    simpa only [fee, B, ← Nat.mul_assoc] using
      cutoff_bound rep index data cost primitive control queryCost sizes laws dataLaws primitiveBound mono routing
        value config inv width zeroTime hh hu hz hzero hs
  have hright : Bounds control queryCost (finishSome rep index bd boundary data cost primitive value config extractor)
      (fun p => Q.size bd.out p.1 ≤ routeWidth ∧ inv p.2) post (extractTime + adapterTime + 144 * fee) := by
    simpa only [fee, B, ← Nat.mul_assoc] using
      finishSome_bound_of_extractor rep index bd boundary data cost primitive control queryCost sizes laws dataLaws
        primitiveBound mono routing value config extractor inv width keyWidth outputWidth routeWidth
        adapterTime extractTime hh hu ho hr caps hs he
  have hb := branchStore_bound_of_width sizes mono control queryCost routing dispatch
    (rep.ty (Reply.storeTy index.ty index.messageTy value config)) (cutoff rep index data cost primitive value config)
    (finishSome rep index bd boundary data cost primitive value config extractor)
    (fun p => inv p.2) (fun p => Q.size bd.out p.1 ≤ routeWidth ∧ inv p.2) post B _ _
    (by dsimp [B]; omega)
    (by intro p hp; have hu' : Q.size rep.data.unit p.1 ≤ width := by cases p.1; exact hu
        exact ⟨hu'.trans (by dsimp [B]; omega), (hs p.2 hp).trans (by dsimp [B]; omega)⟩)
    (fun p hp => ⟨hp.1.trans (by dsimp [B]; omega), (hs p.2 hp.2).trans (by dsimp [B]; omega)⟩) hl hright
  have hb' : Bounds control queryCost
      (.seq (.atomic (QD.distribute rep.data.unit bd.out (rep.ty (Reply.storeTy index.ty index.messageTy value config))))
        (.branch (cutoff rep index data cost primitive value config)
          (finishSome rep index bd boundary data cost primitive value config extractor)))
      middle post (max (zeroTime + 3 * fee) (extractTime + adapterTime + 144 * fee) + 4 * fee) := by
    intro p hp z hz'
    apply hb p _ z hz'
    obtain ⟨tag, saved⟩ := p
    cases tag with
    | inl u => exact hp.2
    | inr out => exact hp
  have h := seq_bound_of_width mono control queryCost routing _ _ pre middle post B
    (adapterTime + 2 * fee) _ hpre hmid hd hb'
  intro input hi z hz'
  obtain ⟨hout, ht⟩ := h input hi z hz'
  exact ⟨hout, by norm_num only [fee, B, ← Nat.mul_assoc] at ht; omega⟩

end Signatures.Runtime.WeightedAGM.NativeSolver
