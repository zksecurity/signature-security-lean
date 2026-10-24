import Proofs.Runtime.BackendSchnorrROMPassVerificationBudget
import Proofs.Runtime.BackendSchnorrROMPassPorts
import Proofs.Runtime.BackendDispatchBudget

/-! All-path terminal composition: actual output conversion, live verification,
singleton construction, optional dispatch and cutoff. The verification budget
is an internal premise, discharged from primitive contracts in the full pass. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.ListROM.NativePass

open BackendProgram RawTape NativeInterface NativeComponents

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  [Q.HasOption] [OptionCode (Q := Q)]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor G₁ (M × G₁ × F))
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead) (dispatch : DispatchCostLaws (Q := Q) overhead)

include sizes lists laws dataLaws mono routing dispatch

theorem terminal_bound_of_verification
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (width tapeWidth mc lc sc rc nextSavedCap frame outputWidth outputTime optionalTime verifyTime : Nat)
    (hh : header ≤ width) (ht : header ≤ tapeWidth) (hu : Q.size rep.data.unit () ≤ width)
    (hs : sc ≤ nextSavedCap) (hw : (6 * (nextSavedCap + rc) + 3) * tapeWidth ≤ width)
    (hframe : (12 * (mc + lc) + 40) * width ≤ frame) (ho : outputWidth ≤ frame)
    (hconvert : ∀ out, Q.size bd.out out ≤ outputWidth →
      Q.size (rep.ty forgery) out ≤ width ∧ Q.cost boundary.output out ≤ outputTime)
    (hoptional : ∀ result, ResultReady (Q := Q) bd outputWidth result →
      Q.cost boundary.optional result ≤ optionalTime)
    (hverify : Bounds control queryCost (verify rep data cost primitive sampler)
      (InputBound (Q := Q) rep forgery width width tapeWidth mc lc sc rc)
      (VerifiedBound (Q := Q) rep width tapeWidth mc (lc + 1) nextSavedCap rc) verifyTime) :
    Bounds control queryCost (terminal rep bd boundary data cost primitive sampler)
      (fun p => ResultReady (Q := Q) bd outputWidth p.1 ∧
        StoreBound (Q := Q) rep width tapeWidth mc lc sc rc p.2)
      (ResultBound (Q := Q) rep width tapeWidth mc (lc + 1) nextSavedCap rc)
      (verifyTime + outputTime + optionalTime + 2048 * overhead (8192 * frame)) := by
  let fee := overhead (8192 * frame)
  let inv := StoreBound (Q := Q) rep width tapeWidth mc lc sc rc
  let pre := fun p : Option (M × G₁ × F) × Shared.Store F G₁ M =>
    ResultReady (Q := Q) bd outputWidth p.1 ∧ inv p.2
  let decoded := InputBound (Q := Q) rep forgery width width tapeWidth mc lc sc rc
  let verified := VerifiedBound (Q := Q) rep width tapeWidth mc (lc + 1) nextSavedCap rc
  let post := ResultBound (Q := Q) rep width tapeWidth mc (lc + 1) nextSavedCap rc
  have hwf : width ≤ frame := by nlinarith only [hframe, Nat.zero_le ((mc + lc) * width)]
  have hw0 : (6 * (sc + rc) + 3) * tapeWidth ≤ width :=
    (Nat.mul_le_mul_right tapeWidth (by omega)).trans hw
  have hstore (saved) (hi : inv saved) : Q.size (rep.ty storeTy) saved ≤ frame := by
    have h := store_size rep sizes lists width tapeWidth mc lc sc rc hh ht hw0 saved hi
    nlinarith only [h, hframe]
  have hdecoded (p) (hi : decoded p) : Q.size (rep.ty (withStore forgery)) p ≤ frame := by
    have h := input_size rep sizes lists forgery width width tapeWidth mc lc sc rc hh ht (by omega) hw0 p hi
    nlinarith only [h, hframe]
  have hverified (p) (hi : verified p) :
      Q.size (rep.ty (NativeFork.passOutput cachePassOutput)) p ≤ frame := by
    have h := verified_size rep sizes lists width tapeWidth mc (lc + 1) nextSavedCap rc hh ht hw p hi
    nlinarith only [h, hframe]
  have hpost (p) (hi : post p) : Q.size (rep.ty resultTy) p ≤ frame := by
    have h := result_size rep sizes lists width tapeWidth mc (lc + 1) nextSavedCap rc hh ht hw p hi
    nlinarith only [h, hframe]
  have hsng : Bounds control queryCost (.atomic (iface := iface)
      (localCode rep data cost primitive singletonExpression)) verified post (1029 * fee) := by
    apply Bounds.atomic
    intro p hp
    have hout : post ([p.1], p.2) := ⟨by simpa using hp.1, by simp, hp.2⟩
    have hi := hverified p hp
    have ho' := hpost _ hout
    have hc := (singletonExpression_cost rep data cost primitive sizes lists laws dataLaws mono p frame
      (hh.trans hwf) (hu.trans hwf) hi).2
    have hm := mono (show 256 * frame ≤ 8192 * frame by omega)
    have hf := (routing.localCall _ _).trans (mono (show
      Q.size (rep.ty (NativeFork.passOutput cachePassOutput)) p + Q.size (rep.ty resultTy) ([p.1], p.2) ≤
        8192 * frame by omega))
    refine ⟨hout, ?_⟩
    change Q.cost (localCode rep data cost primitive singletonExpression) p +
      control.localCall (Q.size (rep.ty (NativeFork.passOutput cachePassOutput)) p)
        (Q.size (rep.ty resultTy) ([p.1], p.2)) ≤ 1029 * fee
    dsimp only [fee]
    omega
  have hfinish : Bounds control queryCost (finishSome rep bd boundary data cost primitive sampler)
      (fun p => Q.size bd.out p.1 ≤ outputWidth ∧ inv p.2) post
      (verifyTime + outputTime + 1033 * fee) := by
    let before := fun p : (M × G₁ × F) × Shared.Store F G₁ M =>
      Q.size bd.out p.1 ≤ outputWidth ∧ inv p.2
    have hi (p) (hp : before p) : Q.size (StepClass.HasProd.prod bd.out (rep.ty storeTy)) p ≤ 4 * frame := by
      have h := sizes.prod_le bd.out (rep.ty storeTy) p
      have hs' := hstore p.2 hp.2
      have ho' := hp.1.trans ho
      omega
    have hc := firstAtomic_bound_of_width (iface := iface) mono control queryCost routing (rep.ty storeTy)
      boundary.output (fun out => Q.size bd.out out ≤ outputWidth)
      (fun out => Q.size (rep.ty forgery) out ≤ width) inv frame outputTime
      (fun _ h => h.trans ho) hstore (fun out h =>
        ⟨(hconvert out h).1, (hconvert out h).1.trans hwf, (hconvert out h).2⟩)
    have hv := seq_bound_of_width mono control queryCost routing _ _ decoded verified post frame
      verifyTime (1029 * fee) hdecoded hverified hverify hsng
    have hall := seq_bound_of_width mono control queryCost routing _ _ before decoded post (4 * frame)
      (outputTime + 2 * overhead (32 * frame)) _ hi (fun _ h => (hdecoded _ h).trans (by omega)) hc hv
    apply Bounds.time_mono control queryCost hall
    have h32 := mono (show 32 * frame ≤ 8192 * frame by omega)
    have h128 := mono (show 32 * (4 * frame) ≤ 8192 * frame by omega)
    dsimp only [fee]
    omega
  have hcut : Bounds control queryCost (cutoff (iface := iface) rep data cost primitive)
      (fun p => inv p.2) post (1029 * fee) := by
    apply Bounds.atomic
    intro p hp
    have hout : post ([], p.2.2) :=
      ⟨by simp, by simp, NativeUniform.tape_mono rep tapeWidth sc nextSavedCap p.2.2.1 hp.tape.1 hs,
        hp.tape.2⟩
    have hi : Q.size (rep.ty (withStore .unit)) p ≤ 4 * frame := by
      have hs' := hstore p.2 hp
      have hu' : Q.size rep.data.unit p.1 ≤ width := by cases p.1; exact hu
      have h := sizes.prod_le rep.data.unit (rep.ty storeTy) p
      change Q.size (rep.ty (withStore .unit)) p ≤ _ at h
      omega
    have ho' := hpost _ hout
    have hc := (cutoffExpression_cost rep data cost primitive sizes lists laws dataLaws mono p (4 * frame)
      (by omega) (by omega) hi).2
    have hm := mono (show 256 * (4 * frame) ≤ 8192 * frame by omega)
    have hf := (routing.localCall _ _).trans (mono (show
      Q.size (rep.ty (withStore .unit)) p + Q.size (rep.ty resultTy) ([], p.2.2) ≤ 8192 * frame by omega))
    refine ⟨hout, ?_⟩
    change Q.cost (localCode rep data cost primitive cutoffExpression) p +
      control.localCall (Q.size (rep.ty (withStore .unit)) p)
        (Q.size (rep.ty resultTy) ([], p.2.2)) ≤ 1029 * fee
    dsimp only [fee]
    omega
  let viewed : Unit ⊕ (M × G₁ × F) → Prop :=
    Sum.elim (fun _ => True) (fun out => Q.size bd.out out ≤ outputWidth)
  let middle := fun p : (Unit ⊕ (M × G₁ × F)) × Shared.Store F G₁ M => viewed p.1 ∧ inv p.2
  have hiSize (result) (hready : ResultReady (Q := Q) bd outputWidth result) :
      Q.size (StepClass.HasOption.option bd.out) result ≤ 2 * frame := by
    cases result with
    | none => exact (sizes.none_le bd.out).trans (by omega)
    | some out =>
        have hb := hready out rfl
        have hs' := sizes.some_le bd.out out
        omega
  have hvSize (value) (hv : viewed value) :
      Q.size (StepClass.HasSum.sum rep.data.unit bd.out) value ≤ 2 * frame := by
    have hsum := sizes.sum_le rep.data.unit bd.out value
    cases value with
    | inl u =>
        have hu' : Q.size rep.data.unit u ≤ width := by cases u; exact hu
        dsimp only [Sum.elim_inl] at hsum
        omega
    | inr out =>
        change Q.size bd.out out ≤ outputWidth at hv
        dsimp only [Sum.elim_inr] at hsum
        omega
  have hpre (p) (hp : pre p) : Q.size (Caller.result (bd := bd) (rep.ty storeTy)) p ≤ 4 * frame := by
    have hprod := sizes.prod_le (StepClass.HasOption.option bd.out) (rep.ty storeTy) p
    have ho' := hiSize p.1 hp.1
    have hs' := hstore p.2 hp.2
    change Q.size (Caller.result (bd := bd) (rep.ty storeTy)) p ≤ _ at hprod
    omega
  have hmid (p) (hp : middle p) :
      Q.size (StepClass.HasProd.prod (StepClass.HasSum.sum rep.data.unit bd.out) (rep.ty storeTy)) p ≤ 4 * frame := by
    have hprod := sizes.prod_le (StepClass.HasSum.sum rep.data.unit bd.out) (rep.ty storeTy) p
    have ho' := hvSize p.1 hp.1
    have hs' := hstore p.2 hp.2
    omega
  have hd := firstAtomic_bound_of_width (iface := iface) mono control queryCost routing
    (rep.ty storeTy) boundary.optional (ResultReady (Q := Q) bd outputWidth) viewed inv (4 * frame) optionalTime
    (fun result hr => (hiSize result hr).trans (by omega))
    (fun saved h => (hstore saved h).trans (by omega)) (by
      intro result hr
      have hv : viewed (optionView result) := by
        cases result with
        | none => trivial
        | some out => exact hr out rfl
      exact ⟨hv, (hvSize _ hv).trans (by omega), hoptional result hr⟩)
  have hb := branchStore_bound_of_width sizes mono control queryCost routing dispatch
    (rep.ty storeTy) (cutoff rep data cost primitive) (finishSome rep bd boundary data cost primitive sampler)
    (fun p => inv p.2) (fun p => Q.size bd.out p.1 ≤ outputWidth ∧ inv p.2) post frame _ _
    (hh.trans hwf)
    (by intro p hp; have hu' : Q.size rep.data.unit p.1 ≤ width := by cases p.1; exact hu
        exact ⟨hu'.trans hwf, hstore p.2 hp⟩)
    (fun p hp => ⟨hp.1.trans ho, hstore p.2 hp.2⟩) hcut hfinish
  have hb' : Bounds control queryCost
      (.seq (.atomic (QD.distribute rep.data.unit bd.out (rep.ty storeTy)))
        (.branch (cutoff rep data cost primitive) (finishSome rep bd boundary data cost primitive sampler)))
      middle post (max (1029 * fee) (verifyTime + outputTime + 1033 * fee) + 4 * overhead (32 * frame)) := by
    apply Bounds.consequence control queryCost hb
    · intro p hp
      obtain ⟨tag, saved⟩ := p
      cases tag with
      | inl u => exact hp.2
      | inr out => exact hp
    · exact fun _ h => h
  have hall := seq_bound_of_width mono control queryCost routing _ _ pre middle post (4 * frame)
    (optionalTime + 2 * overhead (32 * (4 * frame))) _ hpre hmid hd hb'
  apply Bounds.time_mono control queryCost hall
  have h32 := mono (show 32 * frame ≤ 8192 * frame by omega)
  have h128 := mono (show 32 * (4 * frame) ≤ 8192 * frame by omega)
  dsimp only [fee]
  omega

end Signatures.Runtime.Schnorr.ListROM.NativePass
