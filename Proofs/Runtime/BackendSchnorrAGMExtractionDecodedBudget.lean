import Proofs.Runtime.BackendSchnorrAGMExtractionLocalCost

/-! Complete cost of decoded Schnorr extraction: chronological flattening,
entry read, retained response, field extraction, and all control transitions. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Extraction

open BackendProgram

def decodedTime (overhead : Nat → Nat)
    (width cap historyWidth basisCap coeffCap comparisonTime subtractTime incrementTime
      messageTime pointTime fieldTime mulTime equalityTime sampleTime divisionTime : Nat) : Nat :=
  Hash.hashTime overhead width cap historyWidth basisCap coeffCap comparisonTime subtractTime incrementTime
    messageTime pointTime fieldTime mulTime equalityTime sampleTime +
    3 * fieldTime + divisionTime + 1031 * overhead (1024 * Hash.frameWidth width cap coeffCap historyWidth)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)
  (width cap historyWidth basisCap coeffCap comparisonTime subtractTime incrementTime
      messageTime pointTime fieldTime mulTime equalityTime sampleTime : Nat)
  (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
  (hb : ∀ b, Q.size rep.data.bool b ≤ width)
  (hn : ∀ n ≤ basisCap + 1, Q.size rep.data.nat n ≤ width)
  (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
  (hEq : ∀ n ≤ basisCap, (primitiveBound .natEq).time (n, 0) ≤ comparisonTime)
  (hSub : ∀ n ≤ basisCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime)
  (hInc : ∀ n ≤ basisCap, (primitiveBound .natAdd).time (n, 1) ≤ incrementTime)
  (hm : ∀ a b : M, Q.size (rep.ty message) a ≤ 15 * width → Q.size (rep.ty message) b ≤ 15 * width →
    (primitiveBound .messageEq).time (a, b) ≤ messageTime)
  (hg : ∀ a b : G₁, Q.size (rep.ty point₁) a ≤ 15 * width → Q.size (rep.ty point₁) b ≤ 15 * width →
    (primitiveBound .point₁Eq).time (a, b) ≤ pointTime)
  (hz : (primitiveBound .zero).time () ≤ fieldTime)
  (hadd : ∀ a b : F, (primitiveBound .add).time (a, b) ≤ fieldTime)
  (hmul : ∀ a b : F, (primitiveBound .mul).time (a, b) ≤ mulTime)
  (heq : ∀ a b : F, (primitiveBound .scalarEq).time (a, b) ≤ equalityTime)
  (hd : Bounds control queryCost sampler (fun _ => True) (fun c => Q.size (rep.ty scalar) c ≤ width) sampleTime)

include sizes lists laws dataLaws mono routing hh hu hb hn hf hEq hSub hInc hm hg hz hadd hmul heq hd

theorem prepared_bound :
    Bounds control queryCost (prepared rep data cost primitive sampler)
      (Hash.Input (Q := Q) rep width cap historyWidth basisCap coeffCap)
      (EntryRead.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth)
      (Hash.hashTime overhead width cap historyWidth basisCap coeffCap comparisonTime subtractTime incrementTime
        messageTime pointTime fieldTime mulTime equalityTime sampleTime) := by
  let W := Hash.frameWidth width cap coeffCap historyWidth
  let fee := overhead (256 * W)
  let flatTime := Flatten.flattenTime overhead W basisCap coeffCap comparisonTime subtractTime incrementTime fieldTime mulTime fieldTime
  let readTime := Read.readTime overhead (3 * width) cap historyWidth messageTime pointTime fieldTime equalityTime sampleTime
  have hwide : width ≤ 3 * width := by omega
  have hp := Hash.prepare_bound (iface := iface) rep data cost primitive sizes lists laws dataLaws primitiveBound mono
    control queryCost routing width cap historyWidth basisCap coeffCap comparisonTime subtractTime incrementTime
    fieldTime mulTime hh hu hb hn hf hEq hSub hInc hz hmul hadd
  have hr := EntryRead.bound rep data cost primitive sampler sizes lists laws dataLaws primitiveBound mono
    control queryCost routing (3 * width) cap historyWidth messageTime pointTime fieldTime equalityTime sampleTime
    (hh.trans hwide) (hu.trans hwide) (fun b => (hb b).trans hwide) (fun f => (hf f).trans hwide)
    (fun a b ha hb => hm a b (by omega) (by omega))
    (fun a b ha hb => hg a b (by omega) (by omega)) hz hadd heq
    (by intro input hi z hrun; have h := hd input hi z hrun; exact ⟨h.1.trans hwide, h.2⟩)
  have hall := Bounds.seq control queryCost (.atomic (Hash.prepare rep data cost primitive))
    (EntryRead.code rep data cost primitive sampler)
    (Hash.Input (Q := Q) rep width cap historyWidth basisCap coeffCap)
    (Read.Input (Q := Q) rep (3 * width) cap historyWidth)
    (EntryRead.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth)
    (flatTime + 261 * fee) readTime fee hp hr (by
      intro input hi output ho
      have hin := (Hash.input_size rep sizes lists width cap historyWidth basisCap coeffCap hh hu hb hf input hi).1
      have hout := Read.input_size rep sizes lists (3 * width) cap historyWidth
        (hh.trans hwide) (fun b => (hb b).trans hwide) output ho
      apply (routing.sequence _ _).trans (mono ?_)
      dsimp only [W, Hash.frameWidth] at hin ⊢
      omega)
  intro input hi z hrun
  obtain ⟨ho, ht⟩ := hall input hi z hrun
  refine ⟨ho, ht.trans ?_⟩
  dsimp only [Hash.hashTime, flatTime, readTime, fee, W]
  omega

omit hn hEq hSub hInc hm hg hmul heq hd in
private theorem terminal_bound (divisionTime : Nat)
    (hsub : ∀ a b : F, (primitiveBound .sub).time (a, b) ≤ fieldTime)
    (hdiv : ∀ a b : F, (primitiveBound .div).time (a, b) ≤ divisionTime) :
    Bounds control queryCost (.atomic (iface := iface) (localCode rep data cost primitive finishExpression))
      (fun p => EntryRead.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth p.1 ∧
        Q.size (rep.ty scalar) p.2 ≤ width)
      (Read.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth)
      (3 * fieldTime + divisionTime +
        1029 * overhead (1024 * Hash.frameWidth width cap coeffCap historyWidth)) := by
  let W := Hash.frameWidth width cap coeffCap historyWidth
  have hw : width ≤ W := by dsimp only [W, Hash.frameWidth, Read.frameWidth]; nlinarith
  have hwide : width ≤ 3 * width := by omega
  have hreadWidth : Read.frameWidth (3 * width) cap historyWidth ≤ W := by
    dsimp only [W, Hash.frameWidth]; omega
  apply Bounds.atomic
  intro input hi
  have ho : Read.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth (finishValue input) :=
    ⟨(hf _).trans hwide, hi.1.2⟩
  have hin : Q.size (rep.ty terminalTy) input ≤ 3 * W := by
    have hp := (EntryRead.output_size rep sizes lists (3 * width) cap historyWidth (by omega)
      (fun b => (hb b).trans hwide) input.1 hi.1).trans hreadWidth
    have hs := hi.2
    exact (sizes.prod_le (rep.ty EntryRead.outputTy) (rep.ty scalar) input).trans (by omega)
  have hout := (Read.output_size rep sizes lists (3 * width) cap historyWidth (by omega)
    (fun b => (hb b).trans hwide) (finishValue input) ho).trans hreadWidth
  have ht := finish_cost rep data cost primitive sizes laws dataLaws primitiveBound mono input (3 * W) fieldTime divisionTime
    (by omega) (by omega) (fun b => (hb b).trans (by omega)) (fun f => (hf f).trans (by omega)) hin hz hsub hadd hdiv
  have hfee := mono (show 256 * (3 * W) ≤ 1024 * W by omega)
  have hc := (routing.localCall _ _).trans (mono (show
    Q.size (rep.ty terminalTy) input + Q.size (rep.ty Read.outputTy) (finishValue input) ≤ 1024 * W by omega))
  refine ⟨ho, ?_⟩
  change Q.cost (localCode rep data cost primitive finishExpression) input +
    control.localCall (Q.size (rep.ty terminalTy) input) (Q.size (rep.ty Read.outputTy) (finishValue input)) ≤ _
  change _ ≤ 3 * fieldTime + divisionTime + 1029 * overhead (1024 * W)
  omega

omit hn hEq hSub hInc hm hg hmul heq hd in
private theorem decoded_bound_of_prepared
    (body : Code Q unifSpec iface (rep.ty Hash.inputTy) (rep.ty EntryRead.outputTy))
    (bodyTime divisionTime : Nat)
    (hprepared : Bounds control queryCost body
      (Hash.Input (Q := Q) rep width cap historyWidth basisCap coeffCap)
      (EntryRead.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth) bodyTime)
    (hsub : ∀ a b : F, (primitiveBound .sub).time (a, b) ≤ fieldTime)
    (hdiv : ∀ a b : F, (primitiveBound .div).time (a, b) ≤ divisionTime) :
    Bounds control queryCost (.seq (.first (rep.ty scalar) body)
        (.atomic (localCode rep data cost primitive finishExpression)))
      (fun p => Hash.Input (Q := Q) rep width cap historyWidth basisCap coeffCap p.1 ∧ Q.size (rep.ty scalar) p.2 ≤ width)
      (Read.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth)
      (bodyTime + 3 * fieldTime + divisionTime +
        1031 * overhead (1024 * Hash.frameWidth width cap coeffCap historyWidth)) := by
  let W := Hash.frameWidth width cap coeffCap historyWidth
  let fee := overhead (1024 * W)
  let pre := fun p : decodedTy.Value (cryptoBase F G₁ G₂ K M) =>
    Hash.Input (Q := Q) rep width cap historyWidth basisCap coeffCap p.1 ∧ Q.size (rep.ty scalar) p.2 ≤ width
  let middle := fun p : terminalTy.Value (cryptoBase F G₁ G₂ K M) =>
    EntryRead.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth p.1 ∧ Q.size (rep.ty scalar) p.2 ≤ width
  let post := Read.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth
  have hw : width ≤ W := by dsimp only [W, Hash.frameWidth, Read.frameWidth]; nlinarith
  have hwide : width ≤ 3 * width := by omega
  have hreadWidth : Read.frameWidth (3 * width) cap historyWidth ≤ W := by dsimp only [W, Hash.frameWidth]; omega
  have hpre (p) (hi : pre p) : Q.size (rep.ty decodedTy) p ≤ 3 * W := by
    have hp := (Hash.input_size rep sizes lists width cap historyWidth basisCap coeffCap hh hu hb hf p.1 hi.1).1
    have hs := hi.2
    exact (sizes.prod_le (rep.ty Hash.inputTy) (rep.ty scalar) p).trans (by omega)
  have hmid (p) (hi : middle p) : Q.size (rep.ty terminalTy) p ≤ 3 * W := by
    have hp := (EntryRead.output_size rep sizes lists (3 * width) cap historyWidth (by omega)
      (fun b => (hb b).trans hwide) p.1 hi.1).trans hreadWidth
    have hs := hi.2
    exact (sizes.prod_le (rep.ty EntryRead.outputTy) (rep.ty scalar) p).trans (by omega)
  have hfirst : Bounds control queryCost (.first (rep.ty scalar) body)
      pre middle (bodyTime + fee) := by
    apply Bounds.first control queryCost (rep.ty scalar) _
      (Hash.Input (Q := Q) rep width cap historyWidth basisCap coeffCap)
      (EntryRead.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth)
      (fun z => Q.size (rep.ty scalar) z ≤ width) bodyTime fee hprepared
    intro saved hs output ho
    have hp := (EntryRead.output_size rep sizes lists (3 * width) cap historyWidth (by omega)
      (fun b => (hb b).trans hwide) output ho).trans hreadWidth
    exact (routing.retain _ _).trans (mono (by omega))
  have hfinish := terminal_bound (iface := iface) rep data cost primitive sizes lists laws dataLaws primitiveBound mono
    control queryCost routing width cap historyWidth coeffCap fieldTime hh hu hb hf hz hadd divisionTime hsub hdiv
  have hall := Bounds.seq control queryCost _ _ pre middle post (bodyTime + fee)
    (3 * fieldTime + divisionTime + 1029 * fee) fee hfirst hfinish (by
      intro input hi output ho
      have hin := hpre input hi
      have hout := hmid output ho
      apply (routing.sequence _ _).trans (mono ?_)
      change Q.size (rep.ty decodedTy) input + Q.size (rep.ty terminalTy) output ≤ _
      omega)
  change Bounds control queryCost (.seq (.first (rep.ty scalar) body)
        (.atomic (localCode rep data cost primitive finishExpression))) pre post
    (bodyTime + fee + (3 * fieldTime + divisionTime + 1029 * fee) + fee) at hall
  intro input hi z hrun
  obtain ⟨ho, ht⟩ := hall input hi z hrun
  refine ⟨ho, ht.trans ?_⟩
  dsimp only [fee, W]
  omega

theorem decoded_bound (divisionTime : Nat)
    (hsub : ∀ a b : F, (primitiveBound .sub).time (a, b) ≤ fieldTime)
    (hdiv : ∀ a b : F, (primitiveBound .div).time (a, b) ≤ divisionTime) :
    Bounds control queryCost (decoded rep data cost primitive sampler)
      (fun p => Hash.Input (Q := Q) rep width cap historyWidth basisCap coeffCap p.1 ∧ Q.size (rep.ty scalar) p.2 ≤ width)
      (Read.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth)
      (decodedTime overhead width cap historyWidth basisCap coeffCap comparisonTime subtractTime incrementTime
        messageTime pointTime fieldTime mulTime equalityTime sampleTime divisionTime) := by
  have hp := prepared_bound rep data cost primitive sampler sizes lists laws dataLaws primitiveBound mono control queryCost routing
    width cap historyWidth basisCap coeffCap comparisonTime subtractTime incrementTime messageTime pointTime fieldTime mulTime equalityTime sampleTime
    hh hu hb hn hf hEq hSub hInc hm hg hz hadd hmul heq hd
  exact decoded_bound_of_prepared rep data cost primitive sizes lists laws dataLaws primitiveBound mono control queryCost routing
    width cap historyWidth basisCap coeffCap fieldTime hh hu hb hf hz hadd
    (prepared rep data cost primitive sampler) _ divisionTime hp hsub hdiv

end Signatures.Runtime.SchnorrAGM.Native.Extraction
