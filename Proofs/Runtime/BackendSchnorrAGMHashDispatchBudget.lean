import Proofs.Runtime.BackendSchnorrAGMHashDispatchRouting

/-! Complete all-path budget for Schnorr hash dispatch, including malformed
input, both singleton scans, branch selection and rejection-state construction. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.HashDispatch

open BackendProgram

def dispatchTime (overhead : Nat → Nat)
    (width cap historyWidth basisCap groupCap rowCap coeffCap comparisonTime subtractTime incrementTime
      messageTime pointTime fieldTime mulTime equalityTime sampleTime pointZeroTime : Nat) : Nat :=
  let W := frameWidth width cap historyWidth groupCap rowCap coeffCap
  let fee := overhead (4096 * W)
  prepareTime overhead W groupCap rowCap pointZeroTime +
    max (Hash.hashTime overhead width cap historyWidth basisCap coeffCap comparisonTime subtractTime incrementTime
      messageTime pointTime fieldTime mulTime equalityTime sampleTime) (fieldTime + 517 * fee) + 5 * fee

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

include sizes lists laws dataLaws mono routing

theorem bound (width cap historyWidth basisCap groupCap rowCap coeffCap comparisonTime subtractTime incrementTime
      messageTime pointTime fieldTime mulTime equalityTime sampleTime pointZeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ basisCap + 1, Q.size rep.data.nat n ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg0 : Q.size (rep.ty point₁) (0 : G₁) ≤ width)
    (hEq : ∀ n ≤ basisCap, (primitiveBound .natEq).time (n, 0) ≤ comparisonTime)
    (hSub : ∀ n ≤ basisCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime)
    (hInc : ∀ n ≤ basisCap, (primitiveBound .natAdd).time (n, 1) ≤ incrementTime)
    (hm : ∀ a b : M, Q.size (rep.ty message) a ≤ 15 * width → Q.size (rep.ty message) b ≤ 15 * width →
      (primitiveBound .messageEq).time (a, b) ≤ messageTime)
    (hg : ∀ a b : G₁, Q.size (rep.ty point₁) a ≤ 15 * width → Q.size (rep.ty point₁) b ≤ 15 * width →
      (primitiveBound .point₁Eq).time (a, b) ≤ pointTime)
    (hz : (primitiveBound .zero).time () ≤ fieldTime)
    (hz0 : (primitiveBound .zero₁).time () ≤ pointZeroTime)
    (hadd : ∀ a b : F, (primitiveBound .add).time (a, b) ≤ fieldTime)
    (hmul : ∀ a b : F, (primitiveBound .mul).time (a, b) ≤ mulTime)
    (heq : ∀ a b : F, (primitiveBound .scalarEq).time (a, b) ≤ equalityTime)
    (hd : Bounds control queryCost sampler (fun _ => True)
      (fun c => Q.size (rep.ty scalar) c ≤ width) sampleTime) :
    Bounds control queryCost (code rep data cost primitive sampler)
      (Input (Q := Q) rep width cap historyWidth basisCap groupCap rowCap coeffCap)
      (fun out => Read.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth out ∧
        out.2.2.1.length ≤ basisCap)
      (dispatchTime overhead width cap historyWidth basisCap groupCap rowCap coeffCap comparisonTime subtractTime incrementTime
        messageTime pointTime fieldTime mulTime equalityTime sampleTime pointZeroTime) := by
  let W := frameWidth width cap historyWidth groupCap rowCap coeffCap
  let fee := overhead (4096 * W)
  let preparationTime := prepareTime overhead W groupCap rowCap pointZeroTime
  let hashBudget := Hash.hashTime overhead width cap historyWidth basisCap coeffCap comparisonTime subtractTime incrementTime
    messageTime pointTime fieldTime mulTime equalityTime sampleTime
  let pre := Input (Q := Q) rep width cap historyWidth basisCap groupCap rowCap coeffCap
  let decoded := Hash.Input (Q := Q) rep width cap historyWidth basisCap coeffCap
  let middle := Sum.elim decoded decoded
  let post := fun out => Read.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth out ∧ out.2.2.1.length ≤ basisCap
  have hw : width ≤ W := by
    have h := Nat.mul_le_mul_right width (show 1 ≤
      4 * groupCap + 4 * rowCap * (coeffCap + 1) + 4 * coeffCap + 128 by omega)
    dsimp only [W, frameWidth]
    omega
  have hhashWidth : Hash.frameWidth width cap coeffCap historyWidth ≤ W := by
    have h := Nat.mul_le_mul_right width (show 4 * coeffCap + 64 ≤
      4 * groupCap + 4 * rowCap * (coeffCap + 1) + 4 * coeffCap + 128 by omega)
    dsimp only [W, frameWidth, Hash.frameWidth]
    omega
  have hdecoded (input : Hash.inputTy.Value (cryptoBase F G₁ G₂ K M)) (hi : decoded input) :
      Q.size (rep.ty Hash.inputTy) input ≤ W :=
    (Hash.input_size rep sizes lists width cap historyWidth basisCap coeffCap hh hu hb hf input hi).1.trans hhashWidth
  have hmiddle (input : Hash.inputTy.Value (cryptoBase F G₁ G₂ K M) ⊕ Hash.inputTy.Value (cryptoBase F G₁ G₂ K M))
      (hi : middle input) : Q.size (StepClass.HasSum.sum (rep.ty Hash.inputTy) (rep.ty Hash.inputTy)) input ≤ 2 * W := by
    have hs := sizes.sum_le (rep.ty Hash.inputTy) (rep.ty Hash.inputTy) input
    cases input with
    | inl p => have hp := hdecoded p hi; simp only [Sum.elim] at hs; omega
    | inr p => have hp := hdecoded p hi; simp only [Sum.elim] at hs; omega
  have hroute : Bounds control queryCost (.atomic (iface := iface) (route rep data cost primitive))
      pre middle (preparationTime + 3 * fee) := by
    apply Bounds.atomic
    intro input hi
    have ho := route_property rep sizes width cap historyWidth basisCap groupCap rowCap coeffCap hh hg0 input hi
    have hin := (input_size rep sizes lists width cap historyWidth basisCap groupCap rowCap coeffCap hh hu hb hf input hi).1
    have hout := hmiddle (routeValue input) ho
    have ht := route_cost rep data cost primitive sizes lists laws dataLaws primitiveBound mono
      width cap historyWidth basisCap groupCap rowCap coeffCap pointZeroTime hh hu hb hf hg0 hz0 input hi
    have hc := (routing.localCall _ _).trans (mono (show Q.size (rep.ty inputTy) input +
      Q.size (StepClass.HasSum.sum (rep.ty Hash.inputTy) (rep.ty Hash.inputTy)) (routeValue input) ≤ 4096 * W by omega))
    exact ⟨ho, by dsimp only [preparationTime, fee, W] at *; omega⟩
  have hhash : Bounds control queryCost (Hash.code rep data cost primitive sampler) decoded post hashBudget :=
    Hash.bound rep data cost primitive sampler sizes lists laws dataLaws primitiveBound mono control queryCost routing
      width cap historyWidth basisCap coeffCap comparisonTime subtractTime incrementTime messageTime pointTime fieldTime mulTime equalityTime sampleTime
      hh hu hb hn hf hEq hSub hInc hm hg hz hadd hmul heq hd
  have hreject : Bounds control queryCost (.atomic (iface := iface) (reject rep data cost primitive))
      decoded post (fieldTime + 517 * fee) := by
    apply Bounds.atomic
    intro input hi
    have ho := reject_property rep width cap historyWidth basisCap coeffCap (hf 0) input hi
    have hin := hdecoded input hi
    have hout := Read.output_size rep sizes lists (3 * width) cap historyWidth (by omega)
      (fun b => (hb b).trans (by omega)) (rejectValue input) ho.1
    have ht := reject_cost rep data cost primitive sizes laws dataLaws primitiveBound mono input W fieldTime
      (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw) ((hf 0).trans hw) hin hz
    have hfee := mono (show 256 * W ≤ 4096 * W by omega)
    have hc := (routing.localCall _ _).trans (mono (show Q.size (rep.ty Hash.inputTy) input +
      Q.size (rep.ty Read.outputTy) (rejectValue input) ≤ 4096 * W by dsimp only [W, frameWidth] at *; omega))
    exact ⟨ho, by dsimp only [fee]; omega⟩
  have hbranch := Bounds.branch control queryCost (Hash.code rep data cost primitive sampler)
    (.atomic (reject rep data cost primitive)) decoded decoded post hashBudget (fieldTime + 517 * fee) fee
    hhash hreject (by
      intro input hi
      have hs := hmiddle input hi
      exact (routing.branch _).trans (mono (by omega)))
  have hall := Bounds.seq control queryCost (.atomic (route rep data cost primitive))
    (.branch (Hash.code rep data cost primitive sampler) (.atomic (reject rep data cost primitive)))
    pre middle post (preparationTime + 3 * fee) (max hashBudget (fieldTime + 517 * fee) + fee) fee
    hroute hbranch (by
      intro input hi output ho
      have hin := (input_size rep sizes lists width cap historyWidth basisCap groupCap rowCap coeffCap hh hu hb hf input hi).1
      have hout := hmiddle output ho
      exact (routing.sequence _ _).trans (mono (by omega)))
  change Bounds control queryCost (code rep data cost primitive sampler) pre post
    (preparationTime + 3 * fee + (max hashBudget (fieldTime + 517 * fee) + fee) + fee) at hall
  intro input hi z hzrun
  obtain ⟨ho, ht⟩ := hall input hi z hzrun
  refine ⟨ho, ht.trans ?_⟩
  dsimp only [dispatchTime, hashBudget, preparationTime, fee, W]
  omega

end Signatures.Runtime.SchnorrAGM.Native.HashDispatch
