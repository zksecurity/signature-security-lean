import Proofs.Runtime.BackendSchnorrRawUniformPrepareCost

/-! Complete native dynamic-private-draw budget. Scan, hit return, dynamic
sampling, chronological append and control routing are all charged. The numeric
arity bounds primitive/port inputs but does not occur in the runtime formula. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativeUniform

open BackendProgram

def runtimeBound (overhead : Nat → Nat)
    (width savedCap remainingCap comparisonTime zeroTime addTime requestTime responseTime queryTime : Nat) : Nat :=
  let fee := overhead (256 * saveFrameWidth width savedCap remainingCap)
  prepareTime overhead width savedCap remainingCap comparisonTime zeroTime addTime +
    max (261 * fee)
      (saveTime overhead width savedCap remainingCap zeroTime + requestTime + responseTime + queryTime +
        4 * overhead (8 * width) + 3 * fee) + 5 * fee

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {iface : Interface (C := C) unifSpec}
  (ports : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes lists laws dataLaws mono routing

theorem bound (width savedCap remainingCap arityCap comparisonTime zeroTime addTime
    requestTime responseTime queryTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hn : ∀ n ≤ arityCap + 2, Q.size rep.data.nat n ≤ width)
    (hcompare : ∀ a b, Q.size rep.data.nat a ≤ width → Q.size rep.data.nat b ≤ width →
      (primitiveBound .natEq).time (a, b) ≤ comparisonTime)
    (hzero : (primitiveBound .zero).time () ≤ zeroTime)
    (hadd : ∀ n ≤ arityCap, (primitiveBound .natAdd).time (n, 2) ≤ addTime)
    (hp : ∀ n ≤ arityCap, Q.size iface.position n ≤ width)
    (hr : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.size iface.response ⟨n, r⟩ ≤ width)
    (hrequest : ∀ n ≤ arityCap, Q.cost ports.request n ≤ requestTime)
    (hresponse : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.cost ports.response ⟨n, r⟩ ≤ responseTime)
    (hquery : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), queryCost n r +
      control.query (Q.size iface.position n) (Q.size iface.response ⟨n, r⟩) ≤ queryTime) :
    Bounds control queryCost (code rep data cost primitive ports)
      (fun input => input.1 ≤ arityCap ∧ StateBound (Q := Q) rep width savedCap remainingCap input.2)
      (InputBound (Q := Q) rep width (savedCap + 1) remainingCap)
      (runtimeBound overhead width savedCap remainingCap comparisonTime zeroTime addTime
        requestTime responseTime queryTime) := by
  let W := saveFrameWidth width savedCap remainingCap
  let fee := overhead (256 * W)
  let P := prepareTime overhead width savedCap remainingCap comparisonTime zeroTime addTime
  let S := saveTime overhead width savedCap remainingCap zeroTime
  let D := requestTime + responseTime + queryTime + 4 * overhead (8 * width)
  let pre := fun input : inputTy.Value (cryptoBase F G₁ G₂ K M) =>
    input.1 ≤ arityCap ∧ StateBound (Q := Q) rep width savedCap remainingCap input.2
  let ready := DrawBound (Q := Q) rep width savedCap remainingCap
  let auxiliary := InputBound (Q := Q) rep width savedCap remainingCap
  let missing := fun input : drawTy.Value (cryptoBase F G₁ G₂ K M) => input.1 ≤ arityCap ∧ auxiliary input.2
  let middle := Sum.elim ready missing
  let post := InputBound (Q := Q) rep width (savedCap + 1) remainingCap
  have hw : width ≤ W := by dsimp [W, saveFrameWidth]; nlinarith
  have inputProperty (input) (hi : pre input) : InputBound (Q := Q) rep width savedCap remainingCap input :=
    ⟨hn input.1 (hi.1.trans (Nat.le_add_right _ _)), hi.2⟩
  have missingProperty (input) (hi : missing input) : ready input :=
    ⟨hn input.1 (hi.1.trans (Nat.le_add_right _ _)), hi.2⟩
  have preSize (input) (hi : pre input) : Q.size (rep.ty inputTy) input ≤ W :=
    (input_size rep sizes lists width savedCap remainingCap hh input (inputProperty input hi)).trans
      (by dsimp [W, saveFrameWidth]; nlinarith)
  have readySize (input) (hi : ready input) : Q.size (rep.ty drawTy) input ≤ W :=
    (draw_size rep sizes lists width savedCap remainingCap hh input hi).trans
      (by dsimp [W, saveFrameWidth]; nlinarith)
  have auxiliarySize (input) (hi : auxiliary input) : Q.size (rep.ty auxTy) input ≤ W :=
    (input_size rep sizes lists width savedCap remainingCap hh input hi).trans
      (by dsimp [W, saveFrameWidth]; nlinarith)
  have postSize (output) (ho : post output) : Q.size (rep.ty inputTy) output ≤ W :=
    (input_size rep sizes lists width (savedCap + 1) remainingCap hh output ho).trans
      (by dsimp [W, saveFrameWidth]; nlinarith)
  have middleSize (value) (hv : middle value) :
      Q.size (StepClass.HasSum.sum (rep.ty drawTy) (rep.ty drawTy)) value ≤ 2 * W := by
    have hs := sizes.sum_le (rep.ty drawTy) (rep.ty drawTy) value
    cases value with
    | inl value => have h := readySize value hv; dsimp only [Sum.elim] at hs; omega
    | inr value => have h := readySize value (missingProperty value hv); dsimp only [Sum.elim] at hs; omega
  have hchoose : Bounds control queryCost (.atomic (iface := iface) (choose rep data cost primitive))
      pre middle (P + 3 * fee) := by
    apply Bounds.atomic
    intro input hi
    have htag := hn (input.1 + 2) (Nat.add_le_add_right hi.1 2)
    have hready := prepare_property rep width savedCap remainingCap input (inputProperty input hi) htag
    have hpost : middle (if (prepareValue input).1 then .inl (prepareValue input).2
        else .inr (prepareValue input).2) := by
      cases found : (SeedTape.pop (input.1 + 2) (0, (0 : F), 0) input.2.2).1 with
      | true => simpa [prepareValue, found, middle] using hready
      | false =>
          have hn' : (prepareValue input).2.1 ≤ arityCap := by simpa [prepareValue, found] using hi.1
          simpa [middle, missing, auxiliary, InputBound, prepareValue, found] using And.intro hn' hready.2
    have hin := preSize input hi
    have hout := middleSize _ hpost
    have hprepare : Q.size (rep.ty prepareTy) (prepareValue input) ≤ W :=
      (prepare_size rep sizes lists width savedCap remainingCap hh hb input (inputProperty input hi) htag).trans
        (by dsimp [W, saveFrameWidth]; nlinarith)
    have ht := prepare_cost rep data cost primitive sizes lists laws dataLaws primitiveBound mono
      width savedCap remainingCap comparisonTime zeroTime addTime hh hu hb hz
      (hn 0 (by omega)) (hn 2 (by omega)) input (inputProperty input hi) htag
      (fun x member => hcompare x.1 (input.1 + 2) (hi.2.2.1 x member).1 htag)
      hzero (hadd input.1 hi.1)
    have hselect := (dataLaws.select (rep.ty drawTy) (prepareValue input)).trans
      (mono (show Q.size (rep.ty prepareTy) (prepareValue input) +
        Q.size (StepClass.HasSum.sum (rep.ty drawTy) (rep.ty drawTy))
          (if (prepareValue input).1 then .inl (prepareValue input).2 else .inr (prepareValue input).2) ≤ 256 * W by omega))
    have hcomp := laws.compose (prepare rep data cost primitive) (data.select (rep.ty drawTy)) input
    have hj := mono (show Q.size (rep.ty inputTy) input + Q.size (rep.ty prepareTy) (prepareValue input) +
      Q.size (StepClass.HasSum.sum (rep.ty drawTy) (rep.ty drawTy))
        (if (prepareValue input).1 then .inl (prepareValue input).2 else .inr (prepareValue input).2) ≤ 256 * W by omega)
    have hc := (routing.localCall _ _).trans (mono (show Q.size (rep.ty inputTy) input +
      Q.size (StepClass.HasSum.sum (rep.ty drawTy) (rep.ty drawTy))
        (if (prepareValue input).1 then .inl (prepareValue input).2 else .inr (prepareValue input).2) ≤ 256 * W by omega))
    exact ⟨hpost, by change Q.cost (Q.compose _ _) input + _ ≤ _; dsimp only [P, fee]; omega⟩
  have hhit : Bounds control queryCost (.atomic (iface := iface) (hit rep data cost primitive)) ready post
      (261 * fee) := by
    apply Bounds.atomic
    intro input hi
    have result := hit_property rep width savedCap remainingCap input hi
    have ho : post (hitValue input) := ⟨result.1,
      tape_mono rep width savedCap (savedCap + 1) _ result.2.1 (by omega), result.2.2⟩
    have hin := readySize input hi
    have hout := postSize _ ho
    have ht := hit_cost rep data cost primitive sizes laws dataLaws primitiveBound mono input W
      (hh.trans hw) (hu.trans hw) hin
    have hc := (routing.localCall _ _).trans (mono (show Q.size (rep.ty drawTy) input +
      Q.size (rep.ty inputTy) (hitValue input) ≤ 256 * W by omega))
    exact ⟨ho, (Nat.add_le_add ht hc).trans (by dsimp only [fee]; omega)⟩
  have hsample := UniformSampling.bound rep.data ports mono control queryCost routing
    width arityCap requestTime responseTime queryTime
    (fun n h => hn n (by omega)) hp hr hrequest hresponse hquery
  have hretained := Bounds.first control queryCost (rep.ty auxTy) (UniformSampling.code rep.data ports)
    (fun n => n ≤ arityCap) (fun n => n ≤ arityCap ∧ Q.size rep.data.nat n ≤ width)
    auxiliary D fee hsample (by
      intro saved hs output ho
      have hsize := auxiliarySize saved hs
      exact (routing.retain _ _).trans (mono (by have := ho.2; omega)))
  have hdraw : Bounds control queryCost (.first (rep.ty auxTy) (UniformSampling.code rep.data ports))
      missing ready (D + fee) := by
    intro input hi out hout
    obtain ⟨ho, ht⟩ := hretained input hi out hout
    exact ⟨⟨ho.1.2, ho.2⟩, ht⟩
  have hsave : Bounds control queryCost (.atomic (iface := iface) (save rep data cost primitive)) ready post
      (S + fee) := by
    apply Bounds.atomic
    intro input hi
    have ho := save_property rep width savedCap remainingCap hz input hi
    have hin := readySize input hi
    have hout := postSize _ ho
    have ht := save_cost rep data cost primitive sizes lists laws dataLaws primitiveBound mono
      width savedCap remainingCap zeroTime hh hu hz hzero input hi
    have hc := (routing.localCall _ _).trans (mono (show Q.size (rep.ty drawTy) input +
      Q.size (rep.ty inputTy) (saveValue input) ≤ 256 * W by omega))
    exact ⟨ho, Nat.add_le_add ht hc⟩
  have hmiss := Bounds.seq control queryCost _ _ missing ready post (D + fee) (S + fee) fee hdraw hsave (by
    intro input hi value hv
    have hin := readySize input (missingProperty input hi)
    have hout := readySize value hv
    exact (routing.sequence _ _).trans (mono (by
      dsimp only [LanguageRepresentation.ty] at hin hout ⊢
      omega)))
  have hbranch := Bounds.branch control queryCost _ _ ready missing post
    (261 * fee) (D + fee + (S + fee) + fee) fee hhit hmiss (by
      intro input hi
      have hin := middleSize input hi
      exact (routing.branch _).trans (mono (by
        dsimp only [LanguageRepresentation.ty] at hin ⊢
        omega)))
  have hall := Bounds.seq control queryCost _ _ pre middle post (P + 3 * fee)
    (max (261 * fee) (D + fee + (S + fee) + fee) + fee) fee hchoose hbranch (by
      intro input hi value hv
      have hin := preSize input hi
      have hout := middleSize value hv
      exact (routing.sequence _ _).trans (mono (by
        dsimp only [LanguageRepresentation.ty] at hin hout ⊢
        omega)))
  intro input hi out hout
  obtain ⟨ho, ht⟩ := hall input hi out hout
  exact ⟨ho, ht.trans (by dsimp only [runtimeBound, P, S, D, fee, W] at *; omega)⟩

end Signatures.Runtime.Schnorr.RawTape.NativeUniform
