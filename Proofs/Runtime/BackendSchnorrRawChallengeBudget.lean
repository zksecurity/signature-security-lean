import Proofs.Runtime.BackendSchnorrRawChallengeCost
import Proofs.Runtime.PolynomialResources

/-! Complete native challenge-draw resources. The supplied sampler is actual
scalar-sampling code with its own budget; the tape handler's budget is derived.
The runtime formula has polynomial closure from its component resources. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativeChallenge

open BackendProgram

def runtimeBound (overhead : Nat → Nat)
    (width savedCap remainingCap comparisonTime zeroTime sampleTime : Nat) : Nat :=
  let fee := overhead (256 * NativeUniform.saveFrameWidth width savedCap remainingCap)
  prepareTime overhead width savedCap remainingCap comparisonTime zeroTime +
    max (2 * fee) (sampleTime + saveTime overhead width savedCap remainingCap + 8 * fee) + 5 * fee

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
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes lists laws dataLaws mono routing

theorem bound (width savedCap remainingCap comparisonTime zeroTime sampleTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hn0 : Q.size rep.data.nat 0 ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (hcompare : ∀ n, Q.size rep.data.nat n ≤ width →
      (primitiveBound .natEq).time (n, 1) ≤ comparisonTime)
    (hzero : (primitiveBound .zero).time () ≤ zeroTime)
    (hsample : Bounds control queryCost sampler (fun _ => True)
      (fun f => Q.size (rep.ty scalar) f ≤ width) sampleTime) :
    Bounds control queryCost (code rep data cost primitive sampler)
      (NativeUniform.StateBound (Q := Q) rep width savedCap remainingCap)
      (Output (Q := Q) rep width (savedCap + 1) remainingCap)
      (runtimeBound overhead width savedCap remainingCap comparisonTime zeroTime sampleTime) := by
  let W := NativeUniform.saveFrameWidth width savedCap remainingCap
  let fee := overhead (256 * W)
  let P := prepareTime overhead width savedCap remainingCap comparisonTime zeroTime
  let S := saveTime overhead width savedCap remainingCap
  let pre := NativeUniform.StateBound (Q := Q) rep width savedCap remainingCap
  let ready := Output (Q := Q) rep width savedCap remainingCap
  let framed := fun input : Unit × stateTy.Value (cryptoBase F G₁ G₂ K M) => pre input.2
  let middle := Sum.elim ready ready
  let post := Output (Q := Q) rep width (savedCap + 1) remainingCap
  have hw : width ≤ W := by dsimp [W, NativeUniform.saveFrameWidth]; nlinarith
  have preSize (state) (hi : pre state) : Q.size (rep.ty stateTy) state ≤ W :=
    (NativeUniform.state_size rep sizes lists width savedCap remainingCap hh state hi).trans
      (by dsimp [W, NativeUniform.saveFrameWidth]; nlinarith)
  have readySize (input) (hi : ready input) : Q.size (rep.ty drawTy) input ≤ W :=
    (output_size rep sizes lists width savedCap remainingCap hh input hi).trans
      (by dsimp [W, NativeUniform.saveFrameWidth]; nlinarith)
  have postSize (output) (ho : post output) : Q.size (rep.ty drawTy) output ≤ W :=
    (output_size rep sizes lists width (savedCap + 1) remainingCap hh output ho).trans
      (by dsimp [W, NativeUniform.saveFrameWidth]; nlinarith)
  have frameSize (input) (hi : framed input) :
      Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty stateTy)) input ≤ 3 * W := by
    obtain ⟨⟨⟩, state⟩ := input
    have hs := preSize state hi
    have hp := sizes.prod_le rep.data.unit (rep.ty stateTy) ((), state)
    exact hp.trans (by dsimp only; omega)
  have middleSize (value) (hv : middle value) :
      Q.size (StepClass.HasSum.sum (rep.ty drawTy) (rep.ty drawTy)) value ≤ 2 * W := by
    have hs := sizes.sum_le (rep.ty drawTy) (rep.ty drawTy) value
    cases value with
    | inl value => have h := readySize value hv; dsimp only [Sum.elim] at hs; omega
    | inr value => have h := readySize value hv; dsimp only [Sum.elim] at hs; omega
  have hchoose : Bounds control queryCost (.atomic (iface := iface) (choose rep data cost primitive))
      pre middle (P + 3 * fee) := by
    apply Bounds.atomic
    intro state hi
    have hready := prepare_property rep width savedCap remainingCap hz state hi
    have hpost : middle (if (prepareValue state).1 then .inl (prepareValue state).2
        else .inr (prepareValue state).2) := by split <;> exact hready
    have hin := preSize state hi
    have hout := middleSize _ hpost
    have hprepare : Q.size (rep.ty prepareTy) (prepareValue state) ≤ W :=
      (prepare_size rep sizes lists width savedCap remainingCap hh hb hz state hi).trans
        (by dsimp [W, NativeUniform.saveFrameWidth]; nlinarith)
    have ht := prepare_cost rep data cost primitive sizes lists laws dataLaws primitiveBound mono
      width savedCap remainingCap comparisonTime zeroTime hh hu hb hz hn0 hn1 state hi
      (fun x member => hcompare x.1 (hi.2.1 x member).1) hzero
    have hselect := (dataLaws.select (rep.ty drawTy) (prepareValue state)).trans
      (mono (show Q.size (rep.ty prepareTy) (prepareValue state) +
        Q.size (StepClass.HasSum.sum (rep.ty drawTy) (rep.ty drawTy))
          (if (prepareValue state).1 then .inl (prepareValue state).2 else .inr (prepareValue state).2) ≤ 256 * W by omega))
    have hcomp := laws.compose (prepare rep data cost primitive) (data.select (rep.ty drawTy)) state
    have hj := mono (show Q.size (rep.ty stateTy) state + Q.size (rep.ty prepareTy) (prepareValue state) +
      Q.size (StepClass.HasSum.sum (rep.ty drawTy) (rep.ty drawTy))
        (if (prepareValue state).1 then .inl (prepareValue state).2 else .inr (prepareValue state).2) ≤ 256 * W by omega)
    have hc := (routing.localCall _ _).trans (mono (show Q.size (rep.ty stateTy) state +
      Q.size (StepClass.HasSum.sum (rep.ty drawTy) (rep.ty drawTy))
        (if (prepareValue state).1 then .inl (prepareValue state).2 else .inr (prepareValue state).2) ≤ 256 * W by omega))
    exact ⟨hpost, by change Q.cost (Q.compose _ _) state + _ ≤ _; dsimp only [P, fee]; omega⟩
  have hhit : Bounds control queryCost (.atomic (iface := iface) (Q.identity (rep.ty drawTy))) ready post
      (2 * fee) := by
    apply Bounds.atomic
    intro input hi
    have ho : post input := ⟨hi.1,
      NativeUniform.tape_mono rep width savedCap (savedCap + 1) _ hi.2.1 (by omega), hi.2.2⟩
    have hin := readySize input hi
    have ht := (laws.identity (rep.ty drawTy) input).trans (mono (show Q.size (rep.ty drawTy) input ≤ 256 * W by omega))
    have hc := (routing.localCall _ _).trans (mono (show Q.size (rep.ty drawTy) input +
      Q.size (rep.ty drawTy) input ≤ 256 * W by omega))
    exact ⟨ho, (Nat.add_le_add ht hc).trans (by dsimp only [fee]; omega)⟩
  have hrequest : Bounds control queryCost (.atomic (iface := iface) (requestFrame rep data)) ready framed
      (4 * fee) := by
    apply Bounds.atomic
    intro input hi
    have hin := readySize input hi
    have hs := preSize input.2 hi.2
    have hout := frameSize ((), input.2) hi.2
    have hp := laws.pair (data.unit (rep.ty drawTy)) (QP.snd (rep.ty scalar) (rep.ty stateTy)) input
    have ht := (dataLaws.unit (rep.ty drawTy) input).trans
      (mono (show Q.size (rep.ty drawTy) input + Q.size rep.data.unit () ≤ 256 * W by omega))
    have hd := (laws.snd (rep.ty scalar) (rep.ty stateTy) input).trans
      (mono (show Q.size (rep.ty drawTy) input + Q.size (rep.ty stateTy) input.2 ≤ 256 * W by omega))
    have hj := mono (show Q.size (rep.ty drawTy) input +
      Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty stateTy)) ((), input.2) ≤ 256 * W by omega)
    have hc := (routing.localCall _ _).trans hj
    exact ⟨hi.2, by change Q.cost (QP.pair _ _) input + _ ≤ _; dsimp only [fee]; omega⟩
  have hsampled : Bounds control queryCost (.first (rep.ty stateTy) sampler) framed ready (sampleTime + fee) := by
    intro input hi out hout
    apply Bounds.first control queryCost (rep.ty stateTy) sampler (fun _ => True)
      (fun f => Q.size (rep.ty scalar) f ≤ width) pre sampleTime fee hsample ?_
      input ⟨True.intro, hi⟩ out hout
    intro state hs value hv
    have hsize := preSize state hs
    exact (routing.retain _ _).trans (mono (by omega))
  have hsave : Bounds control queryCost (.atomic (iface := iface) (save rep data cost primitive)) ready post
      (S + fee) := by
    apply Bounds.atomic
    intro input hi
    have ho := save_property rep width savedCap remainingCap hn0 hn1 input hi
    have hin := readySize input hi
    have hout := postSize _ ho
    have ht := save_cost rep data cost primitive sizes lists laws dataLaws mono
      width savedCap remainingCap hh hu hn0 hn1 input hi
    have hc := (routing.localCall _ _).trans (mono (show Q.size (rep.ty drawTy) input +
      Q.size (rep.ty drawTy) (saveValue input) ≤ 256 * W by omega))
    exact ⟨ho, Nat.add_le_add ht hc⟩
  have htail := Bounds.seq control queryCost _ _ framed ready post (sampleTime + fee) (S + fee) fee hsampled hsave (by
    intro input hi value hv
    have hin := frameSize input hi
    have hout := readySize value hv
    exact (routing.sequence _ _).trans (mono (by dsimp only [LanguageRepresentation.ty] at hin hout ⊢; omega)))
  have hmiss := Bounds.seq control queryCost _ _ ready framed post (4 * fee)
    (sampleTime + fee + (S + fee) + fee) fee hrequest htail (by
      intro input hi value hv
      have hin := readySize input hi
      have hout := frameSize value hv
      exact (routing.sequence _ _).trans (mono (by dsimp only [LanguageRepresentation.ty] at hin hout ⊢; omega)))
  have hbranch := Bounds.branch control queryCost _ _ ready ready post (2 * fee)
    (4 * fee + (sampleTime + fee + (S + fee) + fee) + fee) fee hhit hmiss (by
      intro input hi
      have hin := middleSize input hi
      exact (routing.branch _).trans (mono (by omega)))
  have hall := Bounds.seq control queryCost _ _ pre middle post (P + 3 * fee)
    (max (2 * fee) (4 * fee + (sampleTime + fee + (S + fee) + fee) + fee) + fee) fee hchoose hbranch (by
      intro input hi value hv
      have hin := preSize input hi
      have hout := middleSize value hv
      exact (routing.sequence _ _).trans (mono (by omega)))
  intro input hi out hout
  obtain ⟨ho, ht⟩ := hall input hi out hout
  exact ⟨ho, ht.trans (by dsimp only [runtimeBound, P, S, fee, W] at *; omega)⟩

omit sizes lists laws dataLaws mono routing in
private theorem max_polynomial {f g : Nat → Nat}
    (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => max (f n) (g n)) :=
  (hf.add hg).of_le (fun _ => Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩)

omit sizes lists laws dataLaws mono routing in
theorem runtimeBound_polynomial (overhead : Nat → Nat → Nat)
    (width savedCap remainingCap comparisonTime zeroTime sampleTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hSaved : PolynomiallyBounded savedCap) (hRemaining : PolynomiallyBounded remainingCap)
    (hCompare : PolynomiallyBounded comparisonTime) (hZero : PolynomiallyBounded zeroTime)
    (hSample : PolynomiallyBounded sampleTime) :
    PolynomiallyBounded (fun n => runtimeBound (overhead n) (width n) (savedCap n) (remainingCap n)
      (comparisonTime n) (zeroTime n) (sampleTime n)) := by
  unfold runtimeBound prepareTime saveTime NativeUniform.saveFrameWidth SeedTape.NativeScan.scanTime
    SeedTape.NativeScan.forwardTime SeedTape.NativeScan.frameWidth ListSnoc.snocTime ListSnoc.frameWidth
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply max_polynomial
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

end Signatures.Runtime.Schnorr.RawTape.NativeChallenge
