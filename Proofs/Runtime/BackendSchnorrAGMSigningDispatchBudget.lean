import Proofs.Runtime.BackendSchnorrAGMSigningDispatchLocalCost

/-! All-path signing-dispatch budget, derived from instruction and scalar-sampler
contracts. Request parsing, branching, and both reply constructors are charged. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.SigningDispatch

open BackendProgram

def dispatchTime (overhead : Nat → Nat)
    (width cap basisCap signedCap groupCap rowCap coeffCap fieldTime scaleTime groupTime
      messageTime pointTime sampleTime : Nat) : Nat :=
  let W := frameWidth width cap basisCap signedCap groupCap rowCap coeffCap
  let fee := overhead (256 * W)
  prepareTime overhead W groupCap +
    max (Signing.signingTime overhead width cap basisCap signedCap fieldTime scaleTime groupTime
      messageTime pointTime sampleTime + 262 * fee) (fieldTime + 517 * fee) + 5 * fee

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

theorem bound (width cap basisCap signedCap groupCap rowCap coeffCap fieldTime scaleTime groupTime
      messageTime pointTime sampleTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width) (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hz : (primitiveBound .zero).time () ≤ fieldTime)
    (hn : ∀ f : F, (primitiveBound .neg).time f ≤ fieldTime)
    (hs : ∀ f : F, ∀ g : G₁, (primitiveBound .scale₁).time (f, g) ≤ scaleTime)
    (hd : ∀ g h : G₁, (primitiveBound .sub₁).time (g, h) ≤ groupTime)
    (hm : ∀ a b : M, Q.size (rep.ty message) a ≤ 15 * width → Q.size (rep.ty message) b ≤ 15 * width →
      (primitiveBound .messageEq).time (a, b) ≤ messageTime)
    (he : ∀ a b : G₁, Q.size (rep.ty point₁) a ≤ 15 * width → Q.size (rep.ty point₁) b ≤ 15 * width →
      (primitiveBound .point₁Eq).time (a, b) ≤ pointTime)
    (hsample : Bounds control queryCost sampler (fun _ => True) (fun f => Q.size (rep.ty scalar) f ≤ width) sampleTime) :
    Bounds control queryCost (code rep data cost primitive sampler)
      (Input (Q := Q) rep width cap basisCap signedCap groupCap rowCap coeffCap)
      (Output (Q := Q) rep width cap basisCap signedCap)
      (dispatchTime overhead width cap basisCap signedCap groupCap rowCap coeffCap fieldTime scaleTime groupTime
        messageTime pointTime sampleTime) := by
  let W := frameWidth width cap basisCap signedCap groupCap rowCap coeffCap
  let fee := overhead (256 * W)
  let preparationTime := prepareTime overhead W groupCap
  let signingBudget := Signing.signingTime overhead width cap basisCap signedCap fieldTime scaleTime groupTime
    messageTime pointTime sampleTime
  let pre := Input (Q := Q) rep width cap basisCap signedCap groupCap rowCap coeffCap
  let decoded := Signing.Input (Q := Q) rep width cap basisCap signedCap
  let signed := Signing.Output (Q := Q) rep width cap basisCap signedCap
  let middle := Sum.elim decoded decoded
  let post := Output (Q := Q) rep width cap basisCap signedCap
  have hw : width ≤ W := calc
    width ≤ Signing.frameWidth width cap basisCap signedCap := by dsimp [Signing.frameWidth]; nlinarith
    _ ≤ W := Nat.le_add_right _ _
  have hcoreWidth : Signing.frameWidth width cap basisCap signedCap ≤ W := Nat.le_add_right _ _
  have hdecoded (input : Signing.inputTy.Value (cryptoBase F G₁ G₂ K M)) (hi : decoded input) :
      Q.size (rep.ty Signing.inputTy) input ≤ W :=
    (Signing.input_size rep sizes lists width cap basisCap signedCap hh hb hf input hi).trans hcoreWidth
  have hsigned (input : Signing.outputTy.Value (cryptoBase F G₁ G₂ K M)) (hi : signed input) :
      Q.size (rep.ty Signing.outputTy) input ≤ W :=
    (Signing.output_size rep sizes lists width cap basisCap signedCap hh hb hf input hi).trans hcoreWidth
  have hpost (output : outputTy.Value (cryptoBase F G₁ G₂ K M)) (ho : post output) :
      Q.size (rep.ty outputTy) output ≤ W :=
    (output_size rep sizes lists width cap basisCap signedCap hh hb hf output ho).trans hcoreWidth
  have hmiddle (input : Signing.inputTy.Value (cryptoBase F G₁ G₂ K M) ⊕ Signing.inputTy.Value (cryptoBase F G₁ G₂ K M))
      (hi : middle input) : Q.size (StepClass.HasSum.sum (rep.ty Signing.inputTy) (rep.ty Signing.inputTy)) input ≤ 2 * W := by
    have hs := sizes.sum_le (rep.ty Signing.inputTy) (rep.ty Signing.inputTy) input
    cases input with
    | inl p => have hp := hdecoded p hi; simp only [Sum.elim] at hs; omega
    | inr p => have hp := hdecoded p hi; simp only [Sum.elim] at hs; omega
  have hroute : Bounds control queryCost (.atomic (iface := iface) (route rep data cost primitive))
      pre middle (preparationTime + 3 * fee) := by
    apply Bounds.atomic
    intro input hi
    have ho : middle (routeValue input) := by
      dsimp only [middle, routeValue]
      split <;> exact hi.decoded
    have hin := (input_size rep sizes lists width cap basisCap signedCap groupCap rowCap coeffCap hh hu hb hf hg input hi).1
    have hout := hmiddle (routeValue input) ho
    have ht := route_cost rep data cost primitive sizes lists laws dataLaws primitiveBound mono
      width cap basisCap signedCap groupCap rowCap coeffCap hh hu hb hf hg input hi
    have hc := (routing.localCall _ _).trans (mono (show Q.size (rep.ty inputTy) input +
      Q.size (StepClass.HasSum.sum (rep.ty Signing.inputTy) (rep.ty Signing.inputTy)) (routeValue input) ≤ 256 * W by omega))
    exact ⟨ho, by dsimp only [preparationTime, fee, W] at *; omega⟩
  have hsign : Bounds control queryCost (Signing.code rep data cost primitive sampler) decoded signed signingBudget :=
    Signing.bound rep data cost primitive sizes lists laws dataLaws primitiveBound mono control queryCost routing sampler
      width cap basisCap signedCap fieldTime scaleTime groupTime messageTime pointTime sampleTime
      hh hu hb hf hg hz hn hs hd hm he hsample
  have hwrap : Bounds control queryCost (.atomic (iface := iface) (wrap rep data cost primitive)) signed post (261 * fee) := by
    apply Bounds.atomic
    intro input hi
    have ho := wrap_property rep width cap basisCap signedCap input hi
    have hin := hsigned input hi
    have hout := hpost (wrapValue input) ho
    have ht := wrap_cost rep data cost primitive sizes lists laws dataLaws primitiveBound mono input W
      (hh.trans hw) (hu.trans hw) hin
    have hc := (routing.localCall _ _).trans (mono (show
      Q.size (rep.ty Signing.outputTy) input + Q.size (rep.ty outputTy) (wrapValue input) ≤ 256 * W by omega))
    exact ⟨ho, by dsimp only [fee]; omega⟩
  have haccept : Bounds control queryCost (accepted rep data cost primitive sampler) decoded post
      (signingBudget + 262 * fee) := by
    have h := Bounds.seq control queryCost _ _ decoded signed post signingBudget (261 * fee) fee hsign hwrap (by
      intro input hi output ho
      have hi' := hdecoded input hi
      have ho' := hsigned output ho
      exact (routing.sequence _ _).trans (mono (by omega)))
    intro input hi out hout
    obtain ⟨ho, ht⟩ := h input hi out hout
    exact ⟨ho, ht.trans (by omega)⟩
  have hreject : Bounds control queryCost (.atomic (iface := iface) (reject rep data cost primitive))
      decoded post (fieldTime + 517 * fee) := by
    apply Bounds.atomic
    intro input hi
    have ho := reject_property rep width cap basisCap signedCap (hf 0) input hi
    have hin := hdecoded input hi
    have hout := hpost (rejectValue input) ho
    have ht := reject_cost rep data cost primitive sizes lists laws dataLaws primitiveBound mono input W fieldTime
      (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw) ((hf 0).trans hw) hin hz
    have hc := (routing.localCall _ _).trans (mono (show
      Q.size (rep.ty Signing.inputTy) input + Q.size (rep.ty outputTy) (rejectValue input) ≤ 256 * W by omega))
    exact ⟨ho, by dsimp only [fee]; omega⟩
  have hbranch := Bounds.branch control queryCost (accepted rep data cost primitive sampler)
    (.atomic (reject rep data cost primitive)) decoded decoded post (signingBudget + 262 * fee) (fieldTime + 517 * fee) fee
    haccept hreject (by
      intro input hi
      have hs := hmiddle input hi
      exact (routing.branch _).trans (mono (by omega)))
  have hall := Bounds.seq control queryCost (.atomic (route rep data cost primitive))
    (.branch (accepted rep data cost primitive sampler) (.atomic (reject rep data cost primitive)))
    pre middle post (preparationTime + 3 * fee) (max (signingBudget + 262 * fee) (fieldTime + 517 * fee) + fee) fee
    hroute hbranch (by
      intro input hi output ho
      have hin := (input_size rep sizes lists width cap basisCap signedCap groupCap rowCap coeffCap hh hu hb hf hg input hi).1
      have hout := hmiddle output ho
      exact (routing.sequence _ _).trans (mono (by omega)))
  intro input hi out hout
  obtain ⟨ho, ht⟩ := hall input hi out hout
  exact ⟨ho, ht.trans (by dsimp only [dispatchTime, signingBudget, preparationTime, fee, W]; omega)⟩

end Signatures.Runtime.SchnorrAGM.Native.SigningDispatch
