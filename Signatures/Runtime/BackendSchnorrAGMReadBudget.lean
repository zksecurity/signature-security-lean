import Signatures.Runtime.BackendSchnorrAGMReadLocalCost

/-! Complete native Schnorr read budgets: default creation, cache traversal and
sampling, retained histories, restored state, and every control transition. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Read

open BackendProgram

def readTime (overhead : Nat → Nat)
    (width cap historyWidth messageTime pointTime fieldTime equalityTime sampleTime : Nat) : Nat :=
  cacheTime overhead width cap messageTime pointTime fieldTime equalityTime sampleTime +
    fieldTime + 800 * overhead (256 * frameWidth width cap historyWidth)

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

/-- This is an all-path bound on the actual complete read. Its only execution
premises are primitive and scalar-sampler contracts. The returned state retains
the same history-width bound and adds at most one cache entry. -/
theorem bound (width cap historyWidth messageTime pointTime fieldTime equalityTime sampleTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hm : ∀ a b : M, Q.size (rep.ty message) a ≤ 5 * width → Q.size (rep.ty message) b ≤ 5 * width →
      (primitiveBound .messageEq).time (a, b) ≤ messageTime)
    (hg : ∀ a b : G₁, Q.size (rep.ty point₁) a ≤ 5 * width → Q.size (rep.ty point₁) b ≤ 5 * width →
      (primitiveBound .point₁Eq).time (a, b) ≤ pointTime)
    (hz : (primitiveBound .zero).time () ≤ fieldTime)
    (hadd : ∀ a b : F, (primitiveBound .add).time (a, b) ≤ fieldTime)
    (heq : ∀ a b : F, (primitiveBound .scalarEq).time (a, b) ≤ equalityTime)
    (hd : Bounds control queryCost sampler (fun _ => True)
      (fun c => Q.size (rep.ty scalar) c ≤ width) sampleTime) :
    Bounds control queryCost (code rep data cost primitive sampler)
      (Input (Q := Q) rep width cap historyWidth)
      (Output (Q := Q) rep width (cap + 1) historyWidth)
      (readTime overhead width cap historyWidth messageTime pointTime fieldTime equalityTime sampleTime) := by
  let W := frameWidth width cap historyWidth
  let fee := overhead (256 * W)
  let cacheBudget := cacheTime overhead width cap messageTime pointTime fieldTime equalityTime sampleTime
  let pre := Input (Q := Q) rep width cap historyWidth
  let middle := fun p : retainedInputTy.Value (cryptoBase F G₁ G₂ K M) => CoreInput (Q := Q) rep width cap p.1 ∧ History (Q := Q) rep historyWidth p.2
  let returned := fun p : retainedOutputTy.Value (cryptoBase F G₁ G₂ K M) => CoreOutput (Q := Q) rep width (cap + 1) p.1 ∧ History (Q := Q) rep historyWidth p.2
  let post := Output (Q := Q) rep width (cap + 1) historyWidth
  have hw : width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have hpre := input_size rep sizes lists width cap historyWidth hh hb
  have hmiddle := retainedInput_size rep sizes lists width cap historyWidth hh hu hb
  have hreturned := retainedOutput_size rep sizes lists width cap historyWidth hh hb
  have hpost := output_size rep sizes lists width cap historyWidth hh hb
  have hsetup : Bounds control queryCost (.atomic (iface := iface) (setup rep data cost primitive))
      pre middle (fieldTime + 517 * fee) := by
    apply Bounds.atomic
    intro input hi
    have hout := pack_property rep sizes width cap historyWidth hh hb (hf 0) input hi
    have hin := hpre input hi
    have hsize := hmiddle (packValue input) hout
    have ht := setup_cost rep data cost primitive sizes laws dataLaws primitiveBound mono input W fieldTime
      (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw) ((hf 0).trans hw) hin hz
    have hc := (routing.localCall _ _).trans (mono (show
      Q.size (rep.ty inputTy) input + Q.size (rep.ty retainedInputTy) (packValue input) ≤ 256 * W by omega))
    exact ⟨hout, by dsimp only [fee]; omega⟩
  have hcache := cacheAccess_bound rep data cost primitive sampler sizes lists laws dataLaws primitiveBound mono
    control queryCost routing width cap messageTime pointTime fieldTime equalityTime sampleTime
    hh hu hb hf hm hg hz hadd heq hd
  have hcore : Bounds control queryCost (.first (rep.ty metaTy) (cacheAccess rep data cost primitive sampler))
      middle returned (cacheBudget + fee) := by
    apply Bounds.first control queryCost (rep.ty metaTy) (cacheAccess rep data cost primitive sampler)
      (CoreInput (Q := Q) rep width cap) (CoreOutput (Q := Q) rep width (cap + 1))
      (History (Q := Q) rep historyWidth) cacheBudget fee hcache
    intro saved hs output ho
    have hs' := history_size rep sizes width historyWidth hh hb saved hs
    have ho' := coreOutput_size rep sizes lists width (cap + 1) hh hb output ho
    apply (routing.retain _ _).trans (mono ?_)
    dsimp only [W, frameWidth]
    nlinarith
  have hfinish : Bounds control queryCost (.atomic (iface := iface) (finish rep data cost primitive))
      returned post (261 * fee) := by
    apply Bounds.atomic
    intro input hi
    have hout := return_property rep width (cap + 1) historyWidth hf input hi
    have hin := hreturned input hi
    have hsize := hpost (returnValue input) hout
    have ht := finish_cost rep data cost primitive sizes laws dataLaws primitiveBound mono input W
      (hh.trans hw) (hu.trans hw) hin
    have hc := (routing.localCall _ _).trans (mono (show
      Q.size (rep.ty retainedOutputTy) input + Q.size (rep.ty outputTy) (returnValue input) ≤ 256 * W by omega))
    exact ⟨hout, by dsimp only [fee]; omega⟩
  have htail := Bounds.seq control queryCost _ _ middle returned post (cacheBudget + fee) (261 * fee) fee
    hcore hfinish (by
      intro input hi output ho
      have hi' := hmiddle input hi
      have ho' := hreturned output ho
      exact (routing.sequence _ _).trans (mono (by
        dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env] at hi' ho' ⊢
        omega)))
  have hall := Bounds.seq control queryCost _ _ pre middle post (fieldTime + 517 * fee)
    (cacheBudget + fee + 261 * fee + fee) fee hsetup htail (by
      intro input hi output ho
      have hi' := hpre input hi
      have ho' := hmiddle output ho
      exact (routing.sequence _ _).trans (mono (by
        dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env] at hi' ho' ⊢
        omega)))
  intro input hi z hzrun
  obtain ⟨hout, ht⟩ := hall input hi z hzrun
  refine ⟨hout, ht.trans ?_⟩
  dsimp only [readTime, fee, W, cacheBudget]
  omega

end Signatures.Runtime.SchnorrAGM.Native.Read
