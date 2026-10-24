import Proofs.Runtime.BackendSchnorrAGMSigningLocalCost

/-! Complete accepted-signing budgets, derived from primitive instructions,
scalar sampling and representation/control contracts. Includes the two draws,
arithmetic, both histories, programming, retained state and every adapter. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Signing

open BackendProgram

def sampledTime (overhead : Nat → Nat)
    (width cap basisCap signedCap fieldTime scaleTime groupTime messageTime pointTime : Nat) : Nat :=
  let W := frameWidth width cap basisCap signedCap
  2 * fieldTime + 2 * scaleTime + groupTime +
    ListSnoc.snocTime overhead (16 * W) signedCap + ListSnoc.snocTime overhead (16 * W) basisCap +
    Programming.programmingTime overhead (15 * width) cap messageTime pointTime + 1820 * overhead (256 * W)

def signingTime (overhead : Nat → Nat)
    (width cap basisCap signedCap fieldTime scaleTime groupTime messageTime pointTime sampleTime : Nat) : Nat :=
  sampledTime overhead width cap basisCap signedCap fieldTime scaleTime groupTime messageTime pointTime +
    2 * sampleTime + 20 * overhead (256 * frameWidth width cap basisCap signedCap)

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
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes lists laws dataLaws mono routing

theorem sampled_bound (width cap basisCap signedCap fieldTime scaleTime groupTime messageTime pointTime : Nat)
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
      (primitiveBound .point₁Eq).time (a, b) ≤ pointTime) :
    Bounds control queryCost (sampledCode rep data cost primitive (iface := iface))
      (fun input => Input (Q := Q) rep width cap basisCap signedCap input.2)
      (Output (Q := Q) rep width cap basisCap signedCap)
      (sampledTime overhead width cap basisCap signedCap fieldTime scaleTime groupTime messageTime pointTime) := by
  let W := frameWidth width cap basisCap signedCap
  let fee := overhead (256 * W)
  let A := 2 * fieldTime + 2 * scaleTime + groupTime
  let H := ListSnoc.snocTime overhead (16 * W) signedCap + ListSnoc.snocTime overhead (16 * W) basisCap
  let P := Programming.programmingTime overhead (15 * width) cap messageTime pointTime
  let pre := fun input : sampledTy.Value (cryptoBase F G₁ G₂ K M) => Input (Q := Q) rep width cap basisCap signedCap input.2
  let work := Work (Q := Q) rep width cap basisCap signedCap
  let middle := ProgramInput (Q := Q) rep width cap basisCap signedCap
  let returned := ProgramOutput (Q := Q) rep width cap basisCap signedCap
  let post := Output (Q := Q) rep width cap basisCap signedCap
  have hw : width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have hpre := sampled_size rep sizes lists width cap basisCap signedCap hh hb hf
  have hwork := work_size rep sizes lists width cap basisCap signedCap hh hu hb hf
  have hmiddle := programInput_size rep sizes lists width cap basisCap signedCap hh hu hb hf
  have hreturned := programOutput_size rep sizes lists width cap basisCap signedCap hh hb hf
  have hpost := output_size rep sizes lists width cap basisCap signedCap hh hb hf
  have hprepare : Bounds control queryCost (.atomic (iface := iface) (prepare rep data cost primitive)) pre work
      (A + 1029 * fee) := by
    apply Bounds.atomic
    intro input hi
    have hout := arithmetic_property rep sizes width cap basisCap signedCap hh hb hf hg input hi
    have hin := hpre input hi
    have hsize := hwork (arithmeticValue input) hout
    have ht := prepare_cost rep data cost primitive sizes laws dataLaws primitiveBound mono input W
      fieldTime scaleTime groupTime (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw)
      (fun f => (hf f).trans hw) (fun g => (hg g).trans hw) hin hz hn hs hd
    have hc := (routing.localCall _ _).trans (mono (show
      Q.size (rep.ty sampledTy) input + Q.size (rep.ty workTy) (arithmeticValue input) ≤ 256 * W by omega))
    exact ⟨hout, (Nat.add_le_add ht hc).trans (by dsimp only [A, fee]; omega)⟩
  have hhistories : Bounds control queryCost (.atomic (iface := iface) (histories rep data cost primitive)) work middle
      (H + 517 * fee) := by
    apply Bounds.atomic
    intro input hi
    have hout := histories_property rep width cap basisCap signedCap input hi
    have hin := hwork input hi
    have hsize := hmiddle (historiesValue input) hout
    have ht := histories_cost rep data cost primitive sizes lists laws dataLaws primitiveBound mono
      width cap basisCap signedCap hh hu hb hf input hi
    have hc := (routing.localCall _ _).trans (mono (show
      Q.size (rep.ty workTy) input + Q.size (rep.ty programInputTy) (historiesValue input) ≤ 256 * W by omega))
    exact ⟨hout, (Nat.add_le_add ht hc).trans (by dsimp only [H, fee, W]; omega)⟩
  have hp := Programming.bound (iface := iface) rep data cost primitive sizes lists laws dataLaws primitiveBound mono
    control queryCost routing (15 * width) cap messageTime pointTime (by omega) (hu.trans (by omega))
    (fun b => (hb b).trans (by omega)) hm he
  have hprogram : Bounds control queryCost (.first (rep.ty savedTy) (Programming.code rep data cost primitive (iface := iface)))
      middle returned (P + fee) := by
    apply Bounds.first control queryCost (rep.ty savedTy) (Programming.code rep data cost primitive)
      (CacheCompiler.Input (Q := Q) rep (15 * width) cap)
      (fun xs => CacheCompiler.Entries (Q := Q) rep (15 * width) xs ∧ xs.length ≤ cap + 1)
      (Saved (Q := Q) rep width (basisCap + 1) (signedCap + 1)) P fee hp
    intro saved hs output ho
    have hs' := saved_size rep sizes lists width (basisCap + 1) (signedCap + 1) hh hb hf saved hs
    have ho' := CacheCompiler.list_size rep sizes lists output (15 * width) (cap + 1) (by omega) ho.1 ho.2
    apply (routing.retain _ _).trans (mono ?_)
    dsimp only [W, frameWidth]
    nlinarith
  have hfinish : Bounds control queryCost (.atomic (iface := iface) (finish rep data cost primitive)) returned post
      (261 * fee) := by
    apply Bounds.atomic
    intro input hi
    have hout := return_property rep width cap basisCap signedCap input hi
    have hin := hreturned input hi
    have hsize := hpost (returnValue input) hout
    have ht := finish_cost rep data cost primitive sizes laws dataLaws primitiveBound mono input W
      (hh.trans hw) (hu.trans hw) hin
    have hc := (routing.localCall _ _).trans (mono (show
      Q.size (rep.ty programOutputTy) input + Q.size (rep.ty outputTy) (returnValue input) ≤ 256 * W by omega))
    exact ⟨hout, (Nat.add_le_add ht hc).trans (by dsimp only [fee]; omega)⟩
  have htail := Bounds.seq control queryCost _ _ middle returned post (P + fee) (261 * fee) fee hprogram hfinish (by
    intro input hi output ho
    have hi' := hmiddle input hi
    have ho' := hreturned output ho
    exact (routing.sequence _ _).trans (mono (by
      dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env] at hi' ho' ⊢
      omega)))
  have hbody := Bounds.seq control queryCost _ _ work middle post (H + 517 * fee)
    (P + fee + 261 * fee + fee) fee hhistories htail (by
      intro input hi output ho
      have hi' := hwork input hi
      have ho' := hmiddle output ho
      exact (routing.sequence _ _).trans (mono (by omega)))
  have hall := Bounds.seq control queryCost _ _ pre work post (A + 1029 * fee)
    (H + 517 * fee + (P + fee + 261 * fee + fee) + fee) fee hprepare hbody (by
      intro input hi output ho
      have hi' := hpre input hi
      have ho' := hwork output ho
      exact (routing.sequence _ _).trans (mono (by omega)))
  intro input hi out hout
  obtain ⟨ho, ht⟩ := hall input hi out hout
  exact ⟨ho, ht.trans (by dsimp only [sampledTime, A, H, P, fee, W]; omega)⟩

theorem bound (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (width cap basisCap signedCap fieldTime scaleTime groupTime messageTime pointTime sampleTime : Nat)
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
      (Input (Q := Q) rep width cap basisCap signedCap)
      (Output (Q := Q) rep width cap basisCap signedCap)
      (signingTime overhead width cap basisCap signedCap fieldTime scaleTime groupTime messageTime pointTime sampleTime) := by
  let W := frameWidth width cap basisCap signedCap
  let fee := overhead (256 * W)
  let pre := Input (Q := Q) rep width cap basisCap signedCap
  let packed := fun input : Unit × inputTy.Value (cryptoBase F G₁ G₂ K M) => pre input.2
  let drawn := fun input : sampledTy.Value (cryptoBase F G₁ G₂ K M) => pre input.2
  let post := Output (Q := Q) rep width cap basisCap signedCap
  let T := sampledTime overhead width cap basisCap signedCap fieldTime scaleTime groupTime messageTime pointTime
  have hw : width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have hpre := input_size rep sizes lists width cap basisCap signedCap hh hb hf
  have hdrawn := sampled_size rep sizes lists width cap basisCap signedCap hh hb hf
  have hpacked (input : Unit × inputTy.Value (cryptoBase F G₁ G₂ K M)) (hi : packed input) :
      Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty inputTy)) input ≤ 3 * W := by
    have hp := sizes.prod_le rep.data.unit (rep.ty inputTy) input
    have hi' := hpre input.2 hi
    have hunit : input.1 = () := Subsingleton.elim _ _
    simp only [hunit] at hp
    omega
  have hpack : Bounds control queryCost (.atomic (iface := iface) (sampleFrame rep data)) pre packed (4 * fee) := by
    apply Bounds.atomic
    intro input hi
    have hin := hpre input hi
    have hout := hpacked ((), input) hi
    have ht := (LocalBound.pair laws (dataLaws.unitBound (rep.ty inputTy))
      (LocalBound.identity laws (rep.ty inputTy))).cost_le input
    have hfee : ∀ n ≤ 256 * W, overhead n ≤ fee := fun _ h => mono h
    have hc := (routing.localCall _ _).trans (hfee _ (show Q.size (rep.ty inputTy) input +
      Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty inputTy)) ((), input) ≤ 256 * W by omega))
    refine ⟨hi, ?_⟩
    dsimp only [LocalBound.pair, DataCostLaws.unitBound, LocalBound.identity, id] at ht
    have h₁ := hfee _ (show Q.size (rep.ty inputTy) input + Q.size rep.data.unit () ≤ 256 * W by omega)
    have h₂ := hfee _ (show Q.size (rep.ty inputTy) input ≤ 256 * W by omega)
    have h₃ := hfee _ (show Q.size (rep.ty inputTy) input +
      Q.size (StepClass.HasProd.prod rep.data.unit (rep.ty inputTy)) ((), input) ≤ 256 * W by omega)
    exact (Nat.add_le_add ht hc).trans (by omega)
  have hpairs := PairSampling.bound rep.data data (rep.ty scalar) (rep.ty scalar) sampler sampler
    sizes laws dataLaws mono control queryCost routing width sampleTime sampleTime hh hu hsample hsample
  have hsampling : Bounds control queryCost
      (.first (rep.ty inputTy) (PairSampling.code rep.data data (rep.ty scalar) (rep.ty scalar) sampler sampler))
      packed drawn (2 * sampleTime + 13 * fee) := by
    intro input hi out hout
    have h := Bounds.first control queryCost (rep.ty inputTy) _ (fun _ => True)
      (fun p => Q.size (rep.ty scalar) p.1 ≤ width ∧ Q.size (rep.ty scalar) p.2 ≤ width) pre
      (sampleTime + sampleTime + 12 * overhead (8 * width)) fee hpairs (by
        intro saved hs output ho
        have hs' := hpre saved hs
        have ho' := sizes.prod_le (rep.ty scalar) (rep.ty scalar) output
        apply (routing.retain _ _).trans (mono ?_)
        omega) input ⟨True.intro, hi⟩ out hout
    have hfee := mono (show 8 * width ≤ 256 * W by omega)
    exact ⟨h.1.2, h.2.trans (by dsimp only [fee]; omega)⟩
  have hcore := sampled_bound (iface := iface) rep data cost primitive sizes lists laws dataLaws primitiveBound mono
    control queryCost routing width cap basisCap signedCap fieldTime scaleTime groupTime messageTime pointTime
    hh hu hb hf hg hz hn hs hd hm he
  have htail := Bounds.seq control queryCost _ _ packed drawn post (2 * sampleTime + 13 * fee) T fee
    hsampling hcore (by
      intro input hi output ho
      have hi' := hpacked input hi
      have ho' := hdrawn output ho
      exact (routing.sequence _ _).trans (mono (by
        dsimp only [LanguageRepresentation.ty, sampledTy] at hi' ho' ⊢
        omega)))
  have hall := Bounds.seq control queryCost _ _ pre packed post (4 * fee)
    (2 * sampleTime + 13 * fee + T + fee) fee hpack htail (by
      intro input hi output ho
      have hi' := hpre input hi
      have ho' := hpacked output ho
      exact (routing.sequence _ _).trans (mono (by omega)))
  intro input hi out hout
  obtain ⟨ho, ht⟩ := hall input hi out hout
  exact ⟨ho, ht.trans (by dsimp only [signingTime, T, fee, W]; omega)⟩

end Signatures.Runtime.SchnorrAGM.Native.Signing
