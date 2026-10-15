import Signatures.Runtime.BackendSchnorrAGMHandlerLocalCost
import Signatures.Runtime.BackendWidthBudget

/-! Composition of proved native-handler budgets with the common-store
adapters. These intermediate rules retain the public configuration, derive the
shared output invariant, and charge both adapters and every control boundary.
The native premises are supplied by the existing primitive-derived dispatch
budgets when installing the complete indexed handler. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.HandlerComponents

open BackendProgram Interface

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes mono routing

private theorem adapt_bound {args raw nativeOut reply : Ty CryptoAtom}
    (inputExpr : Expr CryptoOp [argsStoreTy args] (savedTy raw))
    (outputExpr : Expr CryptoOp [savedTy nativeOut] (resultTy reply))
    (body : Code Q unifSpec iface (rep.ty raw) (rep.ty nativeOut))
    (pre : (argsStoreTy args).Value (cryptoBase F G₁ G₂ K M) → Prop)
    (nativePre : raw.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (nativePost : nativeOut.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (post : (resultTy reply).Value (cryptoBase F G₁ G₂ K M) → Prop)
    (keep : G₁ × G₁ → Prop) (width bodyTime : Nat) (hh : header ≤ width)
    (hinput : ∀ input, pre input → Q.size (rep.ty (argsStoreTy args)) input ≤ width)
    (hnative : ∀ input, nativePre input → Q.size (rep.ty raw) input ≤ width)
    (hout : ∀ output, nativePost output → Q.size (rep.ty nativeOut) output ≤ width)
    (hsaved : ∀ config, keep config → Q.size (rep.ty configTy) config ≤ width)
    (hprepare : ∀ input, pre input →
      let decoded := inputExpr.denote (arithmetic F G₁ G₂ K M cost) (input, ())
      (nativePre decoded.1 ∧ keep decoded.2) ∧
        Q.cost (localCode rep data cost primitive inputExpr) input ≤ 1028 * overhead (8192 * width))
    (hfinish : ∀ output, nativePost output.1 ∧ keep output.2 →
      let result := outputExpr.denote (arithmetic F G₁ G₂ K M cost) (output, ())
      post result ∧ Q.size (rep.ty (resultTy reply)) result ≤ width ∧
        Q.cost (localCode rep data cost primitive outputExpr) output ≤ 1028 * overhead (8192 * width))
    (hbody : Bounds control queryCost body nativePre nativePost bodyTime) :
    Bounds control queryCost
      (.seq (.atomic (localCode rep data cost primitive inputExpr))
        (.seq (.first (rep.ty configTy) body) (.atomic (localCode rep data cost primitive outputExpr))))
      pre post (bodyTime + 2061 * overhead (8192 * width)) := by
  let mid := fun p : (savedTy raw).Value (cryptoBase F G₁ G₂ K M) => nativePre p.1 ∧ keep p.2
  let last := fun p : (savedTy nativeOut).Value (cryptoBase F G₁ G₂ K M) => nativePost p.1 ∧ keep p.2
  have hmid (p) (hp : mid p) : Q.size (rep.ty (savedTy raw)) p ≤ 32 * width := by
    have := hnative p.1 hp.1
    have := hsaved p.2 hp.2
    exact (sizes.prod_le (rep.ty raw) (rep.ty configTy) p).trans (by omega)
  have hlast (p) (hp : last p) : Q.size (rep.ty (savedTy nativeOut)) p ≤ 32 * width := by
    have := hout p.1 hp.1
    have := hsaved p.2 hp.2
    exact (sizes.prod_le (rep.ty nativeOut) (rep.ty configTy) p).trans (by omega)
  have hstart := atomic_bound_of_width (iface := iface) mono control queryCost routing
    (localCode rep data cost primitive inputExpr) pre mid (32 * width) (1028 * overhead (8192 * width))
    (fun input hi => (hinput input hi).trans (by omega)) (by
      intro input hi
      exact ⟨(hprepare input hi).1, hmid _ (hprepare input hi).1, (hprepare input hi).2⟩)
  have hfirst := first_bound_of_width mono control queryCost routing (rep.ty configTy) body
    nativePre nativePost keep (32 * width) bodyTime
    (fun config hc => (hsaved config hc).trans (by omega))
    (fun output ho => (hout output ho).trans (by omega)) hbody
  have hend := atomic_bound_of_width (iface := iface) mono control queryCost routing
    (localCode rep data cost primitive outputExpr) last post (32 * width) (1028 * overhead (8192 * width))
    hlast (by
      intro output ho
      obtain ⟨hp, hw, ht⟩ := hfinish output ho
      exact ⟨hp, hw.trans (by omega), ht⟩)
  have htail := seq_bound_of_width mono control queryCost routing
    (.first (rep.ty configTy) body) (.atomic (localCode rep data cost primitive outputExpr))
    mid last post (32 * width) _ _ hmid hlast hfirst hend
  have hall := seq_bound_of_width mono control queryCost routing
    (.atomic (localCode rep data cost primitive inputExpr))
    (.seq (.first (rep.ty configTy) body) (.atomic (localCode rep data cost primitive outputExpr)))
    pre mid post (32 * width) _ _ (fun input hi => (hinput input hi).trans (by omega)) hmid hstart htail
  intro input hi out ho
  obtain ⟨hp, ht⟩ := hall input hi out ho
  have hfee := mono (show 32 * (32 * width) ≤ 8192 * width by omega)
  exact ⟨hp, by omega⟩

include lists laws dataLaws

theorem signing_bound_of_native (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (width cap basisCap signedCap groupCap rowCap coeffCap bodyTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width) (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hbody : Bounds control queryCost (SigningDispatch.code rep data cost primitive sampler)
      (SigningDispatch.Input (Q := Q) rep width cap basisCap signedCap groupCap rowCap coeffCap)
      (SigningDispatch.Output (Q := Q) rep width cap basisCap signedCap) bodyTime) :
    Bounds control queryCost (signing rep data cost primitive sampler)
      (Input (Q := Q) rep message width cap basisCap signedCap groupCap rowCap coeffCap)
      (Output (Q := Q) rep scalar width (cap + 1) (basisCap + 1) (signedCap + 1))
      (bodyTime + 2061 * overhead (8192 * frameWidth width cap basisCap signedCap groupCap rowCap coeffCap)) := by
  let W := frameWidth width cap basisCap signedCap groupCap rowCap coeffCap
  have hcore : Signing.frameWidth width cap basisCap signedCap ≤ W := by
    dsimp only [W, frameWidth, SigningDispatch.frameWidth]
    omega
  have hw : 3 * width ≤ W := by
    have : 3 * width ≤ Signing.frameWidth width cap basisCap signedCap := by dsimp [Signing.frameWidth]; nlinarith
    exact this.trans hcore
  refine adapt_bound rep data cost primitive sizes mono control queryCost routing
    signingInputExpression (groupOutputExpression scalar) (SigningDispatch.code rep data cost primitive sampler)
    _ _ _ _ (Config (Q := Q) rep width) W bodyTime (by omega)
    (fun input hi => (input_size rep sizes lists message width cap basisCap signedCap groupCap rowCap coeffCap
      hh hu hb hf hg input hi).1) ?_ ?_ ?_ ?_ ?_ hbody
  · intro input hi
    have h := (SigningDispatch.input_size rep sizes lists width cap basisCap signedCap groupCap rowCap coeffCap
      hh hu hb hf hg input hi).1
    exact h.trans (by dsimp only [W, frameWidth]; omega)
  · intro output ho
    exact (SigningDispatch.output_size rep sizes lists width cap basisCap signedCap hh hb hf output ho).trans hcore
  · intro config hc
    exact (config_size rep sizes width hh config hc).trans hw
  · intro input hi
    refine ⟨⟨signing_input rep width cap basisCap signedCap groupCap rowCap coeffCap input hi, hi.2.config⟩, ?_⟩
    have hin := (input_size rep sizes lists message width cap basisCap signedCap groupCap rowCap coeffCap
      hh hu hb hf hg input hi).1
    have h := signingInput_cost rep data cost primitive sizes laws dataLaws mono input W (by omega) (by omega) hin
    exact h.trans (Nat.mul_le_mul_left _ (mono (by omega)))
  · intro output ho
    have hp : Output (Q := Q) rep scalar width (cap + 1) (basisCap + 1) (signedCap + 1)
        (output.1.1, output.2, output.1.2) :=
      ⟨ho.1.scalar, ho.1.groups, ho.1.groupLength, ho.2, ho.1.state⟩
    refine ⟨hp, (output_size rep sizes lists scalar width cap basisCap signedCap hh hb hf _ hp).trans hcore, ?_⟩
    have hn := (SigningDispatch.output_size rep sizes lists width cap basisCap signedCap hh hb hf output.1 ho.1).trans hcore
    have hc := (config_size rep sizes width hh output.2 ho.2).trans hw
    have hin : Q.size (rep.ty (savedTy SigningDispatch.outputTy)) output ≤ 32 * W :=
      (sizes.prod_le (rep.ty SigningDispatch.outputTy) (rep.ty configTy) output).trans (by omega)
    simpa only [← Nat.mul_assoc, Nat.reduceMul] using
      groupOutput_cost rep data cost primitive sizes laws dataLaws mono scalar output (32 * W) (by omega) (by omega) hin

theorem random_bound_of_native (ports : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
    (width cap basisCap signedCap groupCap rowCap coeffCap arityCap bodyTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width) (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hn : ∀ n ≤ arityCap, Q.size rep.data.nat n ≤ width)
    (hbody : Bounds control queryCost (Random.code rep data cost primitive ports)
      (Random.Input (Q := Q) rep width cap basisCap signedCap groupCap rowCap coeffCap arityCap)
      (Random.Output (Q := Q) rep width cap basisCap signedCap arityCap) bodyTime) :
    Bounds control queryCost (random rep data cost primitive ports)
      (fun input => Input (Q := Q) rep .nat width cap basisCap signedCap groupCap rowCap coeffCap input ∧ input.1.1 ≤ arityCap)
      (fun output => Output (Q := Q) rep .nat width cap basisCap signedCap output ∧ output.1.1 ≤ arityCap)
      (bodyTime + 2061 * overhead (8192 * frameWidth width cap basisCap signedCap groupCap rowCap coeffCap)) := by
  let W := frameWidth width cap basisCap signedCap groupCap rowCap coeffCap
  have hcore : Signing.frameWidth width cap basisCap signedCap ≤ W := by
    dsimp only [W, frameWidth, SigningDispatch.frameWidth]
    omega
  have hw : 3 * width ≤ W := by
    have : 3 * width ≤ Signing.frameWidth width cap basisCap signedCap := by dsimp [Signing.frameWidth]; nlinarith
    exact this.trans hcore
  refine adapt_bound rep data cost primitive sizes mono control queryCost routing
    randomInputExpression (groupOutputExpression .nat) (Random.code rep data cost primitive ports)
    _ _ _ _ (Config (Q := Q) rep width) W bodyTime (by omega)
    (fun input hi => (input_size rep sizes lists .nat width cap basisCap signedCap groupCap rowCap coeffCap
      hh hu hb hf hg input hi.1).1) ?_ ?_ ?_ ?_ ?_ hbody
  · intro input hi
    have h := (Random.input_size rep sizes lists width cap basisCap signedCap groupCap rowCap coeffCap arityCap
      hh hu hb hf hg hn input hi).1
    exact h.trans (by dsimp only [W, frameWidth, Random.frameWidth, SigningDispatch.frameWidth]; omega)
  · intro output ho
    exact (Random.output_size rep sizes lists width cap basisCap signedCap arityCap hh hb hf hn output ho).trans hcore
  · intro config hc
    exact (config_size rep sizes width hh config hc).trans hw
  · intro input hi
    refine ⟨⟨random_input rep width cap basisCap signedCap groupCap rowCap coeffCap arityCap input hi.1 hi.2,
      hi.1.2.config⟩, ?_⟩
    have hin := (input_size rep sizes lists .nat width cap basisCap signedCap groupCap rowCap coeffCap
      hh hu hb hf hg input hi.1).1
    have h := randomInput_cost rep data cost primitive sizes laws dataLaws mono input W (by omega) (by omega) hin
    exact h.trans (Nat.mul_le_mul_left _ (mono (by omega)))
  · intro output ho
    have hp : Output (Q := Q) rep .nat width cap basisCap signedCap (output.1.1, output.2, output.1.2) :=
      ⟨hn _ ho.1.value, by intro g hg'; simp only [ho.1.groups, List.not_mem_nil] at hg',
        by simp only [ho.1.groups, List.length_nil]; omega, ho.2, ho.1.state⟩
    have hwide : Output (Q := Q) rep .nat width (cap + 1) (basisCap + 1) (signedCap + 1)
        (output.1.1, output.2, output.1.2) :=
      ⟨hp.data, hp.groups, hp.groupLength, store_mono rep width cap basisCap signedCap
        (cap + 1) (basisCap + 1) (signedCap + 1) (by omega) (by omega) (by omega) _ hp.store⟩
    refine ⟨⟨hp, ho.1.value⟩, (output_size rep sizes lists .nat width cap basisCap signedCap hh hb hf _ hwide).trans hcore, ?_⟩
    have hout := (Random.output_size rep sizes lists width cap basisCap signedCap arityCap hh hb hf hn output.1 ho.1).trans hcore
    have hc := (config_size rep sizes width hh output.2 ho.2).trans hw
    have hin : Q.size (rep.ty (savedTy Random.outputTy)) output ≤ 32 * W :=
      (sizes.prod_le (rep.ty Random.outputTy) (rep.ty configTy) output).trans (by omega)
    simpa only [← Nat.mul_assoc, Nat.reduceMul] using
      groupOutput_cost rep data cost primitive sizes laws dataLaws mono .nat output (32 * W) (by omega) (by omega) hin

theorem hash_bound_of_native (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (width cap basisCap signedCap groupCap rowCap coeffCap bodyTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width) (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hbody : Bounds control queryCost (HashDispatch.code rep data cost primitive sampler)
      (HashDispatch.Input (Q := Q) rep width cap (historyWidth width basisCap signedCap) basisCap groupCap rowCap coeffCap)
      (fun out => Read.Output (Q := Q) rep (3 * width) (cap + 1) (historyWidth width basisCap signedCap) out ∧
        out.2.2.1.length ≤ basisCap) bodyTime) :
    Bounds control queryCost (hash rep data cost primitive sampler)
      (Input (Q := Q) rep message width cap basisCap signedCap groupCap rowCap coeffCap)
      (Output (Q := Q) rep scalar width (cap + 1) basisCap signedCap)
      (bodyTime + 2061 * overhead (8192 * frameWidth width cap basisCap signedCap groupCap rowCap coeffCap)) := by
  let W := frameWidth width cap basisCap signedCap groupCap rowCap coeffCap
  let H := historyWidth width basisCap signedCap
  let nativePre := fun input : HashDispatch.inputTy.Value (cryptoBase F G₁ G₂ K M) =>
    HashDispatch.Input (Q := Q) rep width cap H basisCap groupCap rowCap coeffCap input ∧
      Signing.StateBound (Q := Q) rep width cap basisCap signedCap input.2.2.2
  let nativePost := fun output : Read.outputTy.Value (cryptoBase F G₁ G₂ K M) =>
    Q.size (rep.ty scalar) output.1 ≤ width ∧
      Signing.StateBound (Q := Q) rep width (cap + 1) basisCap signedCap output.2
  have hcore : Signing.frameWidth width cap basisCap signedCap ≤ W := by
    dsimp only [W, frameWidth, SigningDispatch.frameWidth]
    omega
  have hw : 3 * width ≤ W := by
    have : 3 * width ≤ Signing.frameWidth width cap basisCap signedCap := by dsimp [Signing.frameWidth]; nlinarith
    exact this.trans hcore
  have hnative : Bounds control queryCost (HashDispatch.code rep data cost primitive sampler) nativePre nativePost bodyTime := by
    intro input hi out hout
    obtain ⟨ho, ht⟩ := hbody input hi.1 out hout
    obtain ⟨hbasis, hsigned⟩ := HashDispatch.histories_run rep data cost primitive sampler control queryCost input out hout
    refine ⟨⟨hf _, ?_, ho.1.2.2.1, ?_, ?_, ?_⟩, ht⟩
    · simpa only [← Nat.mul_assoc, Nat.reduceMul] using ho.1.2.1
    · rw [hbasis]
      exact hi.2.history.basisLength
    · intro m hm
      rw [hsigned] at hm
      exact hi.2.history.signed m hm
    · rw [hsigned]
      exact hi.2.history.signedLength
  have hnsize (output) (ho : nativePost output) : Q.size (rep.ty Read.outputTy) output ≤ W := by
    have hs := read_state rep sizes lists width (cap + 1) basisCap signedCap hh hb hf output.2 ho.2
    have h := Read.output_size rep sizes lists (3 * width) cap H (by omega)
      (fun b => (hb b).trans (by omega)) output ⟨ho.1.trans (by omega), hs⟩
    exact h.trans (by dsimp only [W, H, frameWidth, HashDispatch.frameWidth]; omega)
  refine adapt_bound rep data cost primitive sizes mono control queryCost routing
    hashInputExpression hashOutputExpression (HashDispatch.code rep data cost primitive sampler)
    _ nativePre nativePost _ (Config (Q := Q) rep width) W bodyTime (by omega)
    (fun input hi => (input_size rep sizes lists message width cap basisCap signedCap groupCap rowCap coeffCap
      hh hu hb hf hg input hi).1) ?_ hnsize ?_ ?_ ?_ hnative
  · intro input hi
    have h := (HashDispatch.input_size rep sizes lists width cap H basisCap groupCap rowCap coeffCap
      hh hu hb hf input hi.1).1
    exact h.trans (by dsimp only [W, H, frameWidth]; omega)
  · intro config hc
    exact (config_size rep sizes width hh config hc).trans hw
  · intro input hi
    refine ⟨⟨⟨hash_input rep sizes lists width cap basisCap signedCap groupCap rowCap coeffCap hh hb hf hg input hi,
      hi.2.state⟩, hi.2.config⟩, ?_⟩
    have hin := (input_size rep sizes lists message width cap basisCap signedCap groupCap rowCap coeffCap
      hh hu hb hf hg input hi).1
    have h := hashInput_cost rep data cost primitive sizes laws dataLaws mono input W (by omega) (by omega) hin
    exact h.trans (Nat.mul_le_mul_left _ (mono (by omega)))
  · intro output ho
    have hp : Output (Q := Q) rep scalar width (cap + 1) basisCap signedCap
        ((output.1.1, []), output.2, output.1.2) :=
      ⟨ho.1.1, by simp, by simp, ho.2, ho.1.2⟩
    have hwide : Output (Q := Q) rep scalar width (cap + 1) (basisCap + 1) (signedCap + 1)
        ((output.1.1, []), output.2, output.1.2) :=
      ⟨hp.data, hp.groups, hp.groupLength, store_mono rep width (cap + 1) basisCap signedCap
        (cap + 1) (basisCap + 1) (signedCap + 1) le_rfl (by omega) (by omega) _ hp.store⟩
    refine ⟨hp, (output_size rep sizes lists scalar width cap basisCap signedCap hh hb hf _ hwide).trans hcore, ?_⟩
    have hn := hnsize output.1 ho.1
    have hc := (config_size rep sizes width hh output.2 ho.2).trans hw
    have hin : Q.size (rep.ty (savedTy Read.outputTy)) output ≤ 32 * W :=
      (sizes.prod_le (rep.ty Read.outputTy) (rep.ty configTy) output).trans (by omega)
    simpa only [← Nat.mul_assoc, Nat.reduceMul] using
      hashOutput_cost rep data cost primitive sizes laws dataLaws mono lists output (32 * W) (by omega) (by omega) hin

end Signatures.Runtime.SchnorrAGM.Native.HandlerComponents
