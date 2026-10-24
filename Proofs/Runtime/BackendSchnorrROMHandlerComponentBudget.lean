import Proofs.Runtime.BackendSchnorrROMHandlerLocalCost
import Proofs.Runtime.BackendSchnorrROMHandlerSize
import Proofs.Runtime.BackendWidthBudget

/-! Compose native ROM kernels with the actual shared-store adapters.
The intermediate kernel premises are supplied by primitive-derived budgets.
Adapter costs, retained state and all control boundaries are derived here. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeComponents

open BackendProgram RawTape

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
  (dataLaws : DataCostLaws rep.data data overhead) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes mono routing

theorem wrap_bound {a b x y : Ty CryptoAtom} (keepTy : Ty CryptoAtom)
    (prepare : Expr CryptoOp [a] (.pair x keepTy)) (finish : Expr CryptoOp [.pair y keepTy] b)
    (body : Code Q unifSpec iface (rep.ty x) (rep.ty y))
    (pre : a.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (nativePre : x.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (nativePost : y.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (post : b.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (keep : keepTy.Value (cryptoBase F G₁ G₂ K M) → Prop)
    (width bodyTime prepareTime finishTime : Nat) (hh : header ≤ width)
    (hinput : ∀ input, pre input → Q.size (rep.ty a) input ≤ width)
    (hnative : ∀ input, nativePre input → Q.size (rep.ty x) input ≤ width)
    (hout : ∀ output, nativePost output → Q.size (rep.ty y) output ≤ width)
    (hsaved : ∀ saved, keep saved → Q.size (rep.ty keepTy) saved ≤ width)
    (hprepare : ∀ input, pre input →
      let decoded := prepare.denote (arithmetic F G₁ G₂ K M cost) (input, ())
      (nativePre decoded.1 ∧ keep decoded.2) ∧ Q.cost (localCode rep data cost primitive prepare) input ≤ prepareTime)
    (hfinish : ∀ output, nativePost output.1 ∧ keep output.2 →
      let result := finish.denote (arithmetic F G₁ G₂ K M cost) (output, ())
      post result ∧ Q.size (rep.ty b) result ≤ width ∧ Q.cost (localCode rep data cost primitive finish) output ≤ finishTime)
    (hbody : Bounds control queryCost body nativePre nativePost bodyTime) :
    Bounds control queryCost (wrap rep data cost primitive keepTy prepare finish body)
      pre post (bodyTime + prepareTime + finishTime + 5 * overhead (1024 * width)) := by
  let mid := fun p : (Ty.pair x keepTy).Value (cryptoBase F G₁ G₂ K M) => nativePre p.1 ∧ keep p.2
  let last := fun p : (Ty.pair y keepTy).Value (cryptoBase F G₁ G₂ K M) => nativePost p.1 ∧ keep p.2
  have hmid (p) (hp : mid p) : Q.size (rep.ty (.pair x keepTy)) p ≤ 32 * width := by
    have := hnative p.1 hp.1
    have := hsaved p.2 hp.2
    exact (sizes.prod_le (rep.ty x) (rep.ty keepTy) p).trans (by omega)
  have hlast (p) (hp : last p) : Q.size (rep.ty (.pair y keepTy)) p ≤ 32 * width := by
    have := hout p.1 hp.1
    have := hsaved p.2 hp.2
    exact (sizes.prod_le (rep.ty y) (rep.ty keepTy) p).trans (by omega)
  have hstart := atomic_bound_of_width (iface := iface) mono control queryCost routing
    (localCode rep data cost primitive prepare) pre mid (32 * width) prepareTime
    (fun input hi => (hinput input hi).trans (by omega)) (by
      intro input hi
      exact ⟨(hprepare input hi).1, hmid _ (hprepare input hi).1, (hprepare input hi).2⟩)
  have hfirst := first_bound_of_width mono control queryCost routing (rep.ty keepTy) body
    nativePre nativePost keep (32 * width) bodyTime
    (fun saved hs => (hsaved saved hs).trans (by omega))
    (fun output ho => (hout output ho).trans (by omega)) hbody
  have hend := atomic_bound_of_width (iface := iface) mono control queryCost routing
    (localCode rep data cost primitive finish) last post (32 * width) finishTime hlast (by
      intro output ho
      obtain ⟨hp, hw, ht⟩ := hfinish output ho
      exact ⟨hp, hw.trans (by omega), ht⟩)
  have htail := seq_bound_of_width mono control queryCost routing
    (.first (rep.ty keepTy) body) (.atomic (localCode rep data cost primitive finish))
    mid last post (32 * width) _ _ hmid hlast hfirst hend
  have hall := seq_bound_of_width mono control queryCost routing
    (.atomic (localCode rep data cost primitive prepare))
    (.seq (.first (rep.ty keepTy) body) (.atomic (localCode rep data cost primitive finish)))
    pre mid post (32 * width) _ _ (fun input hi => (hinput input hi).trans (by omega)) hmid hstart htail
  intro input hi out ho
  obtain ⟨hp, ht⟩ := hall input hi out ho
  exact ⟨hp, by simp only [← Nat.mul_assoc, Nat.reduceMul] at ht; omega⟩

include lists laws dataLaws

theorem hash_bound_of_native
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (width tapeWidth mc lc sc rc nextSavedCap zeroTime bodyTime : Nat)
    (hh : header ≤ width) (ht : header ≤ tapeWidth) (hu : Q.size rep.data.unit () ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width) (hzero : Q.cost (primitive .zero) () ≤ zeroTime)
    (hs : sc ≤ nextSavedCap) (hw : (6 * (nextSavedCap + rc) + 3) * tapeWidth ≤ width)
    (hbody : Bounds control queryCost
      (NativeCache.managed rep data cost primitive (rep.ty NativeUniform.stateTy)
        (NativeDraw.challenge rep data cost primitive sampler))
      (fun p => NativeCache.ManagedInput (Q := Q) rep (3 * width) mc lc p.1 ∧
        NativeUniform.StateBound (Q := Q) rep tapeWidth sc rc p.2)
      (fun p => NativeCache.ManagedOutput (Q := Q) rep (3 * width) (mc + 1) (lc + 1) p.1 ∧
        NativeUniform.StateBound (Q := Q) rep tapeWidth nextSavedCap rc p.2) bodyTime) :
    Bounds control queryCost (hash rep data cost primitive sampler)
      (InputBound (Q := Q) rep hashKey (3 * width) width tapeWidth mc lc sc rc)
      (InputBound (Q := Q) rep scalar (3 * width) width tapeWidth (mc + 1) (lc + 1) nextSavedCap rc)
      (bodyTime + zeroTime + 2061 * overhead (8192 * frameWidth width mc lc)) := by
  let W := frameWidth width mc lc
  let fee := overhead (8192 * W)
  let nativePre := fun p : (taped managedArgsTy).Value (cryptoBase F G₁ G₂ K M) =>
    NativeCache.ManagedInput (Q := Q) rep (3 * width) mc lc p.1 ∧ NativeUniform.StateBound (Q := Q) rep tapeWidth sc rc p.2
  let nativePost := fun p : (taped (.pair scalar (.pair hashCache hashCache))).Value (cryptoBase F G₁ G₂ K M) =>
    NativeCache.ManagedOutput (Q := Q) rep (3 * width) (mc + 1) (lc + 1) p.1 ∧
      NativeUniform.StateBound (Q := Q) rep tapeWidth nextSavedCap rc p.2
  let pre := InputBound (Q := Q) rep hashKey (3 * width) width tapeWidth mc lc sc rc
  let post := InputBound (Q := Q) rep scalar (3 * width) width tapeWidth (mc + 1) (lc + 1) nextSavedCap rc
  have hW : width ≤ W := by dsimp [W, frameWidth]; nlinarith only [Nat.zero_le ((mc + lc) * width)]
  have hw0 : (6 * (sc + rc) + 3) * tapeWidth ≤ width :=
    (Nat.mul_le_mul_right tapeWidth (by omega)).trans hw
  have hin (input) (hi : pre input) : Q.size (rep.ty (withStore hashKey)) input ≤ W := by
    have h := input_size rep sizes lists hashKey (3 * width) width tapeWidth mc lc sc rc hh ht (by omega) hw0 input hi
    dsimp [W, frameWidth]; nlinarith only [h, Nat.zero_le ((mc + lc) * width)]
  have hn (p) (hi : nativePre p) : Q.size (rep.ty (taped managedArgsTy)) p ≤ W := by
    have hm := NativeCache.managed_input_size rep sizes lists (3 * width) mc lc (by omega) (by omega) p.1 hi.1
    have htape := (NativeUniform.state_size rep sizes lists tapeWidth sc rc ht p.2 hi.2).trans hw0
    have hp := sizes.prod_le (rep.ty managedArgsTy) (rep.ty NativeUniform.stateTy) p
    change Q.size (rep.ty managedArgsTy) p.1 ≤ _ at hm
    change Q.size (rep.ty (taped managedArgsTy)) p ≤ _ at hp
    dsimp [W, frameWidth]; nlinarith only [hm, htape, hp, hh, Nat.zero_le ((mc + lc) * width)]
  have hout (p) (ho : nativePost p) : Q.size (rep.ty (taped (.pair scalar (.pair hashCache hashCache)))) p ≤ W := by
    have hm := NativeCache.managed_output_size rep sizes lists (3 * width) (mc + 1) (lc + 1) (by omega) p.1 ho.1
    have htape := (NativeUniform.state_size rep sizes lists tapeWidth nextSavedCap rc ht p.2 ho.2).trans hw
    have hp := sizes.prod_le (rep.ty (.pair scalar (.pair hashCache hashCache))) (rep.ty NativeUniform.stateTy) p
    change Q.size (rep.ty (taped (.pair scalar (.pair hashCache hashCache)))) p ≤ _ at hp
    dsimp [W, frameWidth]; nlinarith only [hm, htape, hp, hh, Nat.zero_le ((mc + lc) * width)]
  have hkeep (config) (hc : ConfigBound (Q := Q) rep width config) : Q.size (rep.ty configTy) config ≤ W := by
    have h := config_size rep sizes width hh config hc
    dsimp [W, frameWidth]; nlinarith only [h, Nat.zero_le ((mc + lc) * width)]
  suffices hall : Bounds control queryCost (hash rep data cost primitive sampler) pre post
      (bodyTime + (zeroTime + 1028 * fee) + 1028 * fee + 5 * overhead (1024 * W)) by
    have hbudget : bodyTime + (zeroTime + 1028 * fee) + 1028 * fee + 5 * overhead (1024 * W) ≤
        bodyTime + zeroTime + 2061 * overhead (8192 * W) := by
      have hf := mono (show 1024 * W ≤ 8192 * W by omega)
      dsimp only [fee]
      omega
    exact Bounds.time_mono control queryCost hall hbudget
  refine wrap_bound rep data cost primitive sizes mono control queryCost routing configTy
    hashInput hashOutput _ pre nativePre nativePost post (ConfigBound (Q := Q) rep width)
    W bodyTime (zeroTime + 1028 * fee) (1028 * fee) (hh.trans hW) hin hn hout hkeep ?_ ?_ hbody
  · intro input hi
    refine ⟨⟨⟨⟨⟨hi.1, hz.trans (by omega), hi.2.caches.managed⟩, hi.2.caches.live⟩, hi.2.tape⟩,
      hi.2.caches.config⟩, ?_⟩
    have h := (hashInput_cost rep data cost primitive sizes laws dataLaws mono input W zeroTime
      (hh.trans hW) (hu.trans hW) (hz.trans hW) hzero (hin input hi)).2
    exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (mono (by omega))) _)
  · intro output ho
    obtain ⟨⟨hc, hm, hmn⟩, hl, hln⟩ := ho.1.1
    have hp : post (output.1.1.1, (output.2, output.1.1.2), output.1.2) :=
      ⟨hc, ⟨⟨ho.2, ⟨hm, hmn⟩, ⟨hl, hln⟩⟩, ho.1.2⟩⟩
    refine ⟨hp, ?_, ?_⟩
    · dsimp only [hashOutput, Expr.denote, Var.get]
      have h := input_size rep sizes lists scalar (3 * width) width tapeWidth (mc + 1) (lc + 1)
        nextSavedCap rc hh ht (by omega) hw _ hp
      dsimp [W, frameWidth]; nlinarith only [h, Nat.zero_le ((mc + lc) * width)]
    · have hi : Q.size (rep.ty (.pair (taped (.pair scalar (.pair hashCache hashCache))) configTy)) output ≤ 32 * W := by
        have hn := hout output.1 ho.1
        have hk := hkeep output.2 ho.2
        exact (sizes.prod_le _ _ output).trans (by omega)
      have h := (hashOutput_cost rep data cost primitive sizes laws dataLaws mono output (32 * W)
        (by omega) (by omega) hi).2
      simpa only [← Nat.mul_assoc, Nat.reduceMul, fee] using h

theorem finalHash_bound_of_native
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (width tapeWidth mc lc sc rc nextSavedCap zeroTime bodyTime : Nat)
    (hh : header ≤ width) (ht : header ≤ tapeWidth) (hu : Q.size rep.data.unit () ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width) (hzero : Q.cost (primitive .zero) () ≤ zeroTime)
    (hs : sc ≤ nextSavedCap) (hw : (6 * (nextSavedCap + rc) + 3) * tapeWidth ≤ width)
    (hbody : Bounds control queryCost
      (NativeCache.live rep data cost primitive (rep.ty NativeUniform.stateTy)
        (NativeDraw.challenge rep data cost primitive sampler))
      (fun p => CacheCompiler.Input (Q := Q) (key := hashKey) (val := scalar) rep (3 * width) lc p.1 ∧
        NativeUniform.StateBound (Q := Q) rep tapeWidth sc rc p.2)
      (fun p => CacheCompiler.Output (Q := Q) (key := hashKey) (val := scalar) rep (3 * width) (lc + 1) p.1 ∧
        NativeUniform.StateBound (Q := Q) rep tapeWidth nextSavedCap rc p.2) bodyTime) :
    Bounds control queryCost (finalHash rep data cost primitive sampler)
      (InputBound (Q := Q) rep hashKey (3 * width) width tapeWidth mc lc sc rc)
      (InputBound (Q := Q) rep scalar (3 * width) width tapeWidth mc (lc + 1) nextSavedCap rc)
      (bodyTime + zeroTime + 2061 * overhead (8192 * frameWidth width mc lc)) := by
  let W := frameWidth width mc lc
  let fee := overhead (8192 * W)
  let nativePre := fun p : (taped liveArgsTy).Value (cryptoBase F G₁ G₂ K M) =>
    CacheCompiler.Input (Q := Q) (key := hashKey) (val := scalar) rep (3 * width) lc p.1 ∧
      NativeUniform.StateBound (Q := Q) rep tapeWidth sc rc p.2
  let nativePost := fun p : (taped (.pair scalar hashCache)).Value (cryptoBase F G₁ G₂ K M) =>
    CacheCompiler.Output (Q := Q) (key := hashKey) (val := scalar) rep (3 * width) (lc + 1) p.1 ∧
      NativeUniform.StateBound (Q := Q) rep tapeWidth nextSavedCap rc p.2
  let pre := InputBound (Q := Q) rep hashKey (3 * width) width tapeWidth mc lc sc rc
  let post := InputBound (Q := Q) rep scalar (3 * width) width tapeWidth mc (lc + 1) nextSavedCap rc
  have hW : width ≤ W := by dsimp [W, frameWidth]; nlinarith only [Nat.zero_le ((mc + lc) * width)]
  have hw0 : (6 * (sc + rc) + 3) * tapeWidth ≤ width :=
    (Nat.mul_le_mul_right tapeWidth (by omega)).trans hw
  have hin (input) (hi : pre input) : Q.size (rep.ty (withStore hashKey)) input ≤ W := by
    have h := input_size rep sizes lists hashKey (3 * width) width tapeWidth mc lc sc rc hh ht (by omega) hw0 input hi
    dsimp [W, frameWidth]; nlinarith only [h, Nat.zero_le ((mc + lc) * width)]
  have hn (p) (hi : nativePre p) : Q.size (rep.ty (taped liveArgsTy)) p ≤ W := by
    have hm := CacheCompiler.input_size (key := hashKey) (val := scalar) rep sizes lists
      (3 * width) lc (by omega) (by omega) p.1 hi.1
    have htape := (NativeUniform.state_size rep sizes lists tapeWidth sc rc ht p.2 hi.2).trans hw0
    have hp := sizes.prod_le (rep.ty liveArgsTy) (rep.ty NativeUniform.stateTy) p
    change Q.size (rep.ty liveArgsTy) p.1 ≤ _ at hm
    change Q.size (rep.ty (taped liveArgsTy)) p ≤ _ at hp
    dsimp [W, frameWidth]; nlinarith only [hm, htape, hp, hh, Nat.zero_le (mc * width), Nat.zero_le (lc * width)]
  have hout (p) (ho : nativePost p) : Q.size (rep.ty (taped (.pair scalar hashCache))) p ≤ W := by
    have hm := CacheCompiler.output_size (key := hashKey) (val := scalar) rep sizes lists
      (3 * width) (lc + 1) (by omega) p.1 ho.1
    have htape := (NativeUniform.state_size rep sizes lists tapeWidth nextSavedCap rc ht p.2 ho.2).trans hw
    have hp := sizes.prod_le (rep.ty (.pair scalar hashCache)) (rep.ty NativeUniform.stateTy) p
    change Q.size (rep.ty (taped (.pair scalar hashCache))) p ≤ _ at hp
    dsimp [W, frameWidth]; nlinarith only [hm, htape, hp, hh, Nat.zero_le (mc * width), Nat.zero_le (lc * width)]
  have hkeep (saved) (hc : KeepBound (Q := Q) rep width mc saved) : Q.size (rep.ty keepCacheTy) saved ≤ W := by
    have h := keep_size rep sizes lists width mc hh saved hc
    dsimp [W, frameWidth]; nlinarith only [h, Nat.zero_le (mc * width), Nat.zero_le (lc * width)]
  suffices hall : Bounds control queryCost (finalHash rep data cost primitive sampler) pre post
      (bodyTime + (zeroTime + 1028 * fee) + 1028 * fee + 5 * overhead (1024 * W)) by
    have hbudget : bodyTime + (zeroTime + 1028 * fee) + 1028 * fee + 5 * overhead (1024 * W) ≤
        bodyTime + zeroTime + 2061 * overhead (8192 * W) := by
      have hf := mono (show 1024 * W ≤ 8192 * W by omega)
      dsimp only [fee]
      omega
    exact Bounds.time_mono control queryCost hall hbudget
  refine wrap_bound rep data cost primitive sizes mono control queryCost routing keepCacheTy
    finalInput finalOutput _ pre nativePre nativePost post (KeepBound (Q := Q) rep width mc)
    W bodyTime (zeroTime + 1028 * fee) (1028 * fee) (hh.trans hW) hin hn hout hkeep ?_ ?_ hbody
  · intro input hi
    refine ⟨⟨⟨⟨hi.1, hz.trans (by omega), hi.2.caches.live⟩, hi.2.tape⟩,
      hi.2.caches.config, hi.2.caches.managed⟩, ?_⟩
    have h := (finalInput_cost rep data cost primitive sizes laws dataLaws mono input W zeroTime
      (hh.trans hW) (hu.trans hW) (hz.trans hW) hzero (hin input hi)).2
    exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (mono (by omega))) _)
  · intro output ho
    obtain ⟨hc, hl, hln⟩ := ho.1.1
    have hp : post (output.1.1.1, (output.2.1, output.2.2, output.1.1.2), output.1.2) :=
      ⟨hc, ⟨⟨ho.2.1, ho.2.2, ⟨hl, hln⟩⟩, ho.1.2⟩⟩
    refine ⟨hp, ?_, ?_⟩
    · dsimp only [finalOutput, Expr.denote, Var.get]
      have h := input_size rep sizes lists scalar (3 * width) width tapeWidth mc (lc + 1)
        nextSavedCap rc hh ht (by omega) hw _ hp
      dsimp [W, frameWidth]; nlinarith only [h, Nat.zero_le (mc * width), Nat.zero_le (lc * width)]
    · have hi : Q.size (rep.ty (.pair (taped (.pair scalar hashCache)) keepCacheTy)) output ≤ 32 * W := by
        have hn := hout output.1 ho.1
        have hk := hkeep output.2 ho.2
        exact (sizes.prod_le _ _ output).trans (by omega)
      have h := (finalOutput_cost rep data cost primitive sizes laws dataLaws mono output (32 * W)
        (by omega) (by omega) hi).2
      simpa only [← Nat.mul_assoc, Nat.reduceMul, fee] using h

/-- The common-store adapters depend only on the signer's input/output encoding
and proved core budget. Both nonce conventions use these same executed adapters. -/
theorem signing_wrap_bound
    (core : Code Q unifSpec iface (rep.ty (taped signingArgsTy))
      (rep.ty (taped (.pair signatureTy hashCache))))
    (width tapeWidth mc lc sc rc nextSavedCap bodyTime : Nat)
    (hh : header ≤ width) (ht : header ≤ tapeWidth) (hu : Q.size rep.data.unit () ≤ width)
    (hs : sc ≤ nextSavedCap) (hw : (6 * (nextSavedCap + rc) + 3) * tapeWidth ≤ width)
    (hbody : Bounds control queryCost
      core
      (fun p => NativeCache.SigningInput (Q := Q) rep width mc p.1 ∧
        NativeUniform.StateBound (Q := Q) rep tapeWidth sc rc p.2)
      (fun p => NativeCache.SigningOutput (Q := Q) rep width (mc + 1) p.1 ∧
        NativeUniform.StateBound (Q := Q) rep tapeWidth nextSavedCap rc p.2) bodyTime) :
    Bounds control queryCost (wrap rep data cost primitive keepCacheTy signingInput signingOutput core)
      (InputBound (Q := Q) rep message width width tapeWidth mc lc sc rc)
      (InputBound (Q := Q) rep signatureTy (3 * width) width tapeWidth (mc + 1) lc nextSavedCap rc)
      (bodyTime + 2061 * overhead (8192 * frameWidth width mc lc)) := by
  let W := frameWidth width mc lc
  let fee := overhead (8192 * W)
  let nativePre := fun p : (taped signingArgsTy).Value (cryptoBase F G₁ G₂ K M) =>
    NativeCache.SigningInput (Q := Q) rep width mc p.1 ∧ NativeUniform.StateBound (Q := Q) rep tapeWidth sc rc p.2
  let nativePost := fun p : (taped (.pair signatureTy hashCache)).Value (cryptoBase F G₁ G₂ K M) =>
    NativeCache.SigningOutput (Q := Q) rep width (mc + 1) p.1 ∧
      NativeUniform.StateBound (Q := Q) rep tapeWidth nextSavedCap rc p.2
  let pre := InputBound (Q := Q) rep message width width tapeWidth mc lc sc rc
  let post := InputBound (Q := Q) rep signatureTy (3 * width) width tapeWidth (mc + 1) lc nextSavedCap rc
  have hW : width ≤ W := by dsimp [W, frameWidth]; nlinarith only [Nat.zero_le ((mc + lc) * width)]
  have hw0 : (6 * (sc + rc) + 3) * tapeWidth ≤ width :=
    (Nat.mul_le_mul_right tapeWidth (by omega)).trans hw
  have hin (input) (hi : pre input) : Q.size (rep.ty (withStore message)) input ≤ W := by
    have h := input_size rep sizes lists message width width tapeWidth mc lc sc rc hh ht (by omega) hw0 input hi
    dsimp [W, frameWidth]; nlinarith only [h, Nat.zero_le ((mc + lc) * width)]
  have hn (p) (hi : nativePre p) : Q.size (rep.ty (taped signingArgsTy)) p ≤ W := by
    have hm := NativeCache.signing_input_size rep sizes lists width mc hh hu p.1 hi.1
    have htape := (NativeUniform.state_size rep sizes lists tapeWidth sc rc ht p.2 hi.2).trans hw0
    have hp := sizes.prod_le (rep.ty signingArgsTy) (rep.ty NativeUniform.stateTy) p
    change Q.size (rep.ty signingArgsTy) p.1 ≤ _ at hm
    change Q.size (rep.ty (taped signingArgsTy)) p ≤ _ at hp
    dsimp [W, frameWidth]; nlinarith only [hm, htape, hp, hh, Nat.zero_le (mc * width), Nat.zero_le (lc * width)]
  have hout (p) (ho : nativePost p) : Q.size (rep.ty (taped (.pair signatureTy hashCache))) p ≤ W := by
    have hm := NativeCache.signing_output_size rep sizes lists width (mc + 1) hh p.1 ho.1
    have htape := (NativeUniform.state_size rep sizes lists tapeWidth nextSavedCap rc ht p.2 ho.2).trans hw
    have hp := sizes.prod_le (rep.ty (.pair signatureTy hashCache)) (rep.ty NativeUniform.stateTy) p
    change Q.size (rep.ty (taped (.pair signatureTy hashCache))) p ≤ _ at hp
    dsimp [W, frameWidth]; nlinarith only [hm, htape, hp, hh, Nat.zero_le (mc * width), Nat.zero_le (lc * width)]
  have hkeep (saved) (hc : KeepBound (Q := Q) rep width lc saved) : Q.size (rep.ty keepCacheTy) saved ≤ W := by
    have h := keep_size rep sizes lists width lc hh saved hc
    dsimp [W, frameWidth]; nlinarith only [h, Nat.zero_le (mc * width), Nat.zero_le (lc * width)]
  suffices hall : Bounds control queryCost (wrap rep data cost primitive keepCacheTy signingInput signingOutput core) pre post
      (bodyTime + 1028 * fee + 1028 * fee + 5 * overhead (1024 * W)) by
    have hbudget : bodyTime + 1028 * fee + 1028 * fee + 5 * overhead (1024 * W) ≤
        bodyTime + 2061 * overhead (8192 * W) := by
      have hf := mono (show 1024 * W ≤ 8192 * W by omega)
      dsimp only [fee]
      omega
    exact Bounds.time_mono control queryCost hall hbudget
  refine wrap_bound rep data cost primitive sizes mono control queryCost routing keepCacheTy
    signingInput signingOutput _ pre nativePre nativePost post (KeepBound (Q := Q) rep width lc)
    W bodyTime (1028 * fee) (1028 * fee) (hh.trans hW) hin hn hout hkeep ?_ ?_ hbody
  · intro input hi
    refine ⟨⟨⟨⟨hi.1, hi.2.caches.config.1, hi.2.caches.config.2, hi.2.caches.managed⟩, hi.2.tape⟩,
      hi.2.caches.config, hi.2.caches.live⟩, ?_⟩
    have h := (signingInput_cost rep data cost primitive sizes laws dataLaws mono input W
      (hh.trans hW) (hu.trans hW) (hin input hi)).2
    exact h.trans (Nat.mul_le_mul_left _ (mono (by omega)))
  · intro output ho
    obtain ⟨hr, hz, hm, hmn⟩ := ho.1.1
    have hv : Q.size (rep.ty signatureTy) output.1.1.1 ≤ 3 * width :=
      (sizes.prod_le (rep.ty point₁) (rep.ty scalar) _).trans (by omega)
    have hp : post (output.1.1.1, (output.2.1, output.1.1.2, output.2.2), output.1.2) :=
      ⟨hv, ⟨⟨ho.2.1, ⟨hm, hmn⟩, ho.2.2⟩, ho.1.2⟩⟩
    refine ⟨hp, ?_, ?_⟩
    · dsimp only [signingOutput, Expr.denote, Var.get]
      have h := input_size rep sizes lists signatureTy (3 * width) width tapeWidth (mc + 1) lc
        nextSavedCap rc hh ht (by omega) hw _ hp
      dsimp [W, frameWidth]; nlinarith only [h, Nat.zero_le (mc * width), Nat.zero_le (lc * width)]
    · have hi : Q.size (rep.ty (.pair (taped (.pair signatureTy hashCache)) keepCacheTy)) output ≤ 32 * W := by
        have hn := hout output.1 ho.1
        have hk := hkeep output.2 ho.2
        exact (sizes.prod_le _ _ output).trans (by omega)
      have h := (signingOutput_cost rep data cost primitive sizes laws dataLaws mono output (32 * W)
        (by omega) (by omega) hi).2
      simpa only [← Nat.mul_assoc, Nat.reduceMul, fee] using h

theorem signing_bound_of_native [Q.IsDistributive]
    (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
    (ports : NativePrivate.Ports (Q := Q) rep (iface := iface))
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (width tapeWidth mc lc sc rc nextSavedCap bodyTime : Nat)
    (hh : header ≤ width) (ht : header ≤ tapeWidth) (hu : Q.size rep.data.unit () ≤ width)
    (hs : sc ≤ nextSavedCap) (hw : (6 * (nextSavedCap + rc) + 3) * tapeWidth ≤ width)
    (hbody : Bounds control queryCost
      (NativeCache.signing rep data cost primitive (rep.ty NativeUniform.stateTy)
        (NativePrivate.code rep data cost primitive uniform ports sampler))
      (fun p => NativeCache.SigningInput (Q := Q) rep width mc p.1 ∧
        NativeUniform.StateBound (Q := Q) rep tapeWidth sc rc p.2)
      (fun p => NativeCache.SigningOutput (Q := Q) rep width (mc + 1) p.1 ∧
        NativeUniform.StateBound (Q := Q) rep tapeWidth nextSavedCap rc p.2) bodyTime) :
    Bounds control queryCost (signing rep data cost primitive uniform ports sampler)
      (InputBound (Q := Q) rep message width width tapeWidth mc lc sc rc)
      (InputBound (Q := Q) rep signatureTy (3 * width) width tapeWidth (mc + 1) lc nextSavedCap rc)
      (bodyTime + 2061 * overhead (8192 * frameWidth width mc lc)) := by
  exact signing_wrap_bound rep data cost primitive sizes lists laws dataLaws mono control queryCost routing
    _ width tapeWidth mc lc sc rc nextSavedCap bodyTime hh ht hu hs hw hbody

theorem random_bound_of_native
    (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
    (width tapeWidth mc lc sc rc nextSavedCap arityCap bodyTime : Nat)
    (hh : header ≤ width) (ht : header ≤ tapeWidth) (hu : Q.size rep.data.unit () ≤ width)
    (hs : sc ≤ nextSavedCap) (hw : (6 * (nextSavedCap + rc) + 3) * tapeWidth ≤ width)
    (hNat : ∀ n ≤ arityCap, Q.size rep.data.nat n ≤ tapeWidth)
    (hbody : Bounds control queryCost (NativeUniform.code rep data cost primitive uniform)
      (fun p => p.1 ≤ arityCap ∧ NativeUniform.StateBound (Q := Q) rep tapeWidth sc rc p.2)
      (NativeUniform.InputBound (Q := Q) rep tapeWidth nextSavedCap rc) bodyTime) :
    Bounds control queryCost (random rep data cost primitive uniform)
      (fun p => p.1 ≤ arityCap ∧ StoreBound (Q := Q) rep width tapeWidth mc lc sc rc p.2)
      (InputBound (Q := Q) rep .nat tapeWidth width tapeWidth mc lc nextSavedCap rc)
      (bodyTime + 2061 * overhead (8192 * frameWidth width mc lc)) := by
  let W := frameWidth width mc lc
  let fee := overhead (8192 * W)
  let nativePre := fun p : (taped .nat).Value (cryptoBase F G₁ G₂ K M) =>
    p.1 ≤ arityCap ∧ NativeUniform.StateBound (Q := Q) rep tapeWidth sc rc p.2
  let nativePost := NativeUniform.InputBound (Q := Q) rep tapeWidth nextSavedCap rc
  let pre := fun p : (withStore .nat).Value (cryptoBase F G₁ G₂ K M) =>
    p.1 ≤ arityCap ∧ StoreBound (Q := Q) rep width tapeWidth mc lc sc rc p.2
  let post := InputBound (Q := Q) rep .nat tapeWidth width tapeWidth mc lc nextSavedCap rc
  have hW : width ≤ W := by dsimp [W, frameWidth]; nlinarith only [Nat.zero_le ((mc + lc) * width)]
  have htw : tapeWidth ≤ width := by nlinarith only [hw, Nat.zero_le ((nextSavedCap + rc) * tapeWidth)]
  have hw0 : (6 * (sc + rc) + 3) * tapeWidth ≤ width :=
    (Nat.mul_le_mul_right tapeWidth (by omega)).trans hw
  have hin (input) (hi : pre input) : Q.size (rep.ty (withStore .nat)) input ≤ W := by
    have h := input_size rep sizes lists .nat tapeWidth width tapeWidth mc lc sc rc hh ht (by omega) hw0
      input ⟨hNat _ hi.1, hi.2⟩
    dsimp [W, frameWidth]; nlinarith only [h, Nat.zero_le ((mc + lc) * width)]
  have hn (p) (hi : nativePre p) : Q.size (rep.ty (taped .nat)) p ≤ W := by
    have htape := (NativeUniform.state_size rep sizes lists tapeWidth sc rc ht p.2 hi.2).trans hw0
    have ha := (hNat _ hi.1).trans htw
    have hp := sizes.prod_le rep.data.nat (rep.ty NativeUniform.stateTy) p
    change Q.size (rep.ty (taped .nat)) p ≤ _ at hp
    dsimp [W, frameWidth]; nlinarith only [ha, htape, hp, hh, Nat.zero_le ((mc + lc) * width)]
  have hout (p) (ho : nativePost p) : Q.size (rep.ty (taped .nat)) p ≤ W := by
    have htape := (NativeUniform.state_size rep sizes lists tapeWidth nextSavedCap rc ht p.2 ho.2).trans hw
    have ha := ho.1.trans htw
    have hp := sizes.prod_le rep.data.nat (rep.ty NativeUniform.stateTy) p
    change Q.size (rep.ty (taped .nat)) p ≤ _ at hp
    dsimp [W, frameWidth]; nlinarith only [ha, htape, hp, hh, Nat.zero_le ((mc + lc) * width)]
  have hkeep (saved) (hc : CachesBound (Q := Q) rep width mc lc saved) : Q.size (rep.ty cacheStore) saved ≤ W := by
    have h := caches_size rep sizes lists width mc lc hh saved hc
    dsimp [W, frameWidth]; nlinarith only [h, Nat.zero_le ((mc + lc) * width)]
  suffices hall : Bounds control queryCost (random rep data cost primitive uniform) pre post
      (bodyTime + 1028 * fee + 1028 * fee + 5 * overhead (1024 * W)) by
    have hbudget : bodyTime + 1028 * fee + 1028 * fee + 5 * overhead (1024 * W) ≤
        bodyTime + 2061 * overhead (8192 * W) := by
      have hf := mono (show 1024 * W ≤ 8192 * W by omega)
      dsimp only [fee]
      omega
    exact Bounds.time_mono control queryCost hall hbudget
  refine wrap_bound rep data cost primitive sizes mono control queryCost routing cacheStore
    randomInput randomOutput _ pre nativePre nativePost post (CachesBound (Q := Q) rep width mc lc)
    W bodyTime (1028 * fee) (1028 * fee) (hh.trans hW) hin hn hout hkeep ?_ ?_ hbody
  · intro input hi
    refine ⟨⟨⟨hi.1, hi.2.tape⟩, hi.2.caches⟩, ?_⟩
    have h := (randomInput_cost rep data cost primitive sizes laws dataLaws mono input W
      (hh.trans hW) (hu.trans hW) (hin input hi)).2
    exact h.trans (Nat.mul_le_mul_left _ (mono (by omega)))
  · intro output ho
    have hp : post (output.1.1, output.2, output.1.2) := ⟨ho.1.1, ⟨ho.2, ho.1.2⟩⟩
    refine ⟨hp, ?_, ?_⟩
    · dsimp only [randomOutput, Expr.denote, Var.get]
      have h := input_size rep sizes lists .nat tapeWidth width tapeWidth mc lc nextSavedCap rc
        hh ht (by omega) hw _ hp
      dsimp [W, frameWidth]; nlinarith only [h, Nat.zero_le ((mc + lc) * width)]
    · have hi : Q.size (rep.ty (.pair (taped .nat) cacheStore)) output ≤ 32 * W := by
        have hn := hout output.1 ho.1
        have hk := hkeep output.2 ho.2
        exact (sizes.prod_le _ _ output).trans (by omega)
      have h := (randomOutput_cost rep data cost primitive sizes laws dataLaws mono output (32 * W)
        (by omega) (by omega) hi).2
      simpa only [← Nat.mul_assoc, Nat.reduceMul, fee] using h

end Signatures.Runtime.Schnorr.ListROM.NativeComponents
