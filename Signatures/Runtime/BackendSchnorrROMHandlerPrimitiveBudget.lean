import Signatures.Runtime.BackendSchnorrROMHandlerComponentBudget
import Signatures.Runtime.BackendSchnorrROMPrivateBudget
import Signatures.Runtime.BackendSchnorrRawUniformPolynomial

/-! Complete shared-store cache/signing budgets from original sampler resources
and primitive contracts. No finished adapter, kernel or sampler budget is assumed.
The same actual programs already have exact source correspondence. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeComponents

open BackendProgram RawTape

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (ports : NativePrivate.Ports (Q := Q) rep (iface := iface))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes lists laws mono routing

theorem cache_components_bound
    (dataLaws : DataCostLaws rep.data data overhead)
    (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
    (distribution : ∀ {A B T : Type} (a : C.Str A) (b : C.Str B) (t : C.Str T) (p : (A ⊕ B) × T),
      Q.cost (QD.distribute a b t) p ≤ overhead
        (Q.size (StepClass.HasProd.prod (StepClass.HasSum.sum a b) t) p +
          Q.size (StepClass.HasSum.sum (StepClass.HasProd.prod a t) (StepClass.HasProd.prod b t))
            (StateSimulation.distributeValue p)))
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (work visits queries sourceWidth tapeWidth savedCap remainingCap counter arityCap tickTime
      comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
      width managedCap liveCap messageTime pointTime scaleTime subTime : Nat)
    (hsource : ExecutionProfile.Within sampler () work visits queries sourceWidth counter (fun n => n ≤ arityCap))
    (tick : ∀ n ≤ counter, ∀ size ≤ 6 * NativePrivate.samplerWidth sourceWidth tapeWidth
      (savedCap + queries) remainingCap queries, control.loop n size ≤ tickTime)
    (hh : header ≤ tapeWidth) (hu : Q.size rep.data.unit () ≤ tapeWidth)
    (hb : ∀ b, Q.size rep.data.bool b ≤ tapeWidth) (hz : Q.size (rep.ty scalar) (0 : F) ≤ tapeWidth)
    (hn : ∀ n ≤ arityCap + 2, Q.size rep.data.nat n ≤ tapeWidth)
    (hcompare : ∀ a b, Q.size rep.data.nat a ≤ tapeWidth → Q.size rep.data.nat b ≤ tapeWidth →
      (primitiveBound .natEq).time (a, b) ≤ comparisonTime)
    (hzero : (primitiveBound .zero).time () ≤ zeroTime)
    (hadd : ∀ n ≤ arityCap, (primitiveBound .natAdd).time (n, 2) ≤ addTime)
    (hp : ∀ n ≤ arityCap, Q.size iface.position n ≤ tapeWidth)
    (hr : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.size iface.response ⟨n, r⟩ ≤ tapeWidth)
    (hrequest : ∀ n ≤ arityCap, Q.cost uniform.request n ≤ requestTime)
    (hresponse : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.cost uniform.response ⟨n, r⟩ ≤ responseTime)
    (hquery : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), queryCost n r +
      control.query (Q.size iface.position n) (Q.size iface.response ⟨n, r⟩) ≤ queryTime)
    (hread : ∀ n ≤ arityCap, Q.cost ports.arity n ≤ arityTime)
    (hreply : ∀ n ≤ arityCap, ∀ r, Q.size rep.data.nat r ≤ tapeWidth → Q.cost ports.reply (r, n) ≤ replyTime)
    (hsourceTapeWidth : sourceWidth ≤ tapeWidth)
    (hstoreWidth : (6 * (savedCap + 2 * queries + 1 + remainingCap) + 3) * tapeWidth ≤ width)
    (hm : ∀ x y : M, Q.size (rep.ty message) x ≤ 3 * width → Q.size (rep.ty message) y ≤ 3 * width →
      (primitiveBound .messageEq).time (x, y) ≤ messageTime)
    (hg : ∀ x y : G₁, Q.size (rep.ty point₁) x ≤ 3 * width → Q.size (rep.ty point₁) y ≤ 3 * width →
      (primitiveBound .point₁Eq).time (x, y) ≤ pointTime)
    (hscale : ∀ z : F, ∀ g : G₁, Q.size (rep.ty scalar) z ≤ width → Q.size (rep.ty point₁) g ≤ width →
      Q.size (rep.ty point₁) (z • g) ≤ width ∧ (primitiveBound .scale₁).time (z, g) ≤ scaleTime)
    (hsub : ∀ g pk : G₁, Q.size (rep.ty point₁) g ≤ width → Q.size (rep.ty point₁) pk ≤ width →
      Q.size (rep.ty point₁) (g - pk) ≤ width ∧ (primitiveBound .sub₁).time (g, pk) ≤ subTime) :
    let firstTime := NativePrivate.samplerTime overhead work visits queries sourceWidth tapeWidth
      savedCap remainingCap tickTime comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
    let secondTime := NativePrivate.samplerTime overhead work visits queries sourceWidth tapeWidth
      (savedCap + queries) remainingCap tickTime comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
    let hashTime := NativeDraw.challengeTime overhead tapeWidth savedCap remainingCap comparisonTime zeroTime
      (ExecutionProfile.runtimeBound overhead tapeWidth work visits queries tickTime queryTime)
    let adapterTime := 2061 * overhead (8192 * frameWidth width managedCap liveCap)
    Bounds control queryCost (finalHash rep data cost primitive sampler)
      (InputBound (Q := Q) rep hashKey (3 * width) width tapeWidth managedCap liveCap savedCap remainingCap)
      (InputBound (Q := Q) rep scalar (3 * width) width tapeWidth managedCap (liveCap + 1) (savedCap + 1) remainingCap)
      (NativeCache.liveTime overhead (3 * width) liveCap messageTime pointTime hashTime + zeroTime + adapterTime) ∧
    Bounds control queryCost (hash rep data cost primitive sampler)
      (InputBound (Q := Q) rep hashKey (3 * width) width tapeWidth managedCap liveCap savedCap remainingCap)
      (InputBound (Q := Q) rep scalar (3 * width) width tapeWidth (managedCap + 1) (liveCap + 1) (savedCap + 1) remainingCap)
      (NativeCache.managedTime overhead (3 * width) managedCap liveCap messageTime pointTime hashTime + zeroTime + adapterTime) ∧
    Bounds control queryCost (signing rep data cost primitive uniform ports sampler)
      (InputBound (Q := Q) rep message width width tapeWidth managedCap liveCap savedCap remainingCap)
      (InputBound (Q := Q) rep signatureTy (3 * width) width tapeWidth (managedCap + 1) liveCap
        (savedCap + 2 * queries) remainingCap)
      (NativeCache.signingTime overhead width managedCap messageTime pointTime scaleTime subTime firstTime secondTime + adapterTime) := by
  dsimp only
  obtain ⟨hl, hm, hs⟩ := NativeCache.kernels_bound rep data cost primitive uniform ports sizes lists laws mono
    control queryCost routing dataLaws primitiveBound distribution sampler
    work visits queries sourceWidth tapeWidth savedCap remainingCap counter arityCap tickTime
    comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
    width managedCap liveCap messageTime pointTime scaleTime subTime
    hsource tick hh hu hb hz hn hcompare hzero hadd hp hr hrequest hresponse hquery hread hreply
    hsourceTapeWidth hstoreWidth hm hg hscale hsub
  have htw : tapeWidth ≤ width := by
    nlinarith only [hstoreWidth, Nat.zero_le ((savedCap + 2 * queries + 1 + remainingCap) * tapeWidth)]
  have hhash : (6 * (savedCap + 1 + remainingCap) + 3) * tapeWidth ≤ width :=
    (Nat.mul_le_mul_right tapeWidth (by omega)).trans hstoreWidth
  have hsign : (6 * (savedCap + 2 * queries + remainingCap) + 3) * tapeWidth ≤ width :=
    (Nat.mul_le_mul_right tapeWidth (by omega)).trans hstoreWidth
  have hzeroActual := ((primitiveBound .zero).cost_le ()).trans hzero
  refine ⟨?_, ?_, ?_⟩
  · exact finalHash_bound_of_native rep data cost primitive sizes lists laws dataLaws mono control queryCost routing
      sampler width tapeWidth managedCap liveCap savedCap remainingCap (savedCap + 1) zeroTime _
      (hh.trans htw) hh (hu.trans htw) (hz.trans htw) hzeroActual (by omega) hhash hl
  · exact hash_bound_of_native rep data cost primitive sizes lists laws dataLaws mono control queryCost routing
      sampler width tapeWidth managedCap liveCap savedCap remainingCap (savedCap + 1) zeroTime _
      (hh.trans htw) hh (hu.trans htw) (hz.trans htw) hzeroActual (by omega) hhash hm
  · exact signing_bound_of_native rep data cost primitive sizes lists laws dataLaws mono control queryCost routing
      uniform ports sampler width tapeWidth managedCap liveCap savedCap remainingCap (savedCap + 2 * queries) _
      (hh.trans htw) hh (hu.trans htw) (by omega) hsign hs

omit QD [SampleableType F] in
theorem random_bound
    (dataLaws : DataCostLaws rep.data data overhead)
    (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
    (width managedCap liveCap : Nat)
    (tapeWidth savedCap remainingCap arityCap comparisonTime zeroTime addTime
    requestTime responseTime queryTime : Nat)
    (hh : header ≤ tapeWidth) (hu : Q.size rep.data.unit () ≤ tapeWidth)
    (hb : ∀ b, Q.size rep.data.bool b ≤ tapeWidth)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ tapeWidth)
    (hn : ∀ n ≤ arityCap + 2, Q.size rep.data.nat n ≤ tapeWidth)
    (hcompare : ∀ a b, Q.size rep.data.nat a ≤ tapeWidth → Q.size rep.data.nat b ≤ tapeWidth →
      (primitiveBound .natEq).time (a, b) ≤ comparisonTime)
    (hzero : (primitiveBound .zero).time () ≤ zeroTime)
    (hadd : ∀ n ≤ arityCap, (primitiveBound .natAdd).time (n, 2) ≤ addTime)
    (hp : ∀ n ≤ arityCap, Q.size iface.position n ≤ tapeWidth)
    (hr : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.size iface.response ⟨n, r⟩ ≤ tapeWidth)
    (hrequest : ∀ n ≤ arityCap, Q.cost uniform.request n ≤ requestTime)
    (hresponse : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.cost uniform.response ⟨n, r⟩ ≤ responseTime)
    (hquery : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), queryCost n r +
      control.query (Q.size iface.position n) (Q.size iface.response ⟨n, r⟩) ≤ queryTime)
    (hstoreWidth : (6 * (savedCap + 1 + remainingCap) + 3) * tapeWidth ≤ width) :
    Bounds control queryCost (random rep data cost primitive uniform)
      (fun p => p.1 ≤ arityCap ∧ StoreBound (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap p.2)
      (InputBound (Q := Q) rep .nat tapeWidth width tapeWidth managedCap liveCap (savedCap + 1) remainingCap)
      (NativeUniform.runtimeBound overhead tapeWidth savedCap remainingCap comparisonTime zeroTime addTime
        requestTime responseTime queryTime + 2061 * overhead (8192 * frameWidth width managedCap liveCap)) := by
  have htw : tapeWidth ≤ width := by
    nlinarith only [hstoreWidth, Nat.zero_le ((savedCap + 1 + remainingCap) * tapeWidth)]
  apply random_bound_of_native rep data cost primitive sizes lists laws dataLaws mono control queryCost routing
    uniform width tapeWidth managedCap liveCap savedCap remainingCap (savedCap + 1) arityCap _
    (hh.trans htw) hh (hu.trans htw) (by omega) hstoreWidth (fun n hn' => hn n (by omega))
  exact NativeUniform.bound rep data cost primitive uniform sizes lists laws dataLaws primitiveBound mono
    control queryCost routing tapeWidth savedCap remainingCap arityCap comparisonTime zeroTime addTime
    requestTime responseTime queryTime hh hu hb hz hn hcompare hzero hadd hp hr hrequest hresponse hquery

omit sizes lists laws mono routing in
theorem adapterTime_polynomial (overhead : Nat → Nat → Nat) (width managedCap liveCap : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hManaged : PolynomiallyBounded managedCap) (hLive : PolynomiallyBounded liveCap) :
    PolynomiallyBounded (fun n => 2061 * overhead n (8192 * frameWidth (width n) (managedCap n) (liveCap n))) := by
  unfold frameWidth
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

omit sizes lists laws mono routing in
theorem cache_components_polynomial (overhead : Nat → Nat → Nat)
    (work visits queries sourceWidth tapeWidth savedCap remainingCap tickTime comparisonTime zeroTime addTime
      requestTime responseTime queryTime arityTime replyTime width managedCap liveCap messageTime pointTime
      scaleTime subTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead)
    (hWork : PolynomiallyBounded work) (hVisits : PolynomiallyBounded visits)
    (hQueries : PolynomiallyBounded queries) (hSourceWidth : PolynomiallyBounded sourceWidth)
    (hTapeWidth : PolynomiallyBounded tapeWidth) (hSaved : PolynomiallyBounded savedCap)
    (hRemaining : PolynomiallyBounded remainingCap) (hTick : PolynomiallyBounded tickTime)
    (hCompare : PolynomiallyBounded comparisonTime) (hZero : PolynomiallyBounded zeroTime)
    (hAdd : PolynomiallyBounded addTime) (hRequest : PolynomiallyBounded requestTime)
    (hResponse : PolynomiallyBounded responseTime) (hQuery : PolynomiallyBounded queryTime)
    (hArity : PolynomiallyBounded arityTime) (hReply : PolynomiallyBounded replyTime)
    (hWidth : PolynomiallyBounded width) (hManaged : PolynomiallyBounded managedCap)
    (hLive : PolynomiallyBounded liveCap) (hMessage : PolynomiallyBounded messageTime)
    (hPoint : PolynomiallyBounded pointTime) (hScale : PolynomiallyBounded scaleTime)
    (hSub : PolynomiallyBounded subTime) :
    let firstTime := fun n => NativePrivate.samplerTime (overhead n) (work n) (visits n) (queries n)
      (sourceWidth n) (tapeWidth n) (savedCap n) (remainingCap n) (tickTime n) (comparisonTime n)
      (zeroTime n) (addTime n) (requestTime n) (responseTime n) (queryTime n) (arityTime n) (replyTime n)
    let secondTime := fun n => NativePrivate.samplerTime (overhead n) (work n) (visits n) (queries n)
      (sourceWidth n) (tapeWidth n) (savedCap n + queries n) (remainingCap n) (tickTime n) (comparisonTime n)
      (zeroTime n) (addTime n) (requestTime n) (responseTime n) (queryTime n) (arityTime n) (replyTime n)
    let hashTime := fun n => NativeDraw.challengeTime (overhead n) (tapeWidth n) (savedCap n) (remainingCap n)
      (comparisonTime n) (zeroTime n)
      (ExecutionProfile.runtimeBound (overhead n) (tapeWidth n) (work n) (visits n) (queries n) (tickTime n) (queryTime n))
    PolynomiallyBounded (fun n => NativeCache.liveTime (overhead n) (3 * width n) (liveCap n)
      (messageTime n) (pointTime n) (hashTime n) + zeroTime n +
      2061 * overhead n (8192 * frameWidth (width n) (managedCap n) (liveCap n))) ∧
    PolynomiallyBounded (fun n => NativeCache.managedTime (overhead n) (3 * width n) (managedCap n) (liveCap n)
      (messageTime n) (pointTime n) (hashTime n) + zeroTime n +
      2061 * overhead n (8192 * frameWidth (width n) (managedCap n) (liveCap n))) ∧
    PolynomiallyBounded (fun n => NativeCache.signingTime (overhead n) (width n) (managedCap n)
      (messageTime n) (pointTime n) (scaleTime n) (subTime n) (firstTime n) (secondTime n) +
      2061 * overhead n (8192 * frameWidth (width n) (managedCap n) (liveCap n))) := by
  obtain ⟨hl, hm, hs⟩ := NativeCache.kernels_polynomial overhead work visits queries sourceWidth tapeWidth savedCap
    remainingCap tickTime comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
    width managedCap liveCap messageTime pointTime scaleTime subTime hOverhead hWork hVisits hQueries hSourceWidth
    hTapeWidth hSaved hRemaining hTick hCompare hZero hAdd hRequest hResponse hQuery hArity hReply
    hWidth hManaged hLive hMessage hPoint hScale hSub
  have ha := adapterTime_polynomial overhead width managedCap liveCap hOverhead hWidth hManaged hLive
  exact ⟨(hl.add hZero).add ha, (hm.add hZero).add ha, hs.add ha⟩

omit sizes lists laws mono routing in
theorem randomTime_polynomial (overhead : Nat → Nat → Nat)
    (width tapeWidth managedCap liveCap savedCap remainingCap comparisonTime zeroTime addTime
      requestTime responseTime queryTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hTape : PolynomiallyBounded tapeWidth) (hManaged : PolynomiallyBounded managedCap)
    (hLive : PolynomiallyBounded liveCap) (hSaved : PolynomiallyBounded savedCap)
    (hRemaining : PolynomiallyBounded remainingCap) (hCompare : PolynomiallyBounded comparisonTime)
    (hZero : PolynomiallyBounded zeroTime) (hAdd : PolynomiallyBounded addTime)
    (hRequest : PolynomiallyBounded requestTime) (hResponse : PolynomiallyBounded responseTime)
    (hQuery : PolynomiallyBounded queryTime) :
    PolynomiallyBounded (fun n => NativeUniform.runtimeBound (overhead n) (tapeWidth n) (savedCap n)
      (remainingCap n) (comparisonTime n) (zeroTime n) (addTime n) (requestTime n) (responseTime n) (queryTime n) +
        2061 * overhead n (8192 * frameWidth (width n) (managedCap n) (liveCap n))) :=
  (NativeUniform.runtimeBound_polynomial overhead tapeWidth savedCap remainingCap comparisonTime zeroTime addTime
    requestTime responseTime queryTime hOverhead hTape hSaved hRemaining hCompare hZero hAdd hRequest hResponse hQuery).add
      (adapterTime_polynomial overhead width managedCap liveCap hOverhead hWidth hManaged hLive)

end Signatures.Runtime.Schnorr.ListROM.NativeComponents
