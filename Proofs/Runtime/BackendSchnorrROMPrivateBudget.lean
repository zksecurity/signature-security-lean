import Proofs.Runtime.BackendSchnorrROMManagedBudget
import Proofs.Runtime.BackendSchnorrROMSigningBudget
import Proofs.Runtime.BackendSchnorrPrivateSamplingResources
import Proofs.Runtime.BackendSchnorrROMDraws
import Proofs.Runtime.BackendExecutionProfileCost

/-! Install challenge-family draws in hashing and private-tape draws in signing.
Both implementations use the same original scalar sampler and shared raw tape. Their complete budgets are derived from original sampler execution
profiles and primitive laws, with cumulative tape reservations for signing. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeCache

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

/-- All actual cache kernels with their source-correct draw families installed. No completed
draw, cache or signing budget is a premise. The caller supplies measured original
sampler resources and primitive encoding/cost laws. -/
theorem kernels_bound
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
    let draw := NativePrivate.code rep data cost primitive uniform ports sampler
    let challenge := NativeDraw.challenge rep data cost primitive sampler
    let firstTime := NativePrivate.samplerTime overhead work visits queries sourceWidth tapeWidth
      savedCap remainingCap tickTime comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
    let secondTime := NativePrivate.samplerTime overhead work visits queries sourceWidth tapeWidth
      (savedCap + queries) remainingCap tickTime comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
    let hashTime := NativeDraw.challengeTime overhead tapeWidth savedCap remainingCap comparisonTime zeroTime
      (ExecutionProfile.runtimeBound overhead tapeWidth work visits queries tickTime queryTime)
    Bounds control queryCost (live rep data cost primitive (rep.ty NativeUniform.stateTy) challenge)
      (fun p => CacheCompiler.Input (Q := Q) (key := hashKey) (val := scalar) rep (3 * width) liveCap p.1 ∧
        NativeUniform.StateBound (Q := Q) rep tapeWidth savedCap remainingCap p.2)
      (fun p => CacheCompiler.Output (Q := Q) (key := hashKey) (val := scalar) rep (3 * width) (liveCap + 1) p.1 ∧
        NativeUniform.StateBound (Q := Q) rep tapeWidth (savedCap + 1) remainingCap p.2)
      (liveTime overhead (3 * width) liveCap messageTime pointTime hashTime) ∧
    Bounds control queryCost (managed rep data cost primitive (rep.ty NativeUniform.stateTy) challenge)
      (fun p => ManagedInput (Q := Q) rep (3 * width) managedCap liveCap p.1 ∧
        NativeUniform.StateBound (Q := Q) rep tapeWidth savedCap remainingCap p.2)
      (fun p => ManagedOutput (Q := Q) rep (3 * width) (managedCap + 1) (liveCap + 1) p.1 ∧
        NativeUniform.StateBound (Q := Q) rep tapeWidth (savedCap + 1) remainingCap p.2)
      (managedTime overhead (3 * width) managedCap liveCap messageTime pointTime hashTime) ∧
    Bounds control queryCost (signing rep data cost primitive (rep.ty NativeUniform.stateTy) draw)
      (fun p => SigningInput (Q := Q) rep width managedCap p.1 ∧
        NativeUniform.StateBound (Q := Q) rep tapeWidth savedCap remainingCap p.2)
      (fun p => SigningOutput (Q := Q) rep width (managedCap + 1) p.1 ∧
        NativeUniform.StateBound (Q := Q) rep tapeWidth (savedCap + 2 * queries) remainingCap p.2)
      (signingTime overhead width managedCap messageTime pointTime scaleTime subTime firstTime secondTime) := by
  dsimp only
  let draw := NativePrivate.code rep data cost primitive uniform ports sampler
  let inv := fun cap => NativeUniform.StateBound (Q := Q) rep tapeWidth cap remainingCap
  let drawTime := fun cap => NativePrivate.samplerTime overhead work visits queries sourceWidth tapeWidth
    cap remainingCap tickTime comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
  have htape : tapeWidth ≤ width := by nlinarith
  have hsourceWidth := hsourceTapeWidth.trans htape
  have hdraw (cap : Nat) (hcap : cap ≤ savedCap + queries) :
      Bounds control queryCost draw (fun p => inv cap p.2)
        (fun p => Q.size (rep.ty scalar) p.1 ≤ width ∧ inv (cap + queries) p.2) (drawTime cap) := by
    have htick : ∀ n ≤ counter, ∀ size ≤ 6 * NativePrivate.samplerWidth sourceWidth tapeWidth cap remainingCap queries,
        control.loop n size ≤ tickTime := by
      intro n hn' size hs
      apply tick n hn' size
      apply hs.trans
      unfold NativePrivate.samplerWidth NativePrivate.frameWidth
      nlinarith [Nat.mul_le_mul_right tapeWidth hcap]
    have hd := NativePrivate.sampler_bound rep data cost primitive uniform ports sizes lists laws mono
      control queryCost routing dataLaws primitiveBound distribution sampler (fun _ => True)
      work visits queries sourceWidth tapeWidth cap remainingCap counter arityCap tickTime
      comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
      (by intro input _; cases input; exact hsource) htick hh hu hb hz hn hcompare hzero hadd hp hr
      hrequest hresponse hquery hread hreply
    intro input hi z hz'
    obtain ⟨ho, ht⟩ := hd input ⟨True.intro, hi⟩ z hz'
    exact ⟨⟨ho.1.trans hsourceWidth, ho.2⟩, ht⟩
  have hstore (cap : Nat) (hcap : cap ≤ savedCap + 2 * queries + 1) (saved) (hs : inv cap saved) :
      Q.size (rep.ty NativeUniform.stateTy) saved ≤ width := by
    have h := NativeUniform.state_size rep sizes lists tapeWidth cap remainingCap hh saved hs
    apply h.trans
    nlinarith [Nat.mul_le_mul_right tapeWidth hcap]
  have hheader := hh.trans htape
  have hunit := hu.trans htape
  have hbool := fun b => (hb b).trans htape
  have hdFirst := hdraw savedCap (by omega)
  have hdSecond : Bounds control queryCost draw (fun p => inv (savedCap + queries) p.2)
      (fun p => Q.size (rep.ty scalar) p.1 ≤ width ∧ inv (savedCap + 2 * queries) p.2)
      (drawTime (savedCap + queries)) := by
    simpa only [two_mul, Nat.add_assoc] using hdraw (savedCap + queries) le_rfl
  have plainTick : ∀ n ≤ counter, ∀ size ≤ 3 * tapeWidth, control.loop n size ≤ tickTime := by
    intro n hn' size hs
    apply tick n hn' size
    unfold NativePrivate.samplerWidth NativePrivate.frameWidth
    nlinarith
  have plainProfile : ∀ input : Unit, True → ExecutionProfile.Within sampler input work visits queries
      tapeWidth counter (fun n => n ≤ arityCap) := by
    intro input _ r hr'
    cases input
    obtain ⟨hw, hv, hq, hf⟩ := hsource r hr'
    exact ⟨hw, hv, hq, hf.1.trans hsourceTapeWidth, hf.2⟩
  have hsample := ExecutionProfile.within_bound control queryCost sizes tapeWidth counter
    (fun n => n ≤ arityCap) hh mono routing tickTime queryTime plainTick hquery sampler (fun _ => True)
    work visits queries plainProfile
  have hdChallenge := NativeDraw.challenge_bound rep data cost primitive sampler sizes lists laws dataLaws
    primitiveBound mono control queryCost routing tapeWidth savedCap remainingCap comparisonTime zeroTime
    (ExecutionProfile.runtimeBound overhead tapeWidth work visits queries tickTime queryTime)
    hh hu hb hz (hn 0 (by omega)) (hn 1 (by omega)) (fun n hn' => hcompare n 1 hn' (hn 1 (by omega))) hzero hsample
  have hdrawWide : Bounds control queryCost (NativeDraw.challenge rep data cost primitive sampler)
      (fun p => inv savedCap p.2)
      (fun p => Q.size (rep.ty scalar) p.1 ≤ 3 * width ∧ inv (savedCap + 1) p.2)
      (NativeDraw.challengeTime overhead tapeWidth savedCap remainingCap comparisonTime zeroTime
        (ExecutionProfile.runtimeBound overhead tapeWidth work visits queries tickTime queryTime)) := by
    intro input hi z hz'
    obtain ⟨ho, ht⟩ := hdChallenge input hi z hz'
    exact ⟨⟨ho.1.trans (by omega), ho.2⟩, ht⟩
  have advance (saved) (hs : inv savedCap saved) : inv (savedCap + 1) saved :=
    ⟨NativeUniform.tape_mono rep tapeWidth savedCap (savedCap + 1) saved.1 hs.1 (by omega), hs.2⟩
  refine ⟨?_, ?_, ?_⟩
  · exact live_bound rep data cost primitive (rep.ty NativeUniform.stateTy) (NativeDraw.challenge rep data cost primitive sampler) sizes lists laws dataLaws
      primitiveBound mono control queryCost routing (inv savedCap) (inv (savedCap + 1)) advance
      (3 * width) liveCap messageTime pointTime _ (by omega) (by omega)
      (fun b => (hbool b).trans (by omega))
      (fun s hs => (hstore savedCap (by omega) s hs).trans (by omega))
      (fun s hs => (hstore (savedCap + 1) (by omega) s hs).trans (by omega)) hm hg hdrawWide
  · exact managed_bound rep data cost primitive (rep.ty NativeUniform.stateTy) (NativeDraw.challenge rep data cost primitive sampler) sizes lists laws dataLaws
      primitiveBound mono control queryCost routing (inv savedCap) (inv (savedCap + 1)) advance
      (3 * width) managedCap liveCap messageTime pointTime _ (by omega) (by omega)
      (fun b => (hbool b).trans (by omega))
      (fun s hs => (hstore savedCap (by omega) s hs).trans (by omega))
      (fun s hs => (hstore (savedCap + 1) (by omega) s hs).trans (by omega)) hm hg hdrawWide
  · exact signing_bound rep data cost primitive (rep.ty NativeUniform.stateTy) draw sizes lists laws dataLaws
      primitiveBound mono control queryCost routing (inv savedCap) (inv (savedCap + queries)) (inv (savedCap + 2 * queries))
      width managedCap messageTime pointTime scaleTime subTime (drawTime savedCap) (drawTime (savedCap + queries))
      hheader hunit hbool (hstore savedCap (by omega)) (hstore (savedCap + queries) (by omega))
      (hstore (savedCap + 2 * queries) (by omega)) hm hg hscale hsub hdFirst hdSecond

omit sizes lists laws mono routing in
theorem kernels_polynomial (overhead : Nat → Nat → Nat)
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
    PolynomiallyBounded (fun n => liveTime (overhead n) (3 * width n) (liveCap n)
      (messageTime n) (pointTime n) (hashTime n)) ∧
    PolynomiallyBounded (fun n => managedTime (overhead n) (3 * width n) (managedCap n) (liveCap n)
      (messageTime n) (pointTime n) (hashTime n)) ∧
    PolynomiallyBounded (fun n => signingTime (overhead n) (width n) (managedCap n)
      (messageTime n) (pointTime n) (scaleTime n) (subTime n) (firstTime n) (secondTime n)) := by
  have hFirst := NativePrivate.samplerTime_polynomial overhead work visits queries sourceWidth tapeWidth savedCap remainingCap
    tickTime comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
    hOverhead hWork hVisits hQueries hSourceWidth hTapeWidth hSaved hRemaining hTick hCompare hZero hAdd
    hRequest hResponse hQuery hArity hReply
  have hSecond := NativePrivate.samplerTime_polynomial overhead work visits queries sourceWidth tapeWidth
    (fun n => savedCap n + queries n) remainingCap tickTime comparisonTime zeroTime addTime
    requestTime responseTime queryTime arityTime replyTime hOverhead hWork hVisits hQueries hSourceWidth
    hTapeWidth (hSaved.add hQueries) hRemaining hTick hCompare hZero hAdd hRequest hResponse hQuery hArity hReply
  have hRaw := ExecutionProfile.runtimeBound_polynomial overhead tapeWidth work visits queries tickTime queryTime
    hOverhead hTapeWidth hWork hVisits hQueries hTick hQuery
  have hHash := NativeDraw.challengeTime_polynomial overhead tapeWidth savedCap remainingCap comparisonTime zeroTime _
    hOverhead hTapeWidth hSaved hRemaining hCompare hZero hRaw
  have hWidth3 : PolynomiallyBounded (fun n => 3 * width n) := (PolynomiallyBounded.const 3).mul hWidth
  exact ⟨liveTime_polynomial overhead _ liveCap messageTime pointTime _ hOverhead hWidth3 hLive hMessage hPoint hHash,
    managedTime_polynomial overhead _ managedCap liveCap messageTime pointTime _
      hOverhead hWidth3 hManaged hLive hMessage hPoint hHash,
    signingTime_polynomial overhead width managedCap messageTime pointTime scaleTime subTime _ _
      hOverhead hWidth hManaged hMessage hPoint hScale hSub hFirst hSecond⟩

end Signatures.Runtime.Schnorr.ListROM.NativeCache
