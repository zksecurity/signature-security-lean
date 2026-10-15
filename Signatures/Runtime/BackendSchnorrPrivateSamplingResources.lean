import Signatures.Runtime.BackendSchnorrPrivateSamplingBudget
import Signatures.Runtime.BackendStateSimulationBudget

/-! Resources for the entire native private sampler. The original sampler's
measured work, visits, queries and widths determine the transformed runtime;
raw-tape handler bounds and increasing capacities are derived internally. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativePrivate

open BackendProgram

def samplerWidth (sourceWidth width savedCap remainingCap queries : Nat) : Nat :=
  sourceWidth + frameWidth width (savedCap + queries) remainingCap

def samplerTime (overhead : Nat → Nat)
    (work visits queries sourceWidth width savedCap remainingCap tickTime comparisonTime zeroTime addTime
      requestTime responseTime queryTime arityTime replyTime : Nat) : Nat :=
  work + visits * StateSimulation.routeTime overhead
    (samplerWidth sourceWidth width savedCap remainingCap queries) tickTime +
      queries * runtimeBound overhead width (savedCap + queries) remainingCap comparisonTime zeroTime addTime
        requestTime responseTime queryTime arityTime replyTime

theorem runtimeBound_saved_mono (overhead : Nat → Nat) (mono : Monotone overhead)
    (width savedCap largerCap remainingCap comparisonTime zeroTime addTime
      requestTime responseTime queryTime arityTime replyTime : Nat) (hcap : savedCap ≤ largerCap) :
    runtimeBound overhead width savedCap remainingCap comparisonTime zeroTime addTime
      requestTime responseTime queryTime arityTime replyTime ≤
    runtimeBound overhead width largerCap remainingCap comparisonTime zeroTime addTime
      requestTime responseTime queryTime arityTime replyTime := by
  unfold runtimeBound NativeUniform.runtimeBound NativeUniform.prepareTime NativeUniform.saveTime
    NativeUniform.saveFrameWidth SeedTape.NativeScan.scanTime SeedTape.NativeScan.forwardTime
    SeedTape.NativeScan.frameWidth ListSnoc.snocTime ListSnoc.frameWidth frameWidth
  dsimp only
  repeat' first
    | exact le_rfl
    | exact hcap
    | apply Nat.add_le_add
    | apply Nat.mul_le_mul
    | apply max_le_max
    | apply mono

theorem samplerTime_polynomial (overhead : Nat → Nat → Nat)
    (work visits queries sourceWidth width savedCap remainingCap tickTime comparisonTime zeroTime addTime
      requestTime responseTime queryTime arityTime replyTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead)
    (hWork : PolynomiallyBounded work) (hVisits : PolynomiallyBounded visits)
    (hQueries : PolynomiallyBounded queries) (hSourceWidth : PolynomiallyBounded sourceWidth)
    (hWidth : PolynomiallyBounded width) (hSaved : PolynomiallyBounded savedCap)
    (hRemaining : PolynomiallyBounded remainingCap) (hTick : PolynomiallyBounded tickTime)
    (hCompare : PolynomiallyBounded comparisonTime) (hZero : PolynomiallyBounded zeroTime)
    (hAdd : PolynomiallyBounded addTime) (hRequest : PolynomiallyBounded requestTime)
    (hResponse : PolynomiallyBounded responseTime) (hQuery : PolynomiallyBounded queryTime)
    (hArity : PolynomiallyBounded arityTime) (hReply : PolynomiallyBounded replyTime) :
    PolynomiallyBounded (fun n => samplerTime (overhead n) (work n) (visits n) (queries n)
      (sourceWidth n) (width n) (savedCap n) (remainingCap n) (tickTime n) (comparisonTime n)
      (zeroTime n) (addTime n) (requestTime n) (responseTime n) (queryTime n) (arityTime n) (replyTime n)) := by
  have raw := runtimeBound_polynomial overhead width (fun n => savedCap n + queries n) remainingCap comparisonTime
    zeroTime addTime requestTime responseTime queryTime arityTime replyTime hOverhead hWidth
    (hSaved.add hQueries) hRemaining hCompare hZero hAdd hRequest hResponse hQuery hArity hReply
  unfold samplerTime StateSimulation.routeTime samplerWidth frameWidth
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {iface : Interface (C := C) unifSpec}
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (ports : Ports (Q := Q) rep (iface := iface))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes lists laws mono routing

/-- Complete actual sampler runtime and final tape capacities. All handler and
structural costs are derived from primitive laws; the only whole-execution
resource premise concerns the original sampler's profile. -/
theorem sampler_bound
    (dataLaws : DataCostLaws rep.data data overhead)
    (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
    (distribution : ∀ {A B T : Type} (a : C.Str A) (b : C.Str B) (t : C.Str T) (p : (A ⊕ B) × T),
      Q.cost (QD.distribute a b t) p ≤ overhead
        (Q.size (StepClass.HasProd.prod (StepClass.HasSum.sum a b) t) p +
          Q.size (StepClass.HasSum.sum (StepClass.HasProd.prod a t) (StepClass.HasProd.prod b t))
            (StateSimulation.distributeValue p)))
    {A B : Type} {a : C.Str A} {b : C.Str B} (program : Code Q unifSpec iface a b) (pre : A → Prop)
    (work visits queries sourceWidth width savedCap remainingCap counter arityCap tickTime
      comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime : Nat)
    (hsource : ∀ input, pre input → ExecutionProfile.Within program input work visits queries
      sourceWidth counter (fun n => n ≤ arityCap))
    (tick : ∀ n ≤ counter, ∀ size ≤ 6 * samplerWidth sourceWidth width savedCap remainingCap queries,
      control.loop n size ≤ tickTime)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hn : ∀ n ≤ arityCap + 2, Q.size rep.data.nat n ≤ width)
    (hcompare : ∀ a b, Q.size rep.data.nat a ≤ width → Q.size rep.data.nat b ≤ width →
      (primitiveBound .natEq).time (a, b) ≤ comparisonTime)
    (hzero : (primitiveBound .zero).time () ≤ zeroTime)
    (hadd : ∀ n ≤ arityCap, (primitiveBound .natAdd).time (n, 2) ≤ addTime)
    (hp : ∀ n ≤ arityCap, Q.size iface.position n ≤ width)
    (hr : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.size iface.response ⟨n, r⟩ ≤ width)
    (hrequest : ∀ n ≤ arityCap, Q.cost uniform.request n ≤ requestTime)
    (hresponse : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.cost uniform.response ⟨n, r⟩ ≤ responseTime)
    (hquery : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), queryCost n r +
      control.query (Q.size iface.position n) (Q.size iface.response ⟨n, r⟩) ≤ queryTime)
    (hread : ∀ n ≤ arityCap, Q.cost ports.arity n ≤ arityTime)
    (hreply : ∀ n ≤ arityCap, ∀ r, Q.size rep.data.nat r ≤ width → Q.cost ports.reply (r, n) ≤ replyTime) :
    Bounds control queryCost (code rep data cost primitive uniform ports program)
      (fun p => pre p.1 ∧ NativeUniform.StateBound (Q := Q) rep width savedCap remainingCap p.2)
      (fun p => Q.size b p.1 ≤ sourceWidth ∧
        NativeUniform.StateBound (Q := Q) rep width (savedCap + queries) remainingCap p.2)
      (samplerTime overhead work visits queries sourceWidth width savedCap remainingCap tickTime
        comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime) := by
  let W := samplerWidth sourceWidth width savedCap remainingCap queries
  let inv := fun used => NativeUniform.StateBound (Q := Q) rep width (savedCap + used) remainingCap
  let drawTime := runtimeBound overhead width (savedCap + queries) remainingCap comparisonTime zeroTime addTime
    requestTime responseTime queryTime arityTime replyTime
  have hw : width ≤ W := by dsimp [W, samplerWidth, frameWidth]; nlinarith
  have hsw : sourceWidth ≤ W := Nat.le_add_right _ _
  have hstore (used) (hc : used ≤ queries) (saved) (hs : inv used saved) :
      Q.size (rep.ty NativeUniform.stateTy) saved ≤ W := by
    have hsize := NativeUniform.state_size rep sizes lists width (savedCap + used) remainingCap hh saved hs
    have hm := Nat.mul_le_mul_right width hc
    dsimp only [W, samplerWidth, frameWidth]
    nlinarith
  have hdraw (used) (hc : used < queries) (i) (hi : i ≤ arityCap) (saved) (hs : inv used saved)
      (z) (hz' : z ∈ support ((handler rep data cost primitive uniform ports).run control queryCost (i, saved))) :
      inv (used + 1) z.value.2 ∧ z.steps ≤ drawTime := by
    obtain ⟨ho, ht⟩ := handler_bound rep data cost primitive uniform ports sizes lists laws mono control queryCost
      routing dataLaws primitiveBound width (savedCap + used) remainingCap arityCap comparisonTime zeroTime addTime
      requestTime responseTime queryTime arityTime replyTime hh hu hb hz hn hcompare hzero hadd hp hr
      hrequest hresponse hquery hread hreply (i, saved) ⟨hi, hs⟩ z hz'
    refine ⟨?_, ht.trans ?_⟩
    · simpa only [inv, Nat.add_assoc] using ho.2.2
    · exact runtimeBound_saved_mono overhead mono width (savedCap + used) (savedCap + queries) remainingCap
        comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime (by omega)
  have charges := StateSimulation.structuralBound (rep.ty NativeUniform.stateTy) control sizes laws mono
    routing distribution W counter tickTime (hh.trans hw) tick
  intro input hi z hz'
  have original := hsource input.1 hi.1
  have widened : ExecutionProfile.Within program input.1 work visits queries W counter (fun n => n ≤ arityCap) := by
    intro r hr'
    obtain ⟨hwork, hvisits, hqueries, hfits⟩ := original r hr'
    exact ⟨hwork, hvisits, hqueries, hfits.1.trans hsw, hfits.2⟩
  obtain ⟨consumed, hc, hout, _, ht⟩ := StateSimulation.native_bound (rep.ty NativeUniform.stateTy)
    control queryCost (handler rep data cost primitive uniform ports) inv queries W counter
    (StateSimulation.routeTime overhead W tickTime) drawTime (fun n => n ≤ arityCap)
    charges hstore hdraw semantics (handler_denote rep data cost primitive uniform ports)
    program input.1 work visits queries widened 0 input.2 (by simpa [inv] using hi.2) (by omega) z hz'
  obtain ⟨metrics, _, _, _, _, _, _, houtput⟩ := StateSimulation.native_resources
    (rep.ty NativeUniform.stateTy) control queryCost (handler rep data cost primitive uniform ports)
    semantics (handler_denote rep data cost primitive uniform ports) program input.1 work visits queries
    sourceWidth counter (fun n => n ≤ arityCap) original input.2 z hz'
  have hfinal : NativeUniform.StateBound (Q := Q) rep width (savedCap + consumed) remainingCap z.value.2 := by
    simpa only [inv, Nat.zero_add] using hout
  exact ⟨⟨houtput, NativeUniform.tape_mono rep width (savedCap + consumed) (savedCap + queries)
    _ hfinal.1 (by omega), hfinal.2⟩, ht⟩

end Signatures.Runtime.Schnorr.RawTape.NativePrivate
