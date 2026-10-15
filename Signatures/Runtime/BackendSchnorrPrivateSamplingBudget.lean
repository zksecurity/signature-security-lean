import Signatures.Runtime.BackendSchnorrPrivateSampling
import Signatures.Runtime.BackendSchnorrRawUniformBudget
import Signatures.Runtime.BackendSchnorrRawUniformPolynomial
import Signatures.Runtime.BackendLanguageBudget

/-! The typed tape handler's complete routing budget, composed with the native
uniform-draw certificate. Runtime reply conversion is charged explicitly.
Whole-sampler resource composition is proved in
`BackendSchnorrPrivateSamplingResources`. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativePrivate

open BackendProgram

universe v w

def frameWidth (width savedCap remainingCap : Nat) : Nat :=
  (6 * (savedCap + remainingCap) + 16) * width

def runtimeBound (overhead : Nat → Nat) (width savedCap remainingCap comparisonTime zeroTime addTime
    requestTime responseTime queryTime arityTime replyTime : Nat) : Nat :=
  NativeUniform.runtimeBound overhead width savedCap remainingCap comparisonTime zeroTime addTime
    requestTime responseTime queryTime + arityTime + replyTime +
      32 * overhead (32 * frameWidth width savedCap remainingCap)

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
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (ports : Ports (Q := Q) rep (iface := iface))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes lists laws mono routing

theorem handler_bound_of_uniform (width savedCap remainingCap arityCap uniformTime arityTime replyTime : Nat)
    (hh : header ≤ width)
    (hn : ∀ n ≤ arityCap, Q.size rep.data.nat n ≤ width)
    (hp : ∀ n ≤ arityCap, Q.size iface.position n ≤ width)
    (hr : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.size iface.response ⟨n, r⟩ ≤ width)
    (hread : ∀ n ≤ arityCap, Q.cost ports.arity n ≤ arityTime)
    (hreply : ∀ n ≤ arityCap, ∀ r, Q.size rep.data.nat r ≤ width →
      Q.cost ports.reply (r, n) ≤ replyTime)
    (huniform : Bounds control queryCost (NativeUniform.code rep data cost primitive uniform)
      (fun p => p.1 ≤ arityCap ∧ NativeUniform.StateBound (Q := Q) rep width savedCap remainingCap p.2)
      (NativeUniform.InputBound (Q := Q) rep width (savedCap + 1) remainingCap) uniformTime) :
    Bounds control queryCost (handler rep data cost primitive uniform ports)
      (fun p => p.1 ≤ arityCap ∧ NativeUniform.StateBound (Q := Q) rep width savedCap remainingCap p.2)
      (fun p => p.1.1 ≤ arityCap ∧ Q.size iface.response p.1 ≤ width ∧
        NativeUniform.StateBound (Q := Q) rep width (savedCap + 1) remainingCap p.2)
      (uniformTime + arityTime + replyTime + 32 * overhead (32 * frameWidth width savedCap remainingCap)) := by
  let W := frameWidth width savedCap remainingCap
  let fee := overhead (32 * W)
  let old := NativeUniform.StateBound (Q := Q) rep width savedCap remainingCap
  let fresh := NativeUniform.StateBound (Q := Q) rep width (savedCap + 1) remainingCap
  let pre := fun p : Nat × List (TapeCell F) × List (TapeCell F) => p.1 ≤ arityCap ∧ old p.2
  let post := NativeUniform.InputBound (Q := Q) rep width (savedCap + 1) remainingCap
  let context := fun p : (Nat × Nat) × List (TapeCell F) × List (TapeCell F) =>
    post (p.1.1, p.2) ∧ p.1.2 ≤ arityCap
  have hw : width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have hold (s) (hs : old s) : Q.size (rep.ty NativeUniform.stateTy) s ≤ W :=
    (NativeUniform.state_size rep sizes lists width savedCap remainingCap hh s hs).trans
      (by dsimp [W, frameWidth]; nlinarith)
  have hfresh (s) (hs : fresh s) : Q.size (rep.ty NativeUniform.stateTy) s ≤ W :=
    (NativeUniform.state_size rep sizes lists width (savedCap + 1) remainingCap hh s hs).trans
      (by dsimp [W, frameWidth]; nlinarith)
  have hfee : ∀ n ≤ 32 * W, overhead n ≤ fee := fun _ h => mono h
  have hreadAtom : Bounds control queryCost (.atomic (iface := iface) ports.arity)
      (fun n => n ≤ arityCap) (fun n => n ≤ arityCap) (arityTime + fee) := by
    apply Bounds.atomic
    intro n hn'
    have hi := hp n hn'
    have ho := hn n hn'
    have ht := hread n hn'
    have hc := routing.localCall (Q.size iface.position n) (Q.size rep.data.nat n)
    exact ⟨hn', by dsimp; have := hfee _ (show Q.size iface.position n + Q.size rep.data.nat n ≤ 32 * W by omega); omega⟩
  have hstart := Bounds.first control queryCost (rep.ty NativeUniform.stateTy) (.atomic ports.arity)
    (fun n => n ≤ arityCap) (fun n => n ≤ arityCap) old (arityTime + fee) fee hreadAtom (by
      intro s hs n hn'
      have hs' := hold s hs
      have hn'' := hn n hn'
      exact (routing.retain _ _).trans (hfee _ (by omega)))
  have hctx := Language.withContext_bound_of_width sizes laws mono control queryCost routing
    (rep.ty NativeUniform.stateTy) (Q.identity rep.data.nat)
    (NativeUniform.code rep data cost primitive uniform) pre post (fun n => n ≤ arityCap)
    W fee uniformTime (hh.trans hw) (by
      intro p hi
      have hnat := (hn p.1 hi.1).trans hw
      refine ⟨hnat, hold p.2 hi.2, hnat, hi.1, ?_⟩
      exact (laws.identity rep.data.nat p.1).trans (hfee _ (by omega))) (by
      intro p ho
      exact ⟨ho.1.trans hw, hfresh p.2 ho.2⟩) huniform
  have hreplyAtom : Bounds control queryCost (.atomic (iface := iface) ports.reply)
      (fun p => p.2 ≤ arityCap ∧ Q.size rep.data.nat p.1 ≤ width)
      (fun p => p.1 ≤ arityCap ∧ Q.size iface.response p ≤ width) (replyTime + fee) := by
    apply Bounds.atomic
    intro p hi
    have hn' := hn p.2 hi.1
    have hout := hr p.2 hi.1 (NativeUniform.decodeNat p.2 p.1)
    have hin := sizes.prod_le rep.data.nat rep.data.nat p
    have ht := hreply p.2 hi.1 p.1 hi.2
    change Q.cost ports.reply p ≤ replyTime at ht
    have hc := routing.localCall (Q.size (StepClass.HasProd.prod rep.data.nat rep.data.nat) p)
      (Q.size iface.response ⟨p.2, NativeUniform.decodeNat p.2 p.1⟩)
    refine ⟨⟨hi.1, hout⟩, ?_⟩
    have := hfee _ (show Q.size (StepClass.HasProd.prod rep.data.nat rep.data.nat) p +
      Q.size iface.response ⟨p.2, NativeUniform.decodeNat p.2 p.1⟩ ≤ 32 * W by omega)
    omega
  have hfinish := Bounds.first control queryCost (rep.ty NativeUniform.stateTy) (.atomic ports.reply)
    (fun p => p.2 ≤ arityCap ∧ Q.size rep.data.nat p.1 ≤ width)
    (fun p => p.1 ≤ arityCap ∧ Q.size iface.response p ≤ width)
    fresh (replyTime + fee) fee hreplyAtom (by
      intro s hs out ho
      have hstore := hfresh s hs
      exact (routing.retain _ _).trans (hfee _ (by have := ho.2; omega)))
  have hend : Bounds (iface := iface) control queryCost (.first (rep.ty NativeUniform.stateTy) (.atomic ports.reply))
      context (fun p => p.1.1 ≤ arityCap ∧ Q.size iface.response p.1 ≤ width ∧ fresh p.2)
      (replyTime + fee + fee) := by
    intro input hi z hz
    obtain ⟨ho, ht⟩ := hfinish input ⟨⟨hi.2, hi.1.1⟩, hi.1.2⟩ z hz
    exact ⟨⟨ho.1.1, ho.1.2, ho.2⟩, ht⟩
  have hprod := @sizes.prod_le
  have hseq := routing.sequence
  have htail := Bounds.seq control queryCost _ _ pre context _
    (uniformTime + fee + 18 * fee) (replyTime + fee + fee) fee hctx hend (by
      intro input hi value hv
      have hni := (hn input.1 hi.1).trans hw
      have hsi := hold input.2 hi.2
      have hno := hv.1.1
      have hnc := hn value.1.2 hv.2
      have hso := hfresh value.2 hv.1.2
      dsimp only [post, NativeUniform.InputBound] at hno
      grind only)
  have hfull := Bounds.seq control queryCost _ _ pre pre _
    (arityTime + fee + fee) _ fee hstart htail (by
      intro input hi value hv
      have hip := hp input.1 hi.1
      have his := hold input.2 hi.2
      have hon := hn value.1 hv.1
      have hos := hold value.2 hv.2
      grind only)
  intro input hi z hz
  obtain ⟨ho, ht⟩ := hfull input hi z hz
  exact ⟨ho, ht.trans (by dsimp only [fee, W]; omega)⟩

/-- The per-draw bound is derived entirely from primitive, interface-conversion
and structural laws. No completed tape-handler runtime is assumed. -/
theorem handler_bound
    (dataLaws : DataCostLaws rep.data data overhead)
    (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
    (width savedCap remainingCap arityCap comparisonTime zeroTime addTime
      requestTime responseTime queryTime arityTime replyTime : Nat)
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
    (hreply : ∀ n ≤ arityCap, ∀ r, Q.size rep.data.nat r ≤ width →
      Q.cost ports.reply (r, n) ≤ replyTime) :
    Bounds control queryCost (handler rep data cost primitive uniform ports)
      (fun p => p.1 ≤ arityCap ∧ NativeUniform.StateBound (Q := Q) rep width savedCap remainingCap p.2)
      (fun p => p.1.1 ≤ arityCap ∧ Q.size iface.response p.1 ≤ width ∧
        NativeUniform.StateBound (Q := Q) rep width (savedCap + 1) remainingCap p.2)
      (runtimeBound overhead width savedCap remainingCap comparisonTime zeroTime addTime
        requestTime responseTime queryTime arityTime replyTime) :=
  handler_bound_of_uniform rep data cost primitive uniform ports sizes lists laws mono control queryCost routing
    width savedCap remainingCap arityCap _ arityTime replyTime hh
    (fun n h => hn n (by omega)) hp hr hread hreply
    (NativeUniform.bound rep data cost primitive uniform sizes lists laws dataLaws primitiveBound
      mono control queryCost routing width savedCap remainingCap arityCap comparisonTime zeroTime addTime
      requestTime responseTime queryTime hh hu hb hz hn hcompare hzero hadd hp hr hrequest hresponse hquery)

omit sizes lists laws mono routing in
theorem runtimeBound_polynomial (overhead : Nat → Nat → Nat)
    (width savedCap remainingCap comparisonTime zeroTime addTime requestTime responseTime queryTime
      arityTime replyTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead)
    (hWidth : PolynomiallyBounded width) (hSaved : PolynomiallyBounded savedCap)
    (hRemaining : PolynomiallyBounded remainingCap)
    (hCompare : PolynomiallyBounded comparisonTime) (hZero : PolynomiallyBounded zeroTime)
    (hAdd : PolynomiallyBounded addTime) (hRequest : PolynomiallyBounded requestTime)
    (hResponse : PolynomiallyBounded responseTime) (hQuery : PolynomiallyBounded queryTime)
    (hArity : PolynomiallyBounded arityTime) (hReply : PolynomiallyBounded replyTime) :
    PolynomiallyBounded (fun n => runtimeBound (overhead n) (width n) (savedCap n) (remainingCap n)
      (comparisonTime n) (zeroTime n) (addTime n) (requestTime n) (responseTime n) (queryTime n)
      (arityTime n) (replyTime n)) := by
  have raw := NativeUniform.runtimeBound_polynomial overhead width savedCap remainingCap comparisonTime
    zeroTime addTime requestTime responseTime queryTime hOverhead hWidth hSaved hRemaining hCompare
    hZero hAdd hRequest hResponse hQuery
  unfold runtimeBound frameWidth
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

end Signatures.Runtime.Schnorr.RawTape.NativePrivate
