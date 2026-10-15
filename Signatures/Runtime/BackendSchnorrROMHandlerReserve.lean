import Signatures.Runtime.BackendSchnorrROMHandlerBudget

/-! Reserve cache entries and private/challenge tape cells for future adaptive
requests. Runtime is charged at fixed maximum capacities, while each call
consumes one reservation. No enumeration of messages or random arities occurs. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.ListROM.NativeHandler

open BackendProgram RawTape NativeInterface NativeComponents

universe v w

section Reservations

variable {C : StepClass.{0, v}} [C.HasProd]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M Input Output : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

structure ReservedState (width tapeWidth managedCap liveCap savedCap remainingCap drawCap remaining : Nat)
    (saved : Shared.Store F G₁ M) : Prop where
  store : StoreBound (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap saved
  managed : saved.1.2.1.length + remaining ≤ managedCap
  live : saved.1.2.2.length + remaining ≤ liveCap
  tape : saved.2.1.length + remaining * drawCap ≤ savedCap

theorem reserved_weaken (width tapeWidth managedCap liveCap savedCap remainingCap drawCap a b : Nat)
    (hab : a ≤ b) (saved : Shared.Store F G₁ M)
    (hs : ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap drawCap b saved) :
    ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap drawCap a saved :=
  ⟨hs.store, by have := hs.managed; omega, by have := hs.live; omega,
    (Nat.add_le_add_left (Nat.mul_le_mul_right drawCap hab) _).trans hs.tape⟩

theorem reserved_lower (width tapeWidth managedCap liveCap savedCap remainingCap drawCap remaining : Nat)
    (saved : Shared.Store F G₁ M)
    (hs : ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap drawCap remaining saved) :
    StoreBound (Q := Q) rep width tapeWidth (managedCap - remaining) (liveCap - remaining)
      (savedCap - remaining * drawCap) remainingCap saved :=
  ⟨⟨hs.store.caches.config, ⟨hs.store.caches.managed.1, by have := hs.managed; omega⟩,
      ⟨hs.store.caches.live.1, by have := hs.live; omega⟩⟩,
    ⟨hs.store.tape.1.1, by have := hs.tape; omega⟩, hs.store.tape.2⟩

variable [C.HasSum] {iface : Interface (C := C) unifSpec}
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)

/-- Internal composition rule: the maximum-capacity budget supplies runtime,
and a smaller-capacity instance proves that the unused reservations survive. -/
theorem bound_reserved_of_bounds
    (step : Code Q unifSpec iface (StepClass.HasProd.prod bd.pos (rep.ty storeTy))
      (StepClass.HasProd.prod bd.idx (rep.ty storeTy)))
    (width tapeWidth managedCap liveCap savedCap remainingCap drawCap arityCap portWidth remaining : Nat)
    (budget : Nat → Nat → Nat → Nat)
    (bounds : ∀ mc ≤ managedCap, ∀ lc ≤ liveCap, ∀ sc ≤ savedCap,
      Bounds control queryCost step
        (fun p => RequestBound (Q := Q) rep width arityCap p.1 ∧
          StoreBound (Q := Q) rep width tapeWidth mc lc sc remainingCap p.2)
        (fun p => Q.size bd.idx p.1 ≤ portWidth ∧
          StoreBound (Q := Q) rep width tapeWidth (mc + 1) (lc + 1) (sc + drawCap) remainingCap p.2)
        (budget mc lc sc)) :
    Bounds control queryCost step
      (fun p => RequestBound (Q := Q) rep width arityCap p.1 ∧
        ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap drawCap (remaining + 1) p.2)
      (fun p => Q.size bd.idx p.1 ≤ portWidth ∧
        ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap drawCap remaining p.2)
      (budget managedCap liveCap savedCap) := by
  intro input hi out hout
  have ht := (bounds managedCap le_rfl liveCap le_rfl savedCap le_rfl input ⟨hi.1, hi.2.store⟩ out hout).2
  obtain ⟨ho, _⟩ := bounds (managedCap - (remaining + 1)) (Nat.sub_le _ _)
    (liveCap - (remaining + 1)) (Nat.sub_le _ _) (savedCap - (remaining + 1) * drawCap) (Nat.sub_le _ _)
    input ⟨hi.1, reserved_lower rep width tapeWidth managedCap liveCap savedCap remainingCap drawCap
      (remaining + 1) input.2 hi.2⟩ out hout
  have hm := hi.2.managed
  have hl := hi.2.live
  have hs := hi.2.tape
  have hm' := ho.2.caches.managed.2
  have hl' := ho.2.caches.live.2
  have hs' := ho.2.tape.1.2
  simp only [Nat.add_mul, Nat.one_mul] at hs hs'
  refine ⟨⟨ho.1, ?_, by omega, by omega, by omega⟩, ht⟩
  exact store_mono rep width tapeWidth (managedCap - (remaining + 1) + 1) (liveCap - (remaining + 1) + 1)
    (savedCap - (remaining + 1) * drawCap + drawCap) remainingCap managedCap liveCap savedCap remainingCap
    (by omega) (by omega) (by simp only [Nat.add_mul, Nat.one_mul]; omega) le_rfl out.value.2 ho.2

end Reservations

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive] [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ K M Input Output : Type} [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output)
  (ports : NativeInterface.Ports (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead) (dispatchLaws : DispatchCostLaws (Q := Q) overhead)

include sizes lists laws mono routing dispatchLaws

theorem code_bound_reserved
    (dataLaws : DataCostLaws rep.data data overhead)
    (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
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
    (hread : ∀ n ≤ arityCap, Q.cost privatePorts.arity n ≤ arityTime)
    (hreply : ∀ n ≤ arityCap, ∀ r, Q.size rep.data.nat r ≤ tapeWidth → Q.cost privatePorts.reply (r, n) ≤ replyTime)
    (hsourceTapeWidth : sourceWidth ≤ tapeWidth)
    (hstoreWidth : (6 * (savedCap + 2 * queries + 1 + remainingCap) + 3) * tapeWidth ≤ width)
    (hm : ∀ x y : M, Q.size (rep.ty message) x ≤ 3 * width → Q.size (rep.ty message) y ≤ 3 * width →
      (primitiveBound .messageEq).time (x, y) ≤ messageTime)
    (hg : ∀ x y : G₁, Q.size (rep.ty point₁) x ≤ 3 * width → Q.size (rep.ty point₁) y ≤ 3 * width →
      (primitiveBound .point₁Eq).time (x, y) ≤ pointTime)
    (hscale : ∀ z : F, ∀ g : G₁, Q.size (rep.ty scalar) z ≤ width → Q.size (rep.ty point₁) g ≤ width →
      Q.size (rep.ty point₁) (z • g) ≤ width ∧ (primitiveBound .scale₁).time (z, g) ≤ scaleTime)
    (hsub : ∀ g pk : G₁, Q.size (rep.ty point₁) g ≤ width → Q.size (rep.ty point₁) pk ≤ width →
      Q.size (rep.ty point₁) (g - pk) ≤ width ∧ (primitiveBound .sub₁).time (g, pk) ≤ subTime)
    (portWidth encodeTime tagTime remaining : Nat)
    (caps : PortCaps rep bd ports width tapeWidth arityCap portWidth encodeTime tagTime) :
    Bounds control queryCost (code rep bd ports data cost primitive uniform privatePorts sampler)
      (fun p => RequestBound (Q := Q) rep width arityCap p.1 ∧
        ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap
          (2 * queries + 1) (remaining + 1) p.2)
      (fun p => Q.size bd.idx p.1 ≤ portWidth ∧
        ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap
          (2 * queries + 1) remaining p.2)
      (timeBudget overhead work visits queries sourceWidth tapeWidth savedCap remainingCap tickTime
        comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
        width managedCap liveCap messageTime pointTime scaleTime subTime portWidth encodeTime tagTime) := by
  apply bound_reserved_of_bounds rep bd control queryCost
    (code rep bd ports data cost primitive uniform privatePorts sampler)
    width tapeWidth managedCap liveCap savedCap remainingCap (2 * queries + 1) arityCap portWidth remaining
    (fun mc lc sc => timeBudget overhead work visits queries sourceWidth tapeWidth sc remainingCap tickTime
      comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
      width mc lc messageTime pointTime scaleTime subTime portWidth encodeTime tagTime)
  intro mc _ lc _ sc hsc
  have hsamplerWidth : NativePrivate.samplerWidth sourceWidth tapeWidth (sc + queries) remainingCap queries ≤
      NativePrivate.samplerWidth sourceWidth tapeWidth (savedCap + queries) remainingCap queries := by
    unfold NativePrivate.samplerWidth NativePrivate.frameWidth
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_right
    omega
  have htick : ∀ n ≤ counter, ∀ size ≤ 6 * NativePrivate.samplerWidth sourceWidth tapeWidth
      (sc + queries) remainingCap queries, control.loop n size ≤ tickTime :=
    fun n hn size hs => tick n hn size (hs.trans (Nat.mul_le_mul_left 6 hsamplerWidth))
  have hwidth : (6 * (sc + 2 * queries + 1 + remainingCap) + 3) * tapeWidth ≤ width :=
    (Nat.mul_le_mul_right tapeWidth (by omega)).trans hstoreWidth
  simpa only [Nat.add_assoc] using
    code_bound rep bd ports data cost primitive uniform privatePorts sizes lists laws mono control queryCost
      routing dispatchLaws dataLaws primitiveBound sampler work visits queries sourceWidth tapeWidth sc remainingCap
      counter arityCap tickTime comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
      width mc lc messageTime pointTime scaleTime subTime hsource htick hh hu hb hz hn hcompare hzero hadd
      hp hr hrequest hresponse hquery hread hreply hsourceTapeWidth hwidth hm hg hscale hsub portWidth encodeTime tagTime caps

end Signatures.Runtime.Schnorr.ListROM.NativeHandler
