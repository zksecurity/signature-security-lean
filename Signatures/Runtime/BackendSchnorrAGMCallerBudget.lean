import Signatures.Runtime.BackendSchnorrAGMHandlerReserve
import Signatures.Runtime.BackendCallerIndexedResource

/-! Additive caller overhead for the executed Schnorr AGM dispatcher. The
attacker supplies its own realized work/query budget; primitive contracts derive
the full handler cost. Capacity reservations cover every adaptive continuation.
Recovery of caller invariants from RunsWithin is a separate boundary theorem. -/

open OracleComp OracleSpec PFunctor Schnorr.AGM
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Handler

open BackendProgram Interface

def kind {F G M : Type} (q : SourceRequest F G M) : Fin 3 :=
  match q.value.data with | .random _ => 0 | .hash _ => 1 | .sign _ => 2

def replies (F G M : Type) [Zero F] : GeneralCaller.ReplyContract (sourceSpec F G M) where
  allows _ _ := True
  responds q := ⟨defaultReply q, trivial⟩

def callerTime (overhead : Nat → Nat) (routeWidth fuel localTime : Nat) (queries : Fin 3 → Nat)
    (handlerTime tickTime : Nat) : Nat :=
  localTime + (∑ k, queries k * handlerTime) + 3 * overhead (32 * routeWidth) +
    (fuel + 1) * (42 * overhead (32 * routeWidth) + tickTime)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ K M Input Output : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [DecidableEq (SourceRequest F G₁ M)]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output) (ports : Ports (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (randomPorts : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)

omit [C.HasOption] QO OC in
theorem executed_mem_code (q : SourceRequest F G₁ M) (saved : (G₁ × G₁) × EncodedState F G₁ M)
    (z : Run ((sourceSpec F G₁ M).Range q) × ((G₁ × G₁) × EncodedState F G₁ M))
    (hz : z ∈ support ((executed rep bd ports data cost primitive randomPorts sampler control queryCost q).run saved)) :
    (⟨(⟨q, z.1.value⟩, z.2), z.1.steps⟩ : Run (SourceIndex F G₁ M × ((G₁ × G₁) × EncodedState F G₁ M))) ∈
      support ((code rep bd ports data cost primitive randomPorts sampler).run control queryCost (q, saved)) := by
  rw [code_executed_run rep bd ports data cost primitive randomPorts sampler control queryCost q saved]
  dsimp only [SourceIndex, sourceSpec, OracleSpec.toPFunctor, PFunctor.Idx]
  rw [support_map]
  exact ⟨z, hz, rfl⟩

variable (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead) (mono : Monotone overhead)
  (routing : RoutingCostLaws control overhead) (dispatchLaws : DispatchCostLaws (Q := Q) overhead)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

include sizes lists laws dataLaws mono routing dispatchLaws

theorem caller_bound
    (width cap basisCap signedCap groupCap rowCap coeffCap arityCap portWidth routeWidth fuel localTime tickTime : Nat)
    (t : Times) (queries : Fin 3 → Nat) (hh : header ≤ width)
    (hroute : frameWidth width cap basisCap signedCap groupCap rowCap coeffCap portWidth ≤ routeWidth)
    (caps : PortCaps rep bd ports width groupCap rowCap coeffCap arityCap portWidth t.requestTime t.tagTime)
    (primitives : PrimitiveCaps rep cost primitive randomPorts sampler control queryCost primitiveBound width basisCap arityCap t)
    (callerInv : Nat → R.machine.State → Prop)
    (hcallerStep : ∀ n state, callerInv (n + 1) state → ∀ q next,
      R.machine.view state = .inr ⟨q, next⟩ →
        RequestBound (Q := Q) rep width groupCap rowCap coeffCap arityCap q ∧ ∀ answer, callerInv n (next answer))
    (hcallerWidth : ∀ n state, callerInv n state →
      Q.size R.state state ≤ routeWidth ∧ Q.size bd.head (R.machine.head state) ≤ routeWidth)
    (htick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ tickTime)
    (input : Input) (saved : (G₁ × G₁) × EncodedState F G₁ M)
    (hiCaller : callerInv fuel (R.machine.init input))
    (hiStore : ReservedState (Q := Q) rep width cap basisCap signedCap fuel saved)
    (hiInput : Q.size bd.input input ≤ routeWidth)
    (hbudget : GeneralCaller.Budget R (replies F G₁ M) kind fuel input localTime queries)
    (z : Run (Option Output × ((G₁ × G₁) × EncodedState F G₁ M)))
    (hz : z ∈ support ((caller rep bd ports data cost primitive randomPorts sampler R fuel).run control queryCost (input, saved))) :
    ReservedState (Q := Q) rep width cap basisCap signedCap 0 z.value.2 ∧
      z.steps ≤ callerTime overhead routeWidth fuel localTime queries
        (timeBudget overhead width cap basisCap signedCap groupCap rowCap coeffCap portWidth t) tickTime := by
  let H := executed rep bd ports data cost primitive randomPorts sampler control queryCost
  let inv := fun n (p : R.machine.State × ((G₁ × G₁) × EncodedState F G₁ M)) =>
    n ≤ fuel ∧ callerInv n p.1 ∧ ReservedState (Q := Q) rep width cap basisCap signedCap n p.2
  let post := ReservedState (Q := Q) rep width cap basisCap signedCap 0
  let price := timeBudget overhead width cap basisCap signedCap groupCap rowCap coeffCap portWidth t
  have hw := frame_widths width cap basisCap signedCap groupCap rowCap coeffCap portWidth
  have hhandler := fun n => code_bound_reserved rep cost primitive randomPorts sampler control queryCost primitiveBound
    bd ports data sizes lists laws dataLaws mono routing dispatchLaws
    width cap basisCap signedCap groupCap rowCap coeffCap arityCap portWidth n t hh caps primitives
  have hstep : ∀ n state saved, inv (n + 1) (state, saved) → ∀ q next,
      R.machine.view state = .inr ⟨q, next⟩ → ∀ p ∈ support ((H q).run saved),
        inv n (next p.1.value, p.2) ∧ (replies F G₁ M).allows q p.1.value ∧ p.1.steps ≤ price := by
    intro n state saved hi q next hv p hp
    obtain ⟨hq, hnext⟩ := hcallerStep n state hi.2.1 q next hv
    have hmem := executed_mem_code rep bd ports data cost primitive randomPorts sampler control queryCost q saved p hp
    have h := hhandler n (q, saved) ⟨hq, hi.2.2⟩ _ hmem
    exact ⟨⟨by have := hi.1; omega, hnext p.1.value, h.1.2⟩, trivial, h.2⟩
  have hpost : ∀ n state saved, inv n (state, saved) → post saved :=
    fun n _ saved hi => reserved_weaken rep width cap basisCap signedCap 0 n (Nat.zero_le n) saved hi.2.2
  have hwidth : ∀ n state saved, inv n (state, saved) →
      Q.size R.state state ≤ routeWidth ∧ Q.size (rep.ty storeTy) saved ≤ routeWidth ∧
      Q.size bd.head (R.machine.head state) ≤ routeWidth := by
    intro n state saved hi
    obtain ⟨hs, hh'⟩ := hcallerWidth n state hi.2.1
    have hstore := store_size rep sizes lists width cap basisCap signedCap groupCap rowCap coeffCap portWidth
      hh primitives.bool primitives.scalar saved
      (HandlerComponents.store_mono rep width cap basisCap signedCap (cap + 1) (basisCap + 1) (signedCap + 1)
        (by omega) (by omega) (by omega) saved hi.2.2.store)
    exact ⟨hs, hstore.trans hroute, hh'⟩
  have hreply : ∀ n state saved, inv (n + 1) (state, saved) → ∀ q next,
      R.machine.view state = .inr ⟨q, next⟩ → ∀ p ∈ support ((H q).run saved),
        Q.size bd.idx ⟨q, p.1.value⟩ ≤ routeWidth := by
    intro n state saved hi q next hv p hp
    have hq := (hcallerStep n state hi.2.1 q next hv).1
    have hmem := executed_mem_code rep bd ports data cost primitive randomPorts sampler control queryCost q saved p hp
    exact (hhandler n (q, saved) ⟨hq, hi.2.2⟩ _ hmem).1.1.trans (hw.2.1.trans hroute)
  have hloop : ∀ n state saved, inv n (state, saved) →
      control.loop n (Q.size (Caller.frame R (rep.ty storeTy)) (state, saved)) ≤ tickTime := by
    intro n state saved hi
    obtain ⟨hs, hstore, _⟩ := hwidth n state saved hi
    have hp := sizes.prod_le R.state (rep.ty storeTy) (state, saved)
    dsimp only at hp
    have hhroute : header ≤ routeWidth := by omega
    have hencoded : Q.size (Caller.frame R (rep.ty storeTy)) (state, saved) ≤ 3 * routeWidth :=
      hp.trans (by omega)
    exact htick n hi.1 _ hencoded
  exact Caller.assembled_bound_indexed_of_width R (rep.ty storeTy) control queryCost
    (code rep bd ports data cost primitive randomPorts sampler) H
    (code_executed_run rep bd ports data cost primitive randomPorts sampler control queryCost)
    (replies F G₁ M) kind (fun _ => price) inv post tickTime hstep hpost hloop
    sizes laws dispatchLaws mono routing routeWidth fuel localTime queries (by omega)
    hwidth hreply (input, saved) ⟨le_rfl, hiCaller, hiStore⟩ hiInput hbudget z hz

end Signatures.Runtime.SchnorrAGM.Native.Handler
