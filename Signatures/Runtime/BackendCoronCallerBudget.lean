import Signatures.Runtime.BackendCoronHandlerState
import Signatures.Runtime.BackendCallerIndexedResource

/-! Native BLS co-CDH caller-phase resource substitution. The attacker supplies
bounds on its own realized local work, queries, reachable boundary values, and
reply-dependent state transitions. Native handler costs and persistent-cache
invariants are conclusions of the primitive-contract proofs, not premises on
the assembled reduction. Challenge setup and final extraction are separate. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Coron.NativeHandler

open BackendProgram ReplyCompiler

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂ (M × G₁))
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (data : DataCode Q rep.data) (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (mono : Monotone overhead) (routing : RoutingCostLaws control overhead)
  (localLaws : LocalCostLaws Q overhead) (dispatchLaws : DispatchCostLaws (Q := Q) overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

include sizes lists mono routing localLaws dispatchLaws dataLaws

set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] PFunctor.Idx

theorem caller_bound
    (qS messageWidth width scalarWidth coinWidth groupWidth cap routeWidth fuel localTime tickTime : Nat)
    (queries : Fin 3 → Nat) (comparisonTime scalarTime coinTime opTime adapterTime dynamicTime : Nat)
    (hh : header ≤ width) (hm : messageWidth ≤ width) (hroute : 8 * width ≤ routeWidth)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ scalarWidth)
    (hc : ∀ x : Fin (qS + 1), Q.size (rep.ty (boundedNat qS)) x ≤ coinWidth)
    (hg : ∀ x : G₁, Q.size (rep.ty point₁) x ≤ groupWidth)
    (hw : storeWidth header messageWidth scalarWidth coinWidth groupWidth cap ≤ width)
    (caps : PortCaps rep bd ports width adapterTime)
    (dynamicSamples : DynamicSamplingCaps rep bd ports sampler control queryCost width dynamicTime)
    (values : NativeValueCaps (Q := Q) rep qS width)
    (ops : NativeInstructionCaps rep cost primitive primitiveBound qS width comparisonTime opTime)
    (samples : NativeSamplingCaps rep samplingCode control queryCost qS scalarTime coinTime)
    (callerInv : Nat → R.machine.State → Prop)
    (hcallerStep : ∀ n state, callerInv (n + 1) state → ∀ i next,
      R.machine.view state = .inr ⟨i, next⟩ →
        RequestSized (Q := Q) rep width i ∧
        RequestMessages (fun m => Q.size (rep.ty message) m ≤ messageWidth) i ∧
        ∀ reply, callerInv n (next reply))
    (hcallerWidth : ∀ n state, callerInv n state →
      Q.size R.state state ≤ routeWidth ∧ Q.size bd.head (R.machine.head state) ≤ routeWidth)
    (htick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ tickTime)
    (pk : G₂) (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M))
    (hiCaller : callerInv fuel (R.machine.init pk))
    (hiStore : ReservedState (Q := Q) rep qS messageWidth width cap fuel saved)
    (hiKey : Q.size bd.input pk ≤ routeWidth)
    (hbudget : GeneralCaller.Budget R (generalReplies M G₁ randomBound) generalKind fuel pk localTime queries)
    (z : Run (Option (M × G₁) × (machineStore qS).Value (cryptoBase F G₁ G₂ M M)))
    (hz : z ∈ support ((caller rep bd ports sampler data samplingCode cost primitive R qS fuel).run
      control queryCost (pk, saved))) :
    StateInvariant (Q := Q) rep qS messageWidth width cap z.value.2 ∧
      z.steps ≤ localTime + (∑ k, queries k * nativeHandlerTime overhead width cap comparisonTime scalarTime
        coinTime opTime adapterTime dynamicTime) + 3 * overhead (32 * routeWidth) +
        (fuel + 1) * (42 * overhead (32 * routeWidth) + tickTime) := by
  let H := executed rep bd ports sampler data samplingCode cost primitive control queryCost qS
  let inv := fun n (p : R.machine.State × (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) =>
    n ≤ fuel ∧ callerInv n p.1 ∧ ReservedState (Q := Q) rep qS messageWidth width cap n p.2
  let post := StateInvariant (Q := Q) rep qS messageWidth width cap
  let time := nativeHandlerTime overhead width cap comparisonTime scalarTime coinTime opTime adapterTime dynamicTime
  have hstep : ∀ n state store, inv (n + 1) (state, store) → ∀ i next,
      R.machine.view state = .inr ⟨i, next⟩ → ∀ p ∈ support ((H i).run store),
        inv n (next p.1.value, p.2) ∧ (generalReplies M G₁ randomBound).allows i p.1.value ∧ p.1.steps ≤ time := by
    intro n state store hs i next hv p hp
    obtain ⟨hrequest, hmessage, hnext⟩ := hcallerStep n state hs.2.1 i next hv
    obtain ⟨hout, _, htime⟩ := executed_reserved_bound rep bd ports sampler data samplingCode cost primitive
      control queryCost sizes lists mono routing localLaws dispatchLaws dataLaws primitiveBound
      qS messageWidth width scalarWidth coinWidth groupWidth cap n comparisonTime scalarTime coinTime opTime
      adapterTime dynamicTime hh hm hf hc hg hw caps dynamicSamples values ops samples i hrequest hmessage store hs.2.2 p hp
    exact ⟨⟨by have := hs.1; omega, hnext p.1.value, hout⟩, trivial, htime⟩
  have hpost : ∀ n state store, inv n (state, store) → post store := by
    intro n state store hs
    have hc : (machineCaches store).size + n ≤ cap := hs.2.2.2.2
    exact ⟨hs.2.2.1, hs.2.2.2.1, by omega⟩
  have hwidth : ∀ n state store, inv n (state, store) → Q.size R.state state ≤ routeWidth ∧
      Q.size (rep.ty (machineStore qS)) store ≤ routeWidth ∧ Q.size bd.head (R.machine.head state) ≤ routeWidth := by
    intro n state store hs
    obtain ⟨hstate, hhead⟩ := hcallerWidth n state hs.2.1
    exact ⟨hstate, hs.2.2.1.trans (by omega), hhead⟩
  have hreply : ∀ n state store, inv (n + 1) (state, store) → ∀ i next,
      R.machine.view state = .inr ⟨i, next⟩ → ∀ p ∈ support ((H i).run store), Q.size bd.idx ⟨i, p.1.value⟩ ≤ routeWidth := by
    intro n state store hs i next hv p hp
    obtain ⟨hrequest, hmessage, _⟩ := hcallerStep n state hs.2.1 i next hv
    have h := executed_reserved_bound rep bd ports sampler data samplingCode cost primitive control queryCost
      sizes lists mono routing localLaws dispatchLaws dataLaws primitiveBound
      qS messageWidth width scalarWidth coinWidth groupWidth cap n comparisonTime scalarTime coinTime opTime
      adapterTime dynamicTime hh hm hf hc hg hw caps dynamicSamples values ops samples i hrequest hmessage store hs.2.2 p hp
    exact h.2.1.trans hroute
  have hloop : ∀ n state store, inv n (state, store) →
      control.loop n (Q.size (Caller.frame R (rep.ty (machineStore qS))) (state, store)) ≤ tickTime := by
    intro n state store hs
    obtain ⟨hstate, hstore, _⟩ := hwidth n state store hs
    have hp := sizes.prod_le R.state (rep.ty (machineStore qS)) (state, store)
    dsimp only at hp
    exact htick n hs.1 _ (by dsimp only [Caller.frame]; omega)
  exact Caller.assembled_bound_indexed_of_width R (rep.ty (machineStore qS)) control queryCost
    (code rep bd ports sampler data samplingCode cost primitive qS) H
    (code_executed_run rep bd ports sampler data samplingCode cost primitive control queryCost qS)
    (generalReplies M G₁ randomBound) generalKind (fun _ => time) inv post tickTime hstep hpost hloop
    sizes localLaws dispatchLaws mono routing routeWidth fuel localTime queries (by omega)
    hwidth hreply (pk, saved) ⟨le_rfl, hiCaller, hiStore⟩ hiKey hbudget z hz

end Signatures.Runtime.Coron.NativeHandler
