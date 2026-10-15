import Signatures.Runtime.BackendSchnorrAGMHandlerBudget

/-! Capacity reserved for a bounded number of future adaptive requests.
Each actual call consumes one reservation and grows each list by at most one.
The runtime uses the fixed maximum capacities throughout the execution. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Handler

open BackendProgram Interface

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M Input Output : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

structure ReservedState (width cap basisCap signedCap remaining : Nat)
    (saved : (G₁ × G₁) × EncodedState F G₁ M) : Prop where
  store : HandlerComponents.StoreBound (Q := Q) rep width cap basisCap signedCap saved
  cache : saved.2.1.length + remaining ≤ cap
  basis : saved.2.2.1.length + remaining ≤ basisCap
  signed : saved.2.2.2.1.length + remaining ≤ signedCap

omit [C.HasSum] in
theorem reserved_weaken (width cap basisCap signedCap a b : Nat) (hab : a ≤ b)
    (saved : (G₁ × G₁) × EncodedState F G₁ M)
    (hs : ReservedState (Q := Q) rep width cap basisCap signedCap b saved) :
    ReservedState (Q := Q) rep width cap basisCap signedCap a saved :=
  ⟨hs.store, by have := hs.cache; omega, by have := hs.basis; omega, by have := hs.signed; omega⟩

omit [C.HasSum] in
theorem reserved_lower (width cap basisCap signedCap remaining : Nat)
    (saved : (G₁ × G₁) × EncodedState F G₁ M)
    (hs : ReservedState (Q := Q) rep width cap basisCap signedCap remaining saved) :
    HandlerComponents.StoreBound (Q := Q) rep width (cap - remaining) (basisCap - remaining) (signedCap - remaining) saved :=
  ⟨hs.store.config, hs.store.state.cache, by have := hs.cache; omega,
    by have := hs.basis; omega, hs.store.state.history.signed, by have := hs.signed; omega⟩

variable [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (randomPorts : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))

theorem primitiveCaps_restrict (width basisCap arityCap lowerBasis : Nat) (t : Times) (hle : lowerBasis ≤ basisCap)
    (h : PrimitiveCaps rep cost primitive randomPorts sampler control queryCost primitiveBound width basisCap arityCap t) :
    PrimitiveCaps rep cost primitive randomPorts sampler control queryCost primitiveBound width lowerBasis arityCap t :=
  { h with
    natural := fun n hn => h.natural n (hn.trans (max_le_max (Nat.add_le_add_right hle 1) le_rfl))
    comparison := fun n hn => h.comparison n (hn.trans hle)
    subtract := fun n hn => h.subtract n (hn.trans hle)
    increment := fun n hn => h.increment n (hn.trans hle) }

variable [C.HasOption] [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  [QD : Q.IsDistributive] [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output) (ports : Ports (Q := Q) rep bd)
  (data : DataCode Q rep.data)
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead) (mono : Monotone overhead)
  (routing : RoutingCostLaws control overhead) (dispatchLaws : DispatchCostLaws (Q := Q) overhead)

include sizes lists laws dataLaws mono routing dispatchLaws

theorem code_bound_reserved
    (width cap basisCap signedCap groupCap rowCap coeffCap arityCap portWidth remaining : Nat) (t : Times)
    (hh : header ≤ width)
    (caps : PortCaps rep bd ports width groupCap rowCap coeffCap arityCap portWidth t.requestTime t.tagTime)
    (primitives : PrimitiveCaps rep cost primitive randomPorts sampler control queryCost primitiveBound width basisCap arityCap t) :
    Bounds control queryCost (code rep bd ports data cost primitive randomPorts sampler)
      (fun input => RequestBound (Q := Q) rep width groupCap rowCap coeffCap arityCap input.1 ∧
        ReservedState (Q := Q) rep width cap basisCap signedCap (remaining + 1) input.2)
      (fun output => Q.size bd.idx output.1 ≤ portWidth ∧
        ReservedState (Q := Q) rep width cap basisCap signedCap remaining output.2)
      (timeBudget overhead width cap basisCap signedCap groupCap rowCap coeffCap portWidth t) := by
  have hfull := code_bound rep cost primitive randomPorts sampler control queryCost primitiveBound bd ports data
    sizes lists laws dataLaws mono routing dispatchLaws width cap basisCap signedCap groupCap rowCap coeffCap arityCap portWidth t hh caps primitives
  have hlower := code_bound rep cost primitive randomPorts sampler control queryCost primitiveBound bd ports data
    sizes lists laws dataLaws mono routing dispatchLaws width (cap - (remaining + 1)) (basisCap - (remaining + 1))
    (signedCap - (remaining + 1)) groupCap rowCap coeffCap arityCap portWidth t hh caps
    (primitiveCaps_restrict (rep := rep) (cost := cost) (primitive := primitive) (randomPorts := randomPorts)
      (sampler := sampler) (control := control) (queryCost := queryCost) (primitiveBound := primitiveBound)
      width basisCap arityCap (basisCap - (remaining + 1)) t (Nat.sub_le _ _) primitives)
  intro input hi out hout
  have ht := (hfull input ⟨hi.1, hi.2.store⟩ out hout).2
  obtain ⟨ho, _⟩ := hlower input ⟨hi.1, reserved_lower rep width cap basisCap signedCap (remaining + 1) input.2 hi.2⟩ out hout
  have hc := hi.2.cache
  have hn := hi.2.basis
  have hs := hi.2.signed
  have hcache := ho.2.state.cacheLength
  have hbasis := ho.2.state.history.basisLength
  have hsigned := ho.2.state.history.signedLength
  refine ⟨⟨ho.1, ?_, by omega, by omega, by omega⟩, ht⟩
  exact HandlerComponents.store_mono rep width
    (cap - (remaining + 1) + 1) (basisCap - (remaining + 1) + 1) (signedCap - (remaining + 1) + 1)
    cap basisCap signedCap (by omega) (by omega) (by omega) _ ho.2

end Signatures.Runtime.SchnorrAGM.Native.Handler
