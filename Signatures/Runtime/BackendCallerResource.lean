import Signatures.Runtime.BackendCallerComposition
import Signatures.Runtime.BackendCallerRouting
import Signatures.Runtime.BackendWithin

/-! Resource certificates for a general caller assembled with implemented
handlers. Source work/query bounds and local implementation/dispatch bounds give
the actual target program's budget. Code size is supplied by the proved compiler
expansion theorem, never by an efficiency premise for the completed solver.
-/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.BackendProgram.Caller

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {I A B S J K : Type} {source : OracleSpec I} [DecidableEq I] [Fintype K]
  {bd : Boundary C source.toPFunctor A B}
  (R : GeneralCaller.Caller (Q := Q) (bd := bd)) (store : C.Str S)
  {target : OracleSpec J} {iface : Interface (C := C) target}
  (control : ControlCosts) (queryCost : (j : J) → target.Range j → Nat)
  (handler : Code Q target iface (StepClass.HasProd.prod bd.pos store)
    (StepClass.HasProd.prod bd.idx store))
  (H : GeneralCaller.Handler (spec := source) (StateT S (OracleComp target)))
  (hhandler : ∀ i saved, handler.run control queryCost (i, saved) =
    (fun p => (⟨(⟨i, p.1.value⟩, p.2), p.1.steps⟩ : Run (source.toPFunctor.Idx × S))) <$> (H i).run saved)
  (inv : R.machine.State × S → Prop) (routingTime tickTime : Nat)
  (hstep : ∀ state saved, inv (state, saved) → ∀ i next,
    R.machine.view state = .inr ⟨i, next⟩ → ∀ p ∈ support ((H i).run saved), inv (next p.1.value, p.2))
  (hstop : ∀ state saved, inv (state, saved) →
    stopWork R store control (state, saved) ≤ Q.cost R.headCode state + routingTime)
  (hreturn : ∀ state saved, inv (state, saved) → ∀ output,
    R.machine.view state = .inl output →
      returnWork R store control (state, saved) output ≤ Q.cost R.headCode state + routingTime)
  (hquery : ∀ state saved, inv (state, saved) → ∀ i next,
    R.machine.view state = .inr ⟨i, next⟩ → ∀ p ∈ support ((H i).run saved),
      queryWork R store control (state, saved) i p.1.value p.2 ≤
        Q.cost R.headCode state + Q.cost R.updateCode (state, ⟨i, p.1.value⟩) + routingTime)
  (contract : GeneralCaller.ReplyContract source) (kind : I → K) (price : K → Nat)
  (storeInv : S → Prop)
  (hprice : ∀ i saved, storeInv saved → ∀ p ∈ support ((H i).run saved),
    storeInv p.2 ∧ contract.allows i p.1.value ∧ p.1.steps ≤ price (kind i))

include hhandler hstep hstop hreturn hquery hprice

theorem assembled_bound (fuel initialTime localTime : Nat) (queries : K → Nat)
    (htick : ∀ n ≤ fuel, ∀ state saved, inv (state, saved) →
      control.loop n (Q.size (frame R store) (state, saved)) ≤ tickTime)
    (input : A × S) (hi : inv (R.machine.init input.1, input.2)) (hs : storeInv input.2)
    (hinit : initWork R store control input ≤ Q.cost R.initCode input.1 + initialTime)
    (hcaller : GeneralCaller.Budget R contract kind fuel input.1 localTime queries)
    (z : Run (Option B × S))
    (hz : z ∈ support ((program R store handler fuel).run control queryCost input)) :
    storeInv z.value.2 ∧ z.steps ≤ localTime + (∑ k, queries k * price k) +
      initialTime + (fuel + 1) * (routingTime + tickTime) := by
  obtain ⟨reference, href, hvalue, hcost⟩ := program_refines_cost R store control queryCost handler H hhandler
    inv routingTime tickTime hstep hstop hreturn hquery fuel initialTime htick input hi hinit z hz
  obtain ⟨hout, ht⟩ := GeneralCaller.Budget.implemented_bound R contract kind fuel input.1 localTime
    queries hcaller H price storeInv hprice input.2 hs reference href
  refine ⟨?_, by omega⟩
  rw [hvalue]
  exact hout

omit hstop hreturn hquery in
/-- All dispatch allowances are derived from the sizes of reachable boundary
values. The handler price includes the implemented handler's own complete work;
the caller's original head/update work is charged only once. -/
theorem assembled_bound_of_width
    {header : Nat} (sizes : SizeLaws Q header) {overhead : Nat → Nat}
    (localLaws : LocalCostLaws Q overhead) (dispatchLaws : DispatchCostLaws (Q := Q) overhead)
    (mono : Monotone overhead) (controlLaws : RoutingCostLaws control overhead)
    (width fuel localTime : Nat) (queries : K → Nat) (hh : header ≤ width)
    (hwidth : ∀ state saved, inv (state, saved) → Q.size R.state state ≤ width ∧
      Q.size store saved ≤ width ∧ Q.size bd.head (R.machine.head state) ≤ width)
    (hreply : ∀ state saved, inv (state, saved) → ∀ i next,
      R.machine.view state = .inr ⟨i, next⟩ → ∀ p ∈ support ((H i).run saved),
        Q.size bd.idx ⟨i, p.1.value⟩ ≤ width)
    (htick : ∀ n ≤ fuel, ∀ state saved, inv (state, saved) →
      control.loop n (Q.size (frame R store) (state, saved)) ≤ tickTime)
    (input : A × S) (hi : inv (R.machine.init input.1, input.2)) (hs : storeInv input.2)
    (hin : Q.size bd.input input.1 ≤ width)
    (hcaller : GeneralCaller.Budget R contract kind fuel input.1 localTime queries)
    (z : Run (Option B × S))
    (hz : z ∈ support ((program R store handler fuel).run control queryCost input)) :
    storeInv z.value.2 ∧ z.steps ≤ localTime + (∑ k, queries k * price k) +
      3 * overhead (32 * width) + (fuel + 1) * (42 * overhead (32 * width) + tickTime) := by
  have hstop' : ∀ state saved, inv (state, saved) →
      stopWork R store control (state, saved) ≤ Q.cost R.headCode state + 42 * overhead (32 * width) := by
    intro state saved hi
    obtain ⟨hst, hstore, hhead⟩ := hwidth state saved hi
    have h := stopWork_of_width R store sizes localLaws dispatchLaws mono control controlLaws
      state saved width hh hst hstore hhead
    omega
  have hreturn' : ∀ state saved, inv (state, saved) → ∀ output,
      R.machine.view state = .inl output → returnWork R store control (state, saved) output ≤
        Q.cost R.headCode state + 42 * overhead (32 * width) := by
    intro state saved hi output hv
    obtain ⟨hst, hstore, hhead⟩ := hwidth state saved hi
    have h := returnWork_of_width R store sizes localLaws dispatchLaws mono control controlLaws
      state saved output hv width hh hst hstore hhead
    omega
  have hquery' : ∀ state saved, inv (state, saved) → ∀ i next,
      R.machine.view state = .inr ⟨i, next⟩ → ∀ p ∈ support ((H i).run saved),
        queryWork R store control (state, saved) i p.1.value p.2 ≤
          Q.cost R.headCode state + Q.cost R.updateCode (state, ⟨i, p.1.value⟩) +
            42 * overhead (32 * width) := by
    intro state saved hi i next hv p hp
    obtain ⟨hst, hstore, hhead⟩ := hwidth state saved hi
    obtain ⟨hn, hw, _⟩ := hwidth _ _ (hstep state saved hi i next hv p hp)
    exact queryWork_of_width R store sizes localLaws dispatchLaws mono control controlLaws
      state saved p.2 i next p.1.value hv width hh hst hstore hhead hn hw
        (hreply state saved hi i next hv p hp)
  obtain ⟨hstate, hstore, _⟩ := hwidth _ _ hi
  have hinit := initWork_of_width R store sizes mono control controlLaws input width hh hstore hstate hin
  exact assembled_bound R store control queryCost handler H hhandler inv (42 * overhead (32 * width))
    tickTime hstep hstop' hreturn' hquery' contract kind price storeInv hprice fuel
    (3 * overhead (32 * width)) localTime queries htick input hi hs hinit hcaller z hz

omit hstep hstop hreturn hquery hprice [C.HasOption] [Q.HasCategory] QP QS QO QD OC [DecidableEq I] in
theorem handler_denote_of_run (i : I) (saved : S) :
    handler.denote (i, saved) =
      (fun p => (⟨i, p.1⟩, p.2)) <$> (Run.value <$> H i).run saved := by
  have h := congrArg (Functor.map Run.value) (hhandler i saved)
  rw [Code.run_erase] at h
  simpa only [StateT.run_map, Functor.map_map, Prod.map] using h

theorem assembled_within
    (backend : Backend.{v, w, x} Q target iface control queryCost)
    (sizes : DescriptionSize Q) (factor : Nat) (description : backend.DescriptionBound sizes factor)
    (fuel initialTime localTime inputSize : Nat) (queries : K → Nat)
    (htick : ∀ n ≤ fuel, ∀ state saved, inv (state, saved) →
      control.loop n (Q.size (frame R store) (state, saved)) ≤ tickTime)
    (sourceProgram : A → OracleComp source B) (hsource : R.machine.ImplementsWithin sourceProgram fuel)
    (hi : ∀ input, Q.size (StepClass.HasProd.prod bd.input store) input ≤ inputSize →
      inv (R.machine.init input.1, input.2) ∧ storeInv input.2)
    (hinit : ∀ input, Q.size (StepClass.HasProd.prod bd.input store) input ≤ inputSize →
      initWork R store control input ≤ Q.cost R.initCode input.1 + initialTime)
    (hcaller : ∀ input, Q.size (StepClass.HasProd.prod bd.input store) input ≤ inputSize →
      GeneralCaller.Budget R contract kind fuel input.1 localTime queries) :
    Within backend sizes factor description (StepClass.HasProd.prod bd.input store) (result (bd := bd) store)
      inputSize (factor * (wiringDescriptionSize R store sizes + handler.descriptionSize sizes + fuel))
      (localTime + (∑ k, queries k * price k) + initialTime + (fuel + 1) * (routingTime + tickTime))
      (fun input => (some <$> simulateQ (fun i => Run.value <$> H i) (sourceProgram input.1)).run input.2) := by
  have hsemantic := handler_denote_of_run store control queryCost handler H hhandler
  have hbound := fun input hsize z hz => (assembled_bound R store control queryCost handler H hhandler
    inv routingTime tickTime hstep hstop hreturn hquery contract kind price storeInv hprice
    fuel initialTime localTime queries htick input (hi input hsize).1 (hi input hsize).2
      (hinit input hsize) (hcaller input hsize) z hz).2
  have h := within_compile backend sizes factor description (program R store handler fuel) inputSize
    (localTime + (∑ k, queries k * price k) + initialTime + (fuel + 1) * (routingTime + tickTime))
    (fun input => (some <$> simulateQ (fun i => Run.value <$> H i) (sourceProgram input.1)).run input.2)
    (by
      intro input
      have he := compiled_program_erase R store handler (fun i => Run.value <$> H i) hsemantic
        control queryCost backend fuel input.1 input.2 sourceProgram hsource
      simpa only [backend.compile_erase] using he)
    (fun input hi z hz => ⟨trivial, hbound input hi z hz⟩)
  simpa only [program_descriptionSize] using h

omit hstop hreturn hquery in
/-- A constructed backend program with the width-derived additive runtime
bound and the compiler's description bound. This is the stateful caller phase;
a scheme solver must also implement and charge initialization and extraction. -/
theorem assembled_within_of_width
    (backend : Backend.{v, w, x} Q target iface control queryCost)
    (descriptions : DescriptionSize Q) (factor : Nat)
    (description : backend.DescriptionBound descriptions factor)
    {header : Nat} (sizes : SizeLaws Q header) {overhead : Nat → Nat}
    (localLaws : LocalCostLaws Q overhead) (dispatchLaws : DispatchCostLaws (Q := Q) overhead)
    (mono : Monotone overhead) (controlLaws : RoutingCostLaws control overhead)
    (width fuel localTime inputSize : Nat) (queries : K → Nat) (hh : header ≤ width)
    (hinput : inputSize ≤ width)
    (hwidth : ∀ state saved, inv (state, saved) → Q.size R.state state ≤ width ∧
      Q.size store saved ≤ width ∧ Q.size bd.head (R.machine.head state) ≤ width)
    (hreply : ∀ state saved, inv (state, saved) → ∀ i next,
      R.machine.view state = .inr ⟨i, next⟩ → ∀ p ∈ support ((H i).run saved),
        Q.size bd.idx ⟨i, p.1.value⟩ ≤ width)
    (htick : ∀ n ≤ fuel, ∀ state saved, inv (state, saved) →
      control.loop n (Q.size (frame R store) (state, saved)) ≤ tickTime)
    (sourceProgram : A → OracleComp source B) (hsource : R.machine.ImplementsWithin sourceProgram fuel)
    (hi : ∀ input, Q.size (StepClass.HasProd.prod bd.input store) input ≤ inputSize →
      inv (R.machine.init input.1, input.2) ∧ storeInv input.2)
    (hcaller : ∀ input, Q.size (StepClass.HasProd.prod bd.input store) input ≤ inputSize →
      GeneralCaller.Budget R contract kind fuel input.1 localTime queries) :
    Within backend descriptions factor description (StepClass.HasProd.prod bd.input store) (result (bd := bd) store)
      inputSize (factor * (wiringDescriptionSize R store descriptions + handler.descriptionSize descriptions + fuel))
      (localTime + (∑ k, queries k * price k) + 3 * overhead (32 * width) +
        (fuel + 1) * (42 * overhead (32 * width) + tickTime))
      (fun input => (some <$> simulateQ (fun i => Run.value <$> H i) (sourceProgram input.1)).run input.2) := by
  have hsemantic := handler_denote_of_run store control queryCost handler H hhandler
  have h := within_compile backend descriptions factor description (program R store handler fuel) inputSize
    (localTime + (∑ k, queries k * price k) + 3 * overhead (32 * width) +
      (fuel + 1) * (42 * overhead (32 * width) + tickTime))
    (fun input => (some <$> simulateQ (fun i => Run.value <$> H i) (sourceProgram input.1)).run input.2)
    (by
      intro input
      have he := compiled_program_erase R store handler (fun i => Run.value <$> H i) hsemantic
        control queryCost backend fuel input.1 input.2 sourceProgram hsource
      simpa only [backend.compile_erase] using he)
    (by
      intro input hsize z hz
      have hin := (sizes.fst_le bd.input store input).trans (hsize.trans hinput)
      exact ⟨trivial, (assembled_bound_of_width R store control queryCost handler H hhandler
        inv tickTime hstep contract kind price storeInv hprice sizes localLaws dispatchLaws mono controlLaws
        width fuel localTime queries hh hwidth hreply htick input (hi input hsize).1 (hi input hsize).2
          hin (hcaller input hsize) z hz).2⟩)
  simpa only [program_descriptionSize] using h

end Signatures.Runtime.BackendProgram.Caller
