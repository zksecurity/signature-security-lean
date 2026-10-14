import Signatures.Runtime.BackendCallerResource
import Signatures.Runtime.BackendCallerDescription

/-! Native caller bounds with an invariant indexed by remaining execution fuel.
A query may grow the reduction store while consuming one unit of fuel. This
supports a cache-size-plus-remaining-fuel invariant, without requiring a fixed
cache cap to be closed under arbitrarily many further requests. The comparison
uses the caller's symbolic-price budget and charges the actual native handler,
caller, routing, and control work. -/

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
  (contract : GeneralCaller.ReplyContract source) (kind : I → K) (price : K → Nat)
  (inv : Nat → R.machine.State × S → Prop) (post : S → Prop)
  (routingTime tickTime : Nat)
  (hstep : ∀ n state saved, inv (n + 1) (state, saved) → ∀ i next,
    R.machine.view state = .inr ⟨i, next⟩ → ∀ p ∈ support ((H i).run saved),
      inv n (next p.1.value, p.2) ∧ contract.allows i p.1.value ∧ p.1.steps ≤ price (kind i))
  (hpost : ∀ n state saved, inv n (state, saved) → post saved)
  (hstop : ∀ state saved, inv 0 (state, saved) →
    stopWork R store control (state, saved) ≤ Q.cost R.headCode state + routingTime)
  (hreturn : ∀ n state saved, inv (n + 1) (state, saved) → ∀ output,
    R.machine.view state = .inl output →
      returnWork R store control (state, saved) output ≤ Q.cost R.headCode state + routingTime)
  (hquery : ∀ n state saved, inv (n + 1) (state, saved) → ∀ i next,
    R.machine.view state = .inr ⟨i, next⟩ → ∀ p ∈ support ((H i).run saved),
      queryWork R store control (state, saved) i p.1.value p.2 ≤
        Q.cost R.headCode state + Q.cost R.updateCode (state, ⟨i, p.1.value⟩) + routingTime)
  (htick : ∀ n state saved, inv n (state, saved) →
    control.loop n (Q.size (frame R store) (state, saved)) ≤ tickTime)

include hhandler hstep hpost hstop hreturn hquery htick

omit [Fintype K] in
theorem fromState_priced_indexed (fuel : Nat)
    (state : R.machine.State) (saved : S) (hi : inv fuel (state, saved))
    (z : Run (Option B × S))
    (hz : z ∈ support ((fromState R store handler fuel).run control queryCost (state, saved))) :
    ∃ reference ∈ support (GeneralCaller.runFrom R
        (GeneralCaller.pricedReplies contract (fun i => price (kind i))) fuel state),
      z.value.1 = reference.value ∧ post z.value.2 ∧
        z.steps ≤ reference.steps + (fuel + 1) * (routingTime + tickTime) := by
  induction fuel generalizing state saved z with
  | zero =>
      change z ∈ support (chargeRun (control.loop 0 (Q.size (frame R store) (state, saved)))
        ((stop R store).run control queryCost (state, saved))) at hz
      rw [stop_run R store control queryCost] at hz
      simp only [chargeRun, map_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      refine ⟨⟨match R.machine.view state with | .inl output => some output | .inr _ => none,
        Q.cost R.headCode state + 1⟩, ?_, ?_, hpost 0 state saved hi, ?_⟩
      · cases hv : R.machine.view state <;> simp [GeneralCaller.runFrom, hv]
      · cases R.machine.view state <;> rfl
      · have hs := hstop state saved hi
        have hc := htick 0 state saved hi
        dsimp
        omega
  | succ fuel ih =>
      rw [fromState, Code.run, loopRun] at hz
      cases hv : R.machine.view state with
      | inl output =>
          rw [body_return_run R store control queryCost handler state saved output hv] at hz
          simp only [pure_bind, support_pure, Set.mem_singleton_iff] at hz
          subst z
          refine ⟨⟨some output, Q.cost R.headCode state + 1⟩, ?_, rfl,
            hpost (fuel + 1) state saved hi, ?_⟩
          · simp [GeneralCaller.runFrom, hv]
          · have hs := hreturn fuel state saved hi output hv
            have hc := htick (fuel + 1) state saved hi
            dsimp
            nlinarith
      | inr request =>
          rcases request with ⟨i, next⟩
          rw [body_query_run R store control queryCost handler H hhandler state saved i next hv] at hz
          simp only [bind_map_left, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
          obtain ⟨p, hp, rest, hr, rfl⟩ := hz
          obtain ⟨hn, ha, ht⟩ := hstep fuel state saved hi i next hv p hp
          obtain ⟨reference, href, hvalue, hout, hcost⟩ := ih (next p.1.value) p.2 hn rest hr
          refine ⟨⟨reference.value, Q.cost R.headCode state + price (kind i) +
            Q.cost R.updateCode (state, ⟨i, p.1.value⟩) + reference.steps + 2⟩,
            ?_, hvalue, hout, ?_⟩
          · have hreply : (⟨p.1.value, price (kind i)⟩ : Run (source.Range i)) ∈ support
                (GeneralCaller.pricedReplies contract (fun i => price (kind i)) i) := by
              simp only [GeneralCaller.pricedReplies, mem_support_bind_iff,
                support_pure, Set.mem_singleton_iff]
              exact ⟨⟨p.1.value, ha⟩, mem_support_query _ _, rfl⟩
            simp only [GeneralCaller.runFrom, hv, mem_support_bind_iff,
              support_pure, Set.mem_singleton_iff]
            exact ⟨⟨p.1.value, price (kind i)⟩, hreply, reference, href, rfl⟩
          · have hs := hquery fuel state saved hi i next hv p hp
            have hc := htick (fuel + 1) state saved hi
            dsimp
            nlinarith

theorem assembled_bound_indexed (fuel initialTime localTime : Nat) (queries : K → Nat)
    (input : A × S) (hi : inv fuel (R.machine.init input.1, input.2))
    (hinit : initWork R store control input ≤ Q.cost R.initCode input.1 + initialTime)
    (hcaller : GeneralCaller.Budget R contract kind fuel input.1 localTime queries)
    (z : Run (Option B × S))
    (hz : z ∈ support ((program R store handler fuel).run control queryCost input)) :
    post z.value.2 ∧ z.steps ≤ localTime + (∑ k, queries k * price k) +
      initialTime + (fuel + 1) * (routingTime + tickTime) := by
  rw [program_run R store control queryCost handler, support_map] at hz
  obtain ⟨rest, hr, rfl⟩ := hz
  obtain ⟨reference, href, _, hout, hcost⟩ := fromState_priced_indexed R store control queryCost
    handler H hhandler contract kind price inv post routingTime tickTime hstep hpost hstop hreturn hquery htick
    fuel _ _ hi rest hr
  have hreference : (⟨reference.value, Q.cost R.initCode input.1 + reference.steps + 1⟩ : Run (Option B)) ∈
      support (GeneralCaller.run R (GeneralCaller.pricedReplies contract (fun i => price (kind i))) fuel input.1) := by
    simp only [GeneralCaller.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
    exact ⟨reference, href, rfl⟩
  have hb := hcaller price _ hreference
  exact ⟨hout, by dsimp at hb ⊢; omega⟩

omit hstop hreturn hquery in
/-- Derive all dispatch work from encoded widths while allowing the cache to
consume the remaining query allowance. The handler's complete measured budget
is supplied per enabled request, not for the whole composed execution. -/
theorem assembled_bound_indexed_of_width
    {header : Nat} (sizes : SizeLaws Q header) {overhead : Nat → Nat}
    (localLaws : LocalCostLaws Q overhead) (dispatchLaws : DispatchCostLaws (Q := Q) overhead)
    (mono : Monotone overhead) (controlLaws : RoutingCostLaws control overhead)
    (width fuel localTime : Nat) (queries : K → Nat) (hh : header ≤ width)
    (hwidth : ∀ n state saved, inv n (state, saved) → Q.size R.state state ≤ width ∧
      Q.size store saved ≤ width ∧ Q.size bd.head (R.machine.head state) ≤ width)
    (hreply : ∀ n state saved, inv (n + 1) (state, saved) → ∀ i next,
      R.machine.view state = .inr ⟨i, next⟩ → ∀ p ∈ support ((H i).run saved),
        Q.size bd.idx ⟨i, p.1.value⟩ ≤ width)
    (input : A × S) (hi : inv fuel (R.machine.init input.1, input.2))
    (hin : Q.size bd.input input.1 ≤ width)
    (hcaller : GeneralCaller.Budget R contract kind fuel input.1 localTime queries)
    (z : Run (Option B × S))
    (hz : z ∈ support ((program R store handler fuel).run control queryCost input)) :
    post z.value.2 ∧ z.steps ≤ localTime + (∑ k, queries k * price k) +
      3 * overhead (32 * width) + (fuel + 1) * (42 * overhead (32 * width) + tickTime) := by
  have hstop' : ∀ state saved, inv 0 (state, saved) →
      stopWork R store control (state, saved) ≤ Q.cost R.headCode state + 42 * overhead (32 * width) := by
    intro state saved hi
    obtain ⟨hst, hstore, hhead⟩ := hwidth 0 state saved hi
    have h := stopWork_of_width R store sizes localLaws dispatchLaws mono control controlLaws
      state saved width hh hst hstore hhead
    omega
  have hreturn' : ∀ n state saved, inv (n + 1) (state, saved) → ∀ output,
      R.machine.view state = .inl output → returnWork R store control (state, saved) output ≤
        Q.cost R.headCode state + 42 * overhead (32 * width) := by
    intro n state saved hi output hv
    obtain ⟨hst, hstore, hhead⟩ := hwidth (n + 1) state saved hi
    have h := returnWork_of_width R store sizes localLaws dispatchLaws mono control controlLaws
      state saved output hv width hh hst hstore hhead
    omega
  have hquery' : ∀ n state saved, inv (n + 1) (state, saved) → ∀ i next,
      R.machine.view state = .inr ⟨i, next⟩ → ∀ p ∈ support ((H i).run saved),
        queryWork R store control (state, saved) i p.1.value p.2 ≤
          Q.cost R.headCode state + Q.cost R.updateCode (state, ⟨i, p.1.value⟩) +
            42 * overhead (32 * width) := by
    intro n state saved hi i next hv p hp
    obtain ⟨hst, hstore, hhead⟩ := hwidth (n + 1) state saved hi
    obtain ⟨hn, hw, _⟩ := hwidth n _ _ (hstep n state saved hi i next hv p hp).1
    exact queryWork_of_width R store sizes localLaws dispatchLaws mono control controlLaws
      state saved p.2 i next p.1.value hv width hh hst hstore hhead hn hw
        (hreply n state saved hi i next hv p hp)
  obtain ⟨hstate, hstore, _⟩ := hwidth fuel _ _ hi
  have hinit := initWork_of_width R store sizes mono control controlLaws input width hh hstore hstate hin
  exact assembled_bound_indexed R store control queryCost handler H hhandler contract kind price
    inv post (42 * overhead (32 * width)) tickTime hstep hpost hstop' hreturn' hquery' htick fuel
    (3 * overhead (32 * width)) localTime queries input hi hinit hcaller z hz

omit hstop hreturn hquery in
/-- The indexed resource proof constructs an executable in the same hardness
class as the caller. Its description includes the caller's actual local code,
the actual handler code, and the derived generic wiring allowance. -/
theorem assembled_within_indexed_of_width
    (backend : Backend.{v, w, x} Q target iface control queryCost)
    (descriptions : DescriptionSize Q) (factor : Nat)
    (description : backend.DescriptionBound descriptions factor)
    (allowance : Nat) (descriptionLaws : LocalDescriptionLaws descriptions allowance)
    (dispatchDescriptions : DispatchDescriptionLaws (Q := Q) descriptions allowance)
    {header : Nat} (sizes : SizeLaws Q header) {overhead : Nat → Nat}
    (localLaws : LocalCostLaws Q overhead) (dispatchLaws : DispatchCostLaws (Q := Q) overhead)
    (mono : Monotone overhead) (controlLaws : RoutingCostLaws control overhead)
    (width fuel localTime inputSize : Nat) (queries : K → Nat) (hh : header ≤ width)
    (hinput : inputSize ≤ width)
    (hwidth : ∀ n state saved, inv n (state, saved) → Q.size R.state state ≤ width ∧
      Q.size store saved ≤ width ∧ Q.size bd.head (R.machine.head state) ≤ width)
    (hreply : ∀ n state saved, inv (n + 1) (state, saved) → ∀ i next,
      R.machine.view state = .inr ⟨i, next⟩ → ∀ p ∈ support ((H i).run saved),
        Q.size bd.idx ⟨i, p.1.value⟩ ≤ width)
    (sourceProgram : A → OracleComp source B) (hsource : R.machine.ImplementsWithin sourceProgram fuel)
    (hi : ∀ input, Q.size (StepClass.HasProd.prod bd.input store) input ≤ inputSize →
      inv fuel (R.machine.init input.1, input.2))
    (hcaller : ∀ input, Q.size (StepClass.HasProd.prod bd.input store) input ≤ inputSize →
      GeneralCaller.Budget R contract kind fuel input.1 localTime queries) :
    Within backend descriptions factor description (StepClass.HasProd.prod bd.input store) (result (bd := bd) store)
      inputSize (factor * (descriptions.localSize R.initCode + 2 * descriptions.localSize R.headCode +
        descriptions.localSize R.updateCode + handler.descriptionSize descriptions + fuel + 55 * allowance + 26))
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
      rw [program_denote R store handler (fun i => Run.value <$> H i) hsemantic]
      rw [hsource.simulateQ_run_eq])
    (by
      intro input hsize z hz
      have hin := (sizes.fst_le bd.input store input).trans (hsize.trans hinput)
      exact ⟨trivial, (assembled_bound_indexed_of_width R store control queryCost handler H hhandler
        contract kind price inv post tickTime hstep hpost htick sizes localLaws dispatchLaws mono controlLaws
        width fuel localTime queries hh hwidth hreply input (hi input hsize) hin (hcaller input hsize) z hz).2⟩)
  exact Within.mono backend descriptions factor description h (Nat.mul_le_mul_left factor
    (program_descriptionSize_bound R store descriptions allowance descriptionLaws dispatchDescriptions handler fuel)) le_rfl

end Signatures.Runtime.BackendProgram.Caller
