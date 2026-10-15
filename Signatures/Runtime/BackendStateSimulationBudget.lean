import Signatures.Runtime.BackendStateSimulationLoopBudget

/-! Total time and query-indexed store preservation for the actual state-passing
compiler. Its overhead is additive in source work, executed nodes and requests.
The source sampler is arbitrary backend code; only the handler is replaced. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.StateSimulation

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QD : Q.IsDistributive]
  {I J S : Type} {source : OracleSpec I} {target : OracleSpec J}
  {src : Interface (C := C) source} {dst : Interface (C := C) target}
  (store : C.Str S) (control : ControlCosts)
  (queryCost : (j : J) → target.Range j → Nat)
  (handler : Code Q target dst (StepClass.HasProd.prod src.position store)
    (StepClass.HasProd.prod src.response store))
  (inv : Nat → S → Prop) (cap width counter route query : Nat) (allowed : I → Prop)
  (charges : StructuralBound (Q := Q) store control width counter route)
  (hstore : ∀ used ≤ cap, ∀ saved, inv used saved → Q.size store saved ≤ width)
  (hquery : ∀ used < cap, ∀ i, allowed i → ∀ saved, inv used saved →
    ∀ z ∈ support (handler.run control queryCost (i, saved)),
      inv (used + 1) z.value.2 ∧ z.steps ≤ query)

include charges hstore hquery

theorem audit_bound {A B : Type} {a : C.Str A} {b : C.Str B}
    (program : Code Q source src a b) :
    AuditBound inv cap width counter route query allowed
      (audit store control queryCost handler program) := by
  induction program with
  | atomic code =>
      intro input r hr used hs hf hc
      simp only [audit, support_pure, Set.mem_singleton_iff] at hr
      subst r
      rw [auditFrame_fits] at hf
      change used ≤ cap at hc
      have hsz := hstore used hc input.2 hs
      have ht := charges.atomic code input.1 input.2 hf.2.1 hf.2.2.1 hsz
      constructor
      · simpa only [auditFrame, ExecutionProfile.frame, ExecutionProfile.Metrics.node,
          List.length_nil, Nat.add_zero] using hs
      · simpa only [auditFrame, ExecutionProfile.frame, ExecutionProfile.Metrics.node,
          ExecutionProfile.Metrics.price, List.length_nil, Nat.one_mul, Nat.zero_mul,
          Nat.add_zero, Nat.zero_add] using ht
  | query =>
      intro input r hr used hs hf hc
      simp only [audit, support_map, Set.mem_image] at hr
      obtain ⟨z, hz, rfl⟩ := hr
      rw [auditFrame_fits] at hf
      change used + 1 ≤ cap at hc
      have ha := hf.2.2.2.2.2.2 input.1 (by simp)
      obtain ⟨hout, ht⟩ := hquery used (by omega) input.1 ha input.2 hs z hz
      refine ⟨hout, ?_⟩
      change z.steps ≤ 0 + 1 * route + 1 * query
      omega
  | @seq A B D a b d first second ih1 ih2 =>
      intro input r hr used hs hf hc
      simp only [audit, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨mid, hmid, last, hlast, rfl⟩ := hr
      rw [auditFrame_fits, ExecutionProfile.Metrics.fits_join] at hf
      change used + (mid.2.requests ++ last.2.requests).length ≤ cap at hc
      rw [List.length_append] at hc
      have hc1 : used + mid.2.requests.length ≤ cap := by omega
      obtain ⟨hm, ht1⟩ := ih1 input mid hmid used hs hf.2.2.2.2.1 hc1
      obtain ⟨ho, ht2⟩ := ih2 mid.1.value last hlast (used + mid.2.requests.length) hm
        hf.2.2.2.2.2 (by omega)
      have hi := hstore used (by omega) input.2 hs
      have hs' := hstore _ hc1 mid.1.value.2 hm
      have hm' := (audit_sizes store control queryCost handler first input mid hmid).2.trans hf.2.2.2.2.1.1
      have hj := charges.sequence a b input mid.1.value hf.2.1 hi hm' hs'
      constructor
      · simpa only [auditFrame, ExecutionProfile.frame, ExecutionProfile.Metrics.node,
          ExecutionProfile.Metrics.join, List.length_append, Nat.add_assoc] using ho
      · simp only [auditFrame_price, ExecutionProfile.Metrics.price_join]
        change mid.1.steps + last.1.steps + control.sequence
          (Q.size (StepClass.HasProd.prod a store) input)
          (Q.size (StepClass.HasProd.prod b store) mid.1.value) ≤ _
        omega
  | @branch A B D a b d left right ih1 ih2 =>
      intro input r hr used hs hf hc
      rcases input with ⟨input, saved⟩
      cases input with
      | inl value =>
          simp only [audit, support_map, Set.mem_image] at hr
          obtain ⟨z, hz, rfl⟩ := hr
          rw [auditFrame_fits] at hf
          change used + z.2.requests.length ≤ cap at hc
          obtain ⟨ho, ht⟩ := ih1 (value, saved) z hz used hs hf.2.2.2.2 hc
          have hi := hstore used (by omega) saved hs
          have hb := charges.branch a b (.inl value) saved hf.2.1 hi
          refine ⟨ho, ?_⟩
          simp only [auditFrame_price]
          change z.1.steps + branchWork (Q := Q) store control a b (.inl value) saved ≤ _
          omega
      | inr value =>
          simp only [audit, support_map, Set.mem_image] at hr
          obtain ⟨z, hz, rfl⟩ := hr
          rw [auditFrame_fits] at hf
          change used + z.2.requests.length ≤ cap at hc
          obtain ⟨ho, ht⟩ := ih2 (value, saved) z hz used hs hf.2.2.2.2 hc
          have hi := hstore used (by omega) saved hs
          have hb := charges.branch a b (.inr value) saved hf.2.1 hi
          refine ⟨ho, ?_⟩
          simp only [auditFrame_price]
          change z.1.steps + branchWork (Q := Q) store control a b (.inr value) saved ≤ _
          omega
  | @first A B T a b retained body ih =>
      intro input r hr used hs hf hc
      simp only [audit, support_map, Set.mem_image] at hr
      obtain ⟨z, hz, rfl⟩ := hr
      rw [auditFrame_fits] at hf
      change used + z.2.requests.length ≤ cap at hc
      obtain ⟨ho, ht⟩ := ih (input.1.1, input.2) z hz used hs hf.2.2.2.2 hc
      obtain ⟨hin, hout⟩ := audit_sizes store control queryCost handler body (input.1.1, input.2) z hz
      have hi := hstore used (by omega) input.2 hs
      have hs' := hstore _ hc z.1.value.2 ho
      have hb := charges.first a b retained input.1 input.2 z.1.value
        (hin.trans hf.2.2.2.2.1) hf.1 hi (hout.trans hf.2.2.2.2.1) hs'
      refine ⟨ho, ?_⟩
      simp only [auditFrame_price]
      change z.1.steps + firstWork (Q := Q) store control a b retained input.1 input.2 z.1.value ≤ _
      omega
  | loop body stop fuel ih1 ih2 =>
      exact auditLoop_bound store control inv cap width counter route query allowed charges hstore
        _ _ _ _ (audit_sizes store control queryCost handler body) ih1 ih2 fuel
  | @iterate A a n body ih =>
      intro input r hr used hs hf hc
      simp only [audit, support_map, Set.mem_image] at hr
      obtain ⟨z, hz, rfl⟩ := hr
      rw [auditFrame_fits] at hf
      change used + z.2.requests.length ≤ cap at hc
      obtain ⟨ho, ht⟩ := auditIteration_bound store control inv cap width counter route query allowed charges hstore
        a n _ ih input.1.1 (input.1.2, input.2) z hz used hs hf.2.2.2.2 hc
      obtain ⟨hin, _, hn⟩ := auditIteration_sizes store control a n
        (audit store control queryCost handler body) input.1.1 (input.1.2, input.2) z hz
      have hi := hstore used (by omega) input.2 hs
      have hb := charges.iteration a n input (hn.trans hf.2.2.2.2.1) (hin.trans hf.2.2.2.2.1) hi
      refine ⟨ho, ?_⟩
      simp only [auditFrame_price]
      change z.1.steps + iterationWork (Q := Q) store control a n input ≤ _
      omega

/-- The actual compiled run consumes at most the source query allowance and
adds at most one routing charge per source visit and one handler charge per
source query. Only the original program's measured resources are supplied. -/
theorem native_bound
    (H : QueryImpl source (StateT S (OracleComp target)))
    (hhandler : ∀ i saved, handler.denote (i, saved) =
      (fun p => (Sigma.mk i p.1, p.2)) <$> (H i).run saved)
    {A B : Type} {a : C.Str A} {b : C.Str B} (program : Code Q source src a b)
    (input : A) (work visits queries : Nat)
    (hsource : ExecutionProfile.Within program input work visits queries width counter allowed)
    (used : Nat) (saved : S) (hs : inv used saved) (reserve : used + queries ≤ cap)
    (z : Run (B × S))
    (hz : z ∈ support ((compile store handler program).run control queryCost (input, saved))) :
    ∃ consumed ≤ queries, inv (used + consumed) z.value.2 ∧ Q.size b z.value.1 ≤ width ∧
      z.steps ≤ work + visits * route + queries * query := by
  obtain ⟨metrics, ha, hw, hv, hq, hf, _, hout⟩ :=
    native_resources store control queryCost handler H hhandler program input
      work visits queries width counter allowed hsource saved z hz
  obtain ⟨hi, ht⟩ := audit_bound store control queryCost handler inv cap width counter route query
    allowed charges hstore hquery program (input, saved) (z, metrics) ha used hs hf
      (by change used + metrics.requests.length ≤ cap; omega)
  refine ⟨metrics.requests.length, hq, hi, hout, ht.trans ?_⟩
  exact Nat.add_le_add (Nat.add_le_add hw (Nat.mul_le_mul_right route hv))
    (Nat.mul_le_mul_right query hq)

end Signatures.Runtime.BackendProgram.StateSimulation
