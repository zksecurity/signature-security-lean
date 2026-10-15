import Signatures.Runtime.BackendStateSimulationAccounting

/-! Sequential resource composition for both loop forms, including exhausted
stop code and a store invariant that advances by actual query counts. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.StateSimulation

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QD : Q.IsDistributive]
  {I J S : Type} {target : OracleSpec J}
  (store : C.Str S) (control : ControlCosts)
  (inv : Nat → S → Prop) (cap width counter route query : Nat) (allowed : I → Prop)
  (charges : StructuralBound (Q := Q) store control width counter route)
  (hstore : ∀ used ≤ cap, ∀ saved, inv used saved → Q.size store saved ≤ width)

include charges hstore

theorem auditLoop_bound {A B : Type} (a : C.Str A) (b : C.Str B)
    (body : A × S → OracleComp target (Audit I (B ⊕ A) S))
    (stop : A × S → OracleComp target (Audit I B S))
    (bodySize : ∀ input z, z ∈ support (body input) →
      Q.size a input.1 ≤ z.2.width ∧ Q.size (StepClass.HasSum.sum b a) z.1.value.1 ≤ z.2.width)
    (bodyBound : AuditBound inv cap width counter route query allowed body)
    (stopBound : AuditBound inv cap width counter route query allowed stop) (fuel : Nat) :
    AuditBound inv cap width counter route query allowed
      (auditLoop (Q := Q) store control a b body stop fuel) := by
  induction fuel with
  | zero =>
      intro input r hr used hs hf hc
      simp only [auditLoop, support_map, Set.mem_image] at hr
      obtain ⟨z, hz, rfl⟩ := hr
      rw [auditFrame_fits] at hf
      change used + z.2.requests.length ≤ cap at hc
      obtain ⟨hout, ht⟩ := stopBound input z hz used hs hf.2.2.2.2 hc
      have hsz := hstore used (by omega) input.2 hs
      have htick := charges.loopStop a input hf.2.1 hsz
      refine ⟨hout, ?_⟩
      simp only [auditFrame_price]
      change z.1.steps + control.loop 0 (Q.size (StepClass.HasProd.prod a store) input) ≤ _
      omega
  | succ fuel ih =>
      intro input r hr used hs hf hc
      simp only [auditLoop, mem_support_bind_iff] at hr
      obtain ⟨z, hz, hr⟩ := hr
      cases he : z.1.value.1 with
      | inl output =>
          simp only [he, support_pure, Set.mem_singleton_iff] at hr
          subst r
          rw [auditFrame_fits] at hf
          change used + z.2.requests.length ≤ cap at hc
          obtain ⟨hout, ht⟩ := bodyBound input z hz used hs hf.2.2.2.2 hc
          have hi := hstore used (by omega) input.2 hs
          have ho := hstore _ hc z.1.value.2 hout
          have hb := (bodySize input z hz).2.trans hf.2.2.2.2.1
          have hfee := charges.loopStep a b input z.1.value (fuel + 1) hf.2.1 hi hb ho hf.2.2.2.1
          refine ⟨hout, ?_⟩
          simp only [auditFrame_price]
          change z.1.steps + (loopBodyWork (Q := Q) store control a b input z.1.value +
            control.loop (fuel + 1) (Q.size (StepClass.HasProd.prod a store) input)) ≤ _
          omega
      | inr next =>
          simp only [he, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
          obtain ⟨rest, hrest, rfl⟩ := hr
          rw [auditFrame_fits, ExecutionProfile.Metrics.fits_join] at hf
          change used + (z.2.requests ++ rest.2.requests).length ≤ cap at hc
          rw [List.length_append] at hc
          have hc1 : used + z.2.requests.length ≤ cap := by omega
          obtain ⟨hmid, ht1⟩ := bodyBound input z hz used hs hf.2.2.2.2.1 hc1
          obtain ⟨hout, ht2⟩ := ih (next, z.1.value.2) rest hrest
            (used + z.2.requests.length) hmid hf.2.2.2.2.2 (by omega)
          have hi := hstore used (by omega) input.2 hs
          have ho := hstore _ hc1 z.1.value.2 hmid
          have hb := (bodySize input z hz).2.trans hf.2.2.2.2.1.1
          have hfee := charges.loopStep a b input z.1.value (fuel + 1) hf.2.1 hi hb ho hf.2.2.2.1
          constructor
          · simpa only [auditFrame, ExecutionProfile.frame, ExecutionProfile.Metrics.node,
              ExecutionProfile.Metrics.join, List.length_append, Nat.add_assoc] using hout
          · simp only [auditFrame_price, ExecutionProfile.Metrics.price_join]
            change z.1.steps + rest.1.steps + (loopBodyWork (Q := Q) store control a b input z.1.value +
              control.loop (fuel + 1) (Q.size (StepClass.HasProd.prod a store) input)) ≤ _
            omega

theorem auditIteration_bound {A : Type} (a : C.Str A) (n : C.Str Nat)
    (body : A × S → OracleComp target (Audit I A S))
    (bodyBound : AuditBound inv cap width counter route query allowed body) (count : Nat) :
    AuditBound inv cap width counter route query allowed
      (auditIteration (Q := Q) store control a n body count) := by
  induction count with
  | zero =>
      intro input r hr used hs hf hc
      simp only [auditIteration, support_pure, Set.mem_singleton_iff] at hr
      subst r
      rw [auditFrame_fits] at hf
      change used ≤ cap at hc
      have hi := hstore used hc input.2 hs
      have htick := charges.iterationTick a n 0 input hf.1 hf.2.1 hi hf.2.2.2.1
      constructor
      · simpa [auditFrame, ExecutionProfile.frame, ExecutionProfile.Metrics.node] using hs
      · simpa only [auditFrame, ExecutionProfile.frame, ExecutionProfile.Metrics.node,
          ExecutionProfile.Metrics.price, List.length_nil, Nat.one_mul, Nat.zero_mul,
          Nat.add_zero, Nat.zero_add] using htick
  | succ count ih =>
      intro input r hr used hs hf hc
      simp only [auditIteration, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨step, hstep, rest, hrest, rfl⟩ := hr
      rw [auditFrame_fits, ExecutionProfile.Metrics.fits_join] at hf
      change used + (step.2.requests ++ rest.2.requests).length ≤ cap at hc
      rw [List.length_append] at hc
      obtain ⟨hmid, ht1⟩ := bodyBound input step hstep used hs hf.2.2.2.2.1 (by omega)
      obtain ⟨hout, ht2⟩ := ih step.1.value rest hrest (used + step.2.requests.length)
        hmid hf.2.2.2.2.2 (by omega)
      have hi := hstore used (by omega) input.2 hs
      have htick := charges.iterationTick a n (count + 1) input hf.1 hf.2.1 hi hf.2.2.2.1
      constructor
      · simpa only [auditFrame, ExecutionProfile.frame, ExecutionProfile.Metrics.node,
          ExecutionProfile.Metrics.join, List.length_append, Nat.add_assoc] using hout
      · simp only [auditFrame_price, ExecutionProfile.Metrics.price_join]
        change step.1.steps + rest.1.steps + control.loop (count + 1)
          (Q.size (StepClass.HasProd.prod n (StepClass.HasProd.prod a store)) (count + 1, input)) ≤ _
        omega

end Signatures.Runtime.BackendProgram.StateSimulation
