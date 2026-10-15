import Signatures.Runtime.BackendExecutionProfileBounds
import Signatures.Runtime.BackendBudget
import Signatures.Runtime.BackendCallerRouting
import Signatures.Runtime.PolynomialResources

/-! Recover actual untransformed execution time from the original profile.
The same profile can therefore price both ordinary sampling and private-tape
sampling, without assuming a finished sampler runtime certificate. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.ExecutionProfile

def runtimeBound (overhead : Nat → Nat) (width work visits queries tickTime queryTime : Nat) : Nat :=
  work + visits * (overhead (3 * width) + tickTime) + queries * queryTime

theorem runtimeBound_polynomial (overhead : Nat → Nat → Nat)
    (width work visits queries tickTime queryTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hWork : PolynomiallyBounded work) (hVisits : PolynomiallyBounded visits)
    (hQueries : PolynomiallyBounded queries) (hTick : PolynomiallyBounded tickTime)
    (hQuery : PolynomiallyBounded queryTime) :
    PolynomiallyBounded (fun n => runtimeBound (overhead n) (width n) (work n) (visits n)
      (queries n) (tickTime n) (queryTime n)) := by
  unfold runtimeBound
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {I : Type} {spec : OracleSpec I} {iface : Interface (C := C) spec}
  (control : ControlCosts) (queryCost : (i : I) → spec.Range i → Nat)
  {header : Nat} (sizes : SizeLaws Q header)
  (width counter route query : Nat) (allowed : I → Prop)

private def Witness {A B : Type} (execute : A → OracleComp spec (Run B))
    (profile : A → OracleComp spec (Result I B)) : Prop :=
  ∀ input z, z ∈ support (execute input) → ∃ metrics,
    (z.value, metrics) ∈ support (profile input) ∧
      (metrics.Fits width counter allowed → z.steps ≤ metrics.price route query)

variable (hh : header ≤ width)
  (hlocal : ∀ x ≤ width, ∀ y ≤ width, control.localCall x y ≤ route)
  (hseq : ∀ x ≤ width, ∀ y ≤ width, control.sequence x y ≤ route)
  (hbranch : ∀ x ≤ width, control.branch x ≤ route)
  (hretain : ∀ x ≤ width, ∀ y ≤ width, control.retain x y ≤ route)
  (htick : ∀ n ≤ counter, ∀ x ≤ 3 * width, control.loop n x ≤ route)
  (hquery : ∀ i, allowed i → ∀ reply,
    queryCost i reply + control.query (Q.size iface.position i) (Q.size iface.response ⟨i, reply⟩) ≤ query)

include htick

omit [C.HasProd] [C.HasSum] [C.HasOption] in
private theorem loop_witness {A B : Type} (a : C.Str A) (b : C.Str B)
    (body : A → OracleComp spec (Run (B ⊕ A))) (stop : A → OracleComp spec (Run B))
    (bodyProfile : A → OracleComp spec (Result I (B ⊕ A))) (stopProfile : A → OracleComp spec (Result I B))
    (hb : Witness width counter route query allowed body bodyProfile)
    (hs : Witness width counter route query allowed stop stopProfile) (fuel : Nat) :
    Witness width counter route query allowed
      (loopRun (fun n x => control.loop n (Q.size a x)) body stop fuel)
      (loop (Q := Q) a b bodyProfile stopProfile fuel) := by
  induction fuel with
  | zero =>
      intro input z hz
      simp only [loopRun, chargeRun, support_map, Set.mem_image] at hz
      obtain ⟨r, hr, rfl⟩ := hz
      obtain ⟨metrics, hm, ht⟩ := hs input r hr
      refine ⟨(frame (Q := Q) a b input (r.value, metrics) 0 0).2, ?_, ?_⟩
      · simp only [loop, support_map, Set.mem_image]
        exact ⟨(r.value, metrics), hm, rfl⟩
      · intro hf
        change (frame (Q := Q) a b input (r.value, metrics) 0 0).2.Fits width counter allowed at hf
        rw [frame_fits] at hf
        have hcost := ht hf.2.2.2.2
        have hfee := htick 0 (by omega) (Q.size a input) (by omega)
        simp only [frame, Metrics.price_node]
        change r.steps + control.loop 0 (Q.size a input) ≤ metrics.price route query + route
        omega
  | succ fuel ih =>
      intro input z hz
      simp only [loopRun, mem_support_bind_iff] at hz
      obtain ⟨step, hs', hz⟩ := hz
      obtain ⟨m1, hm1, ht1⟩ := hb input step hs'
      cases he : step.value with
      | inl output =>
          simp only [he, support_pure, Set.mem_singleton_iff] at hz
          subst z
          refine ⟨(frame (Q := Q) a b input (output, m1) 0 (fuel + 1)).2, ?_, ?_⟩
          · simp only [loop, mem_support_bind_iff]
            refine ⟨(step.value, m1), hm1, ?_⟩
            simp only [he, support_pure, Set.mem_singleton_iff]
            rfl
          · intro hf
            change (frame (Q := Q) a b input (output, m1) 0 (fuel + 1)).2.Fits width counter allowed at hf
            rw [frame_fits] at hf
            have hcost := ht1 hf.2.2.2.2
            have hfee := htick (fuel + 1) hf.2.2.2.1 (Q.size a input) (by omega)
            simp only [frame, Metrics.price_node]
            change step.steps + control.loop (fuel + 1) (Q.size a input) ≤ m1.price route query + route
            omega
      | inr next =>
          simp only [he, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
          obtain ⟨rest, hr, rfl⟩ := hz
          obtain ⟨m2, hm2, ht2⟩ := ih next rest hr
          refine ⟨(frame (Q := Q) a b input (rest.value, m1.join m2) 0 (fuel + 1)).2, ?_, ?_⟩
          · simp only [loop, mem_support_bind_iff]
            refine ⟨(step.value, m1), hm1, ?_⟩
            simp only [he, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
            exact ⟨(rest.value, m2), hm2, rfl⟩
          · intro hf
            change (frame (Q := Q) a b input (rest.value, m1.join m2) 0 (fuel + 1)).2.Fits width counter allowed at hf
            rw [frame_fits, Metrics.fits_join] at hf
            have hcost1 := ht1 hf.2.2.2.2.1
            have hcost2 := ht2 hf.2.2.2.2.2
            have hfee := htick (fuel + 1) hf.2.2.2.1 (Q.size a input) (by omega)
            simp only [frame, Metrics.price_node]
            change step.steps + rest.steps + control.loop (fuel + 1) (Q.size a input) ≤
              (m1.join m2).price route query + route
            rw [Metrics.price_join]
            omega

include sizes hh in
private theorem iteration_witness {A : Type} (a : C.Str A) (n : C.Str Nat)
    (body : A → OracleComp spec (Run A)) (profile : A → OracleComp spec (Result I A))
    (hb : Witness width counter route query allowed body profile) (count : Nat) :
    Witness width counter route query allowed
      (iterationRun (fun count x => control.loop count (Q.size (StepClass.HasProd.prod n a) (count, x))) body count)
      (iteration (Q := Q) a n profile count) := by
  induction count with
  | zero =>
      intro input z hz
      simp only [iterationRun, support_pure, Set.mem_singleton_iff] at hz
      subst z
      refine ⟨(frame (Q := Q) a a input (input, {}) (Q.size n 0) 0).2, ?_, ?_⟩
      · simp only [iteration, support_pure, Set.mem_singleton_iff]; rfl
      · intro hf
        change (frame (Q := Q) a a input (input, {}) (Q.size n 0) 0).2.Fits width counter allowed at hf
        rw [frame_fits] at hf
        have hp := sizes.prod_le n a (0, input)
        have ht := htick 0 (by omega) (Q.size (StepClass.HasProd.prod n a) (0, input)) (by dsimp only at hp; omega)
        simpa [frame, Metrics.price, Metrics.node] using ht
  | succ count ih =>
      intro input z hz
      simp only [iterationRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨step, hs, rest, hr, rfl⟩ := hz
      obtain ⟨m1, hm1, ht1⟩ := hb input step hs
      obtain ⟨m2, hm2, ht2⟩ := ih step.value rest hr
      refine ⟨(frame (Q := Q) a a input (rest.value, m1.join m2) (Q.size n (count + 1)) (count + 1)).2, ?_, ?_⟩
      · simp only [iteration, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
        exact ⟨(step.value, m1), hm1, (rest.value, m2), hm2, rfl⟩
      · intro hf
        change (frame (Q := Q) a a input (rest.value, m1.join m2)
          (Q.size n (count + 1)) (count + 1)).2.Fits width counter allowed at hf
        rw [frame_fits, Metrics.fits_join] at hf
        have hcost1 := ht1 hf.2.2.2.2.1
        have hcost2 := ht2 hf.2.2.2.2.2
        have hp := sizes.prod_le n a (count + 1, input)
        have hfee := htick (count + 1) hf.2.2.2.1 (Q.size (StepClass.HasProd.prod n a) (count + 1, input)) (by dsimp only at hp; omega)
        simp only [frame, Metrics.price_node]
        change step.steps + rest.steps + control.loop (count + 1) (Q.size (StepClass.HasProd.prod n a) (count + 1, input)) ≤
          (m1.join m2).price route query + route
        rw [Metrics.price_join]
        omega

include sizes hh hlocal hseq hbranch hretain hquery

private theorem run_witness {A B : Type} {a : C.Str A} {b : C.Str B} (program : Code Q spec iface a b) :
    Witness width counter route query allowed (program.run control queryCost) (run program) := by
  induction program with
  | @atomic A B a b f code =>
      intro input z hz
      simp only [Code.run, support_pure, Set.mem_singleton_iff] at hz
      subst z
      refine ⟨(frame (Q := Q) a b input (f input, {work := Q.cost code input})).2, ?_, ?_⟩
      · simp only [run, support_pure, Set.mem_singleton_iff]; rfl
      · intro hf
        rw [frame_fits] at hf
        have ht := hlocal _ hf.2.1 _ hf.2.2.1
        simpa [frame, Metrics.node, Metrics.price] using Nat.add_le_add_left ht (Q.cost code input)
  | query =>
      intro input z hz
      simp only [Code.run, support_map, Set.mem_image] at hz
      obtain ⟨reply, hr, rfl⟩ := hz
      refine ⟨(frame (Q := Q) iface.position iface.response input (⟨input, reply⟩, {requests := [input]})).2, ?_, ?_⟩
      · simp only [run, support_map, Set.mem_image]
        exact ⟨reply, hr, rfl⟩
      · intro hf
        rw [frame_fits] at hf
        have ht := hquery input (hf.2.2.2.2.2.2 input (by simp)) reply
        change queryCost input reply + control.query _ _ ≤ 0 + 1 * route + 1 * query
        omega
  | @seq A B D a b d first second ih1 ih2 =>
      intro input z hz
      simp only [Code.run, sequenceRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨r1, hr1, r2, hr2, rfl⟩ := hz
      obtain ⟨m1, hm1, ht1⟩ := ih1 input r1 hr1
      obtain ⟨m2, hm2, ht2⟩ := ih2 r1.value r2 hr2
      refine ⟨(frame (Q := Q) a d input (r2.value, m1.join m2)).2, ?_, ?_⟩
      · simp only [run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
        exact ⟨(r1.value, m1), hm1, (r2.value, m2), hm2, rfl⟩
      · intro hf
        rw [frame_fits, Metrics.fits_join] at hf
        have h1 := ht1 hf.2.2.2.2.1
        have h2 := ht2 hf.2.2.2.2.2
        have hmid := (run_sizes first input (r1.value, m1) hm1).2.trans hf.2.2.2.2.1.1
        dsimp only at hmid
        have ht := hseq _ hf.2.1 _ hmid
        simp only [frame, Metrics.price_node]
        change r1.steps + r2.steps + control.sequence _ _ ≤ (m1.join m2).price route query + route
        rw [Metrics.price_join]
        omega
  | @branch A B D a b d left right ih1 ih2 =>
      intro input z hz
      cases input with
      | inl x =>
          simp only [Code.run, chargeRun, support_map, Set.mem_image] at hz
          obtain ⟨r, hr, rfl⟩ := hz
          obtain ⟨m, hm, ht⟩ := ih1 x r hr
          refine ⟨(frame (Q := Q) (StepClass.HasSum.sum a b) d (Sum.inl x) (r.value, m)).2, ?_, ?_⟩
          · simp only [run, support_map, Set.mem_image]; exact ⟨(r.value, m), hm, rfl⟩
          · intro hf
            rw [frame_fits] at hf
            have hb := hbranch _ hf.2.1
            have ht' := ht hf.2.2.2.2
            simp only [frame, Metrics.price_node]
            change r.steps + control.branch _ ≤ m.price route query + route
            omega
      | inr x =>
          simp only [Code.run, chargeRun, support_map, Set.mem_image] at hz
          obtain ⟨r, hr, rfl⟩ := hz
          obtain ⟨m, hm, ht⟩ := ih2 x r hr
          refine ⟨(frame (Q := Q) (StepClass.HasSum.sum a b) d (Sum.inr x) (r.value, m)).2, ?_, ?_⟩
          · simp only [run, support_map, Set.mem_image]; exact ⟨(r.value, m), hm, rfl⟩
          · intro hf
            rw [frame_fits] at hf
            have hb := hbranch _ hf.2.1
            have ht' := ht hf.2.2.2.2
            simp only [frame, Metrics.price_node]
            change r.steps + control.branch _ ≤ m.price route query + route
            omega
  | @first A B S a b saved body ih =>
      intro input z hz
      simp only [Code.run, retainRun, support_map, Set.mem_image] at hz
      obtain ⟨r, hr, rfl⟩ := hz
      obtain ⟨m, hm, ht⟩ := ih input.1 r hr
      refine ⟨(frame (Q := Q) (StepClass.HasProd.prod a saved) (StepClass.HasProd.prod b saved) input ((r.value, input.2), m) (Q.size saved input.2)).2, ?_, ?_⟩
      · simp only [run, support_map, Set.mem_image]; exact ⟨(r.value, m), hm, rfl⟩
      · intro hf
        rw [frame_fits] at hf
        have ho := (run_sizes body input.1 (r.value, m) hm).2.trans hf.2.2.2.2.1
        dsimp only at ho
        have hcost := ht hf.2.2.2.2
        have hfee := hretain _ hf.1 _ ho
        simp only [frame, Metrics.price_node]
        change r.steps + control.retain _ _ ≤ m.price route query + route
        omega
  | loop body stop fuel hb hs =>
      exact loop_witness control width counter route query allowed htick _ _ _ _ _ _ hb hs fuel
  | @iterate S s n body ih =>
      intro input z hz
      have hi := iteration_witness control sizes width counter route query allowed hh htick s n
        (body.run control queryCost) (run body) ih input.1
      obtain ⟨m, hm, ht⟩ := hi input.2 z hz
      refine ⟨(frame (Q := Q) (StepClass.HasProd.prod n s) s input (z.value, m)).2, ?_, ?_⟩
      · simp only [run, support_map, Set.mem_image]; exact ⟨(z.value, m), hm, rfl⟩
      · intro hf
        rw [frame_fits] at hf
        have hcost := ht hf.2.2.2.2
        simp only [frame, Metrics.price_node]
        change z.steps ≤ m.price route query + route
        omega

omit hlocal hseq hbranch hretain htick hquery route query in
theorem within_bound {overhead : Nat → Nat} (mono : Monotone overhead)
    (routing : RoutingCostLaws control overhead)
    (tickTime queryTime : Nat)
    (tick : ∀ n ≤ counter, ∀ x ≤ 3 * width, control.loop n x ≤ tickTime)
    (queryBound : ∀ i, allowed i → ∀ reply,
      queryCost i reply + control.query (Q.size iface.position i) (Q.size iface.response ⟨i, reply⟩) ≤ queryTime)
    {A B : Type} {a : C.Str A} {b : C.Str B} (program : Code Q spec iface a b) (pre : A → Prop)
    (work visits queries : Nat)
    (profile : ∀ input, pre input → Within program input work visits queries width counter allowed) :
    Bounds control queryCost program pre (fun output => Q.size b output ≤ width)
      (runtimeBound overhead width work visits queries tickTime queryTime) := by
  have fee : ∀ n ≤ 3 * width, overhead n ≤ overhead (3 * width) := fun _ hn => mono hn
  have h := run_witness control queryCost sizes width counter (overhead (3 * width) + tickTime) queryTime
    allowed hh
    (by intro x hx y hy; exact (routing.localCall x y).trans ((fee _ (by omega)).trans (Nat.le_add_right _ _)))
    (by intro x hx y hy; exact (routing.sequence x y).trans ((fee _ (by omega)).trans (Nat.le_add_right _ _)))
    (by intro x hx; exact (routing.branch x).trans ((fee _ (by omega)).trans (Nat.le_add_right _ _)))
    (by intro x hx y hy; exact (routing.retain x y).trans ((fee _ (by omega)).trans (Nat.le_add_right _ _)))
    (fun n hn x hx => (tick n hn x hx).trans (Nat.le_add_left _ _)) queryBound program
  intro input hi z hz
  obtain ⟨m, hm, ht⟩ := h input z hz
  have hp := profile input hi (z.value, m) hm
  exact ⟨(run_sizes program input (z.value, m) hm).2.trans hp.2.2.2.1,
    (ht hp.2.2.2).trans (Within.price program input work visits queries width counter allowed
      (profile input hi) (overhead (3 * width) + tickTime) queryTime (z.value, m) hm)⟩

end Signatures.Runtime.BackendProgram.ExecutionProfile
