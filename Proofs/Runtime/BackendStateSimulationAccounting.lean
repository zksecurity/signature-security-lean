import Proofs.Runtime.BackendStateSimulationResources
import Proofs.Runtime.BackendStateSimulationRouting

/-! Whole-execution accounting for the state-passing compiler. The store
invariant is indexed by queries already consumed, so it can describe growing
finite tapes rather than requiring closure under arbitrarily many requests. -/

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

omit [C.HasProd] [C.HasSum] [Q.HasCategory] QP QD in
@[simp] theorem auditFrame_fits {A B : Type} (a : C.Str A) (b : C.Str B) (input : A)
    (r : Run (B × S)) (metrics : ExecutionProfile.Metrics I)
    (extra count width counter : Nat) (allowed : I → Prop) :
    (auditFrame (Q := Q) a b input r metrics extra count).2.Fits width counter allowed ↔
      extra ≤ width ∧ Q.size a input ≤ width ∧ Q.size b r.value.1 ≤ width ∧
        count ≤ counter ∧ metrics.Fits width counter allowed :=
  ExecutionProfile.frame_fits a b input (r.value.1, metrics) extra count width counter allowed

omit [C.HasProd] [C.HasSum] [Q.HasCategory] QP QD in
@[simp] theorem auditFrame_price {A B : Type} (a : C.Str A) (b : C.Str B) (input : A)
    (r : Run (B × S)) (metrics : ExecutionProfile.Metrics I)
    (extra count route query : Nat) :
    (auditFrame (Q := Q) a b input r metrics extra count).2.price route query =
      metrics.price route query + route := by
  exact ExecutionProfile.Metrics.price_node metrics _ _ route query

omit [Q.HasCategory] QP in
theorem auditLoop_sizes {A B : Type} (a : C.Str A) (b : C.Str B)
    (body : A × S → OracleComp target (Audit I (B ⊕ A) S))
    (stop : A × S → OracleComp target (Audit I B S)) (fuel : Nat) (input : A × S)
    (r : Audit I B S) (hr : r ∈ support (auditLoop (Q := Q) store control a b body stop fuel input)) :
    Q.size a input.1 ≤ r.2.width ∧ Q.size b r.1.value.1 ≤ r.2.width := by
  cases fuel with
  | zero =>
      simp only [auditLoop, support_map, Set.mem_image] at hr
      obtain ⟨z, _, rfl⟩ := hr
      exact ExecutionProfile.frame_sizes _ _ _ _ _ _
  | succ fuel =>
      simp only [auditLoop, mem_support_bind_iff] at hr
      obtain ⟨z, _, hr⟩ := hr
      cases h : z.1.value.1 with
      | inl output =>
          simp only [h, support_pure, Set.mem_singleton_iff] at hr
          subst r
          exact ExecutionProfile.frame_sizes _ _ _ _ _ _
      | inr next =>
          simp only [h, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
          obtain ⟨rest, _, rfl⟩ := hr
          exact ExecutionProfile.frame_sizes _ _ _ _ _ _

omit [Q.HasCategory] QP QD [C.HasSum] in
theorem auditIteration_sizes {A : Type} (a : C.Str A) (counter : C.Str Nat)
    (body : A × S → OracleComp target (Audit I A S)) (count : Nat) (input : A × S)
    (r : Audit I A S) (hr : r ∈ support (auditIteration (Q := Q) store control a counter body count input)) :
    Q.size a input.1 ≤ r.2.width ∧ Q.size a r.1.value.1 ≤ r.2.width ∧
      Q.size counter count ≤ r.2.width := by
  cases count with
  | zero =>
      simp only [auditIteration, support_pure, Set.mem_singleton_iff] at hr
      subst r
      dsimp only [auditFrame, ExecutionProfile.frame, ExecutionProfile.Metrics.node]
      omega
  | succ count =>
      simp only [auditIteration, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨step, _, rest, _, rfl⟩ := hr
      dsimp only [auditFrame, ExecutionProfile.frame, ExecutionProfile.Metrics.node]
      omega

theorem audit_sizes {A B : Type} {a : C.Str A} {b : C.Str B}
    (program : Code Q source src a b) (input : A × S) (r : Audit I B S)
    (hr : r ∈ support (audit store control queryCost handler program input)) :
    Q.size a input.1 ≤ r.2.width ∧ Q.size b r.1.value.1 ≤ r.2.width := by
  cases program with
  | atomic code =>
      simp only [audit, support_pure, Set.mem_singleton_iff] at hr
      subst r
      exact ExecutionProfile.frame_sizes _ _ _ _ _ _
  | query =>
      simp only [audit, support_map, Set.mem_image] at hr
      obtain ⟨reply, _, rfl⟩ := hr
      exact ExecutionProfile.frame_sizes _ _ _ _ _ _
  | seq initial following =>
      simp only [audit, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨first, _, second, _, rfl⟩ := hr
      exact ExecutionProfile.frame_sizes _ _ _ _ _ _
  | branch left right =>
      rcases input with ⟨input, saved⟩
      cases input <;> simp only [audit, support_map, Set.mem_image] at hr <;>
        obtain ⟨result, _, rfl⟩ := hr <;> exact ExecutionProfile.frame_sizes _ _ _ _ _ _
  | first retained body =>
      simp only [audit, support_map, Set.mem_image] at hr
      obtain ⟨result, _, rfl⟩ := hr
      exact ExecutionProfile.frame_sizes _ _ _ _ _ _
  | loop body stop fuel => exact auditLoop_sizes _ _ _ _ _ _ fuel input r hr
  | iterate counter body =>
      simp only [audit, support_map, Set.mem_image] at hr
      obtain ⟨result, _, rfl⟩ := hr
      exact ExecutionProfile.frame_sizes _ _ _ _ _ _

/-- A budget for a proof-only joint execution, conditional on the source
profile and on the remaining query allowance. -/
def AuditBound {A B : Type} (inv : Nat → S → Prop) (cap width counter route query : Nat)
    (allowed : I → Prop) (computation : A × S → OracleComp target (Audit I B S)) : Prop :=
  ∀ input r, r ∈ support (computation input) → ∀ used,
    inv used input.2 → r.2.Fits width counter allowed →
      used + r.2.requests.length ≤ cap →
        inv (used + r.2.requests.length) r.1.value.2 ∧ r.1.steps ≤ r.2.price route query

/-- Per-node structural charges. These contain no handler or whole-program
budget and are derived below from primitive and encoding laws. -/
structure StructuralBound (width counter route : Nat) : Prop where
  atomic : ∀ {A B : Type} {a : C.Str A} {b : C.Str B} {f : A → B}
    (code : Q.Realizer a b f) (input : A) (saved : S),
    Q.size a input ≤ width → Q.size b (f input) ≤ width → Q.size store saved ≤ width →
    localWork control code input + control.retain (Q.size store saved) (Q.size b (f input)) ≤
      Q.cost code input + route
  sequence : ∀ {A B : Type} (a : C.Str A) (b : C.Str B) (input : A × S) (output : B × S),
    Q.size a input.1 ≤ width → Q.size store input.2 ≤ width →
    Q.size b output.1 ≤ width → Q.size store output.2 ≤ width →
    control.sequence (Q.size (StepClass.HasProd.prod a store) input)
      (Q.size (StepClass.HasProd.prod b store) output) ≤ route
  branch : ∀ {A B : Type} (a : C.Str A) (b : C.Str B) (input : A ⊕ B) (saved : S),
    Q.size (StepClass.HasSum.sum a b) input ≤ width → Q.size store saved ≤ width →
      branchWork (Q := Q) store control a b input saved ≤ route
  first : ∀ {A B T : Type} (a : C.Str A) (b : C.Str B) (retained : C.Str T)
    (input : A × T) (saved : S) (output : B × S),
    Q.size a input.1 ≤ width → Q.size retained input.2 ≤ width → Q.size store saved ≤ width →
    Q.size b output.1 ≤ width → Q.size store output.2 ≤ width →
      firstWork (Q := Q) store control a b retained input saved output ≤ route
  loopStop : ∀ {A : Type} (a : C.Str A) (input : A × S),
    Q.size a input.1 ≤ width → Q.size store input.2 ≤ width →
      control.loop 0 (Q.size (StepClass.HasProd.prod a store) input) ≤ route
  loopStep : ∀ {A B : Type} (a : C.Str A) (b : C.Str B)
    (input : A × S) (output : (B ⊕ A) × S) (count : Nat),
    Q.size a input.1 ≤ width → Q.size store input.2 ≤ width →
    Q.size (StepClass.HasSum.sum b a) output.1 ≤ width → Q.size store output.2 ≤ width →
    count ≤ counter → loopBodyWork (Q := Q) store control a b input output +
      control.loop count (Q.size (StepClass.HasProd.prod a store) input) ≤ route
  iteration : ∀ {A : Type} (a : C.Str A) (n : C.Str Nat) (input : (Nat × A) × S),
    Q.size n input.1.1 ≤ width → Q.size a input.1.2 ≤ width → Q.size store input.2 ≤ width →
      iterationWork (Q := Q) store control a n input ≤ route
  iterationTick : ∀ {A : Type} (a : C.Str A) (n : C.Str Nat) (count : Nat) (input : A × S),
    Q.size n count ≤ width → Q.size a input.1 ≤ width → Q.size store input.2 ≤ width →
    count ≤ counter →
      control.loop count (Q.size (StepClass.HasProd.prod n (StepClass.HasProd.prod a store))
        (count, input)) ≤ route

def routeTime (overhead : Nat → Nat) (width tickTime : Nat) : Nat :=
  64 * overhead (64 * width) + tickTime

/-- All extra work at one executed source node, including loop tests, follows
from primitive contracts; no bound on compiled code occurs among the premises. -/
theorem structuralBound [C.HasOption] [QS : Q.HasSum]
    {header : Nat} (sizes : SizeLaws Q header) {overhead : Nat → Nat}
    (laws : LocalCostLaws Q overhead) (mono : Monotone overhead)
    (routing : RoutingCostLaws control overhead)
    (distribution : ∀ {A B T : Type} (a : C.Str A) (b : C.Str B) (t : C.Str T) (p : (A ⊕ B) × T),
      Q.cost (QD.distribute a b t) p ≤ overhead
        (Q.size (StepClass.HasProd.prod (StepClass.HasSum.sum a b) t) p +
          Q.size (StepClass.HasSum.sum (StepClass.HasProd.prod a t) (StepClass.HasProd.prod b t))
            (distributeValue p)))
    (width counter tickTime : Nat) (hh : header ≤ width)
    (tick : ∀ n ≤ counter, ∀ size ≤ 6 * width, control.loop n size ≤ tickTime) :
    StructuralBound (Q := Q) store control width counter (routeTime overhead width tickTime) := by
  constructor
  · intro A B a b f code input saved hi ho hs
    have h := atomic_work store control mono routing code input saved width hi ho hs
    unfold routeTime
    omega
  · intro A B a b input output hi hs ho ht
    have h := sequence_work store control sizes mono routing a b input output width hh hi hs ho ht
    unfold routeTime
    omega
  · intro A B a b input saved hi hs
    have h := branch_work store control sizes mono routing distribution a b input saved width hh hi hs
    unfold routeTime
    omega
  · intro A B T a b retained input saved output hi hk hs ho ht
    have h := first_work store control sizes laws mono routing a b retained input saved output width hh hi hk hs ho ht
    unfold routeTime
    omega
  · intro A a input hi hs
    have hp := sizes.prod_le a store input
    have h := tick 0 (by omega) _ (show Q.size (StepClass.HasProd.prod a store) input ≤ 6 * width by omega)
    unfold routeTime
    omega
  · intro A B a b input output count hi hs ho ht hn
    have h := loop_body_work store control sizes mono routing distribution a b input output width hh hi hs ho ht
    have hp := sizes.prod_le a store input
    have hk := tick count hn _ (show Q.size (StepClass.HasProd.prod a store) input ≤ 6 * width by omega)
    unfold routeTime
    omega
  · intro A a n input hn hi hs
    have h := iteration_work store control sizes laws mono routing a n input width hh hn hi hs
    unfold routeTime
    omega
  · intro A a n count input hn hi hs hc
    have hp := sizes.prod_le a store input
    have hnp := sizes.prod_le n (StepClass.HasProd.prod a store) (count, input)
    dsimp only at hnp
    have h := tick count hc _ (show Q.size (StepClass.HasProd.prod n (StepClass.HasProd.prod a store))
      (count, input) ≤ 6 * width by omega)
    unfold routeTime
    omega

end Signatures.Runtime.BackendProgram.StateSimulation
