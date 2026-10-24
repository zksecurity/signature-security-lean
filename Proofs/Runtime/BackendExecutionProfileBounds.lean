import Proofs.Runtime.BackendExecutionProfile

/-! Resource algebra and boundary recovery for original-code profiles. Maxima
measure encoded values and loop counters; sums measure actual executed work and
queries. All of these facts are independent of a state-passing implementation. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.ExecutionProfile

universe v w

def Metrics.price {I : Type} (a : Metrics I) (route query : Nat) : Nat :=
  a.work + a.visits * route + a.requests.length * query

@[simp] theorem Metrics.price_join {I : Type} (a b : Metrics I) (route query : Nat) :
    (a.join b).price route query = a.price route query + b.price route query := by
  simp only [price, join, List.length_append, Nat.add_mul]
  omega

@[simp] theorem Metrics.price_node {I : Type} (a : Metrics I) (width counter route query : Nat) :
    (a.node width counter).price route query = a.price route query + route := by
  simp only [price, node, Nat.add_mul, Nat.one_mul]
  omega

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {I : Type} {spec : OracleSpec I} {iface : Interface (C := C) spec}

omit [C.HasProd] [C.HasSum] in
theorem frame_sizes {A B : Type} (a : C.Str A) (b : C.Str B) (input : A)
    (result : Result I B) (extraWidth counter : Nat) :
    Q.size a input ≤ (frame (Q := Q) a b input result extraWidth counter).2.width ∧
      Q.size b result.1 ≤ (frame (Q := Q) a b input result extraWidth counter).2.width := by
  dsimp only [frame, Metrics.node]
  omega

omit [C.HasProd] [C.HasSum] in
theorem frame_fits {A B : Type} (a : C.Str A) (b : C.Str B) (input : A)
    (result : Result I B) (extraWidth counter width limit : Nat) (allowed : I → Prop) :
    (frame (Q := Q) a b input result extraWidth counter).2.Fits width limit allowed ↔
      extraWidth ≤ width ∧ Q.size a input ≤ width ∧ Q.size b result.1 ≤ width ∧
        counter ≤ limit ∧ result.2.Fits width limit allowed := by
  simp only [frame, Metrics.fits_node, max_le_iff]
  tauto

omit [C.HasProd] [C.HasSum] in
theorem loop_sizes {A B : Type} (a : C.Str A) (b : C.Str B)
    (body : A → OracleComp spec (Result I (B ⊕ A)))
    (stop : A → OracleComp spec (Result I B)) (fuel : Nat) (input : A)
    (r : Result I B) (hr : r ∈ support (loop (Q := Q) a b body stop fuel input)) :
    Q.size a input ≤ r.2.width ∧ Q.size b r.1 ≤ r.2.width := by
  cases fuel with
  | zero =>
      simp only [loop, support_map, Set.mem_image] at hr
      obtain ⟨result, _, rfl⟩ := hr
      exact frame_sizes a b input result 0 0
  | succ fuel =>
      simp only [loop, mem_support_bind_iff] at hr
      obtain ⟨step, _, hr⟩ := hr
      cases h : step.1 with
      | inl output =>
          simp only [h, support_pure, Set.mem_singleton_iff] at hr
          subst r
          exact frame_sizes a b input (output, step.2) 0 (fuel + 1)
      | inr next =>
          simp only [h, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
          obtain ⟨result, _, rfl⟩ := hr
          exact frame_sizes a b input (result.1, step.2.join result.2) 0 (fuel + 1)

theorem run_sizes {A B : Type} {a : C.Str A} {b : C.Str B}
    (program : Code Q spec iface a b) (input : A) (r : Result I B)
    (hr : r ∈ support (run program input)) :
    Q.size a input ≤ r.2.width ∧ Q.size b r.1 ≤ r.2.width := by
  cases program with
  | atomic code =>
      simp only [run, support_pure, Set.mem_singleton_iff] at hr
      subst r
      exact frame_sizes _ _ _ _ _ _
  | query =>
      simp only [run, support_map, Set.mem_image] at hr
      obtain ⟨reply, _, rfl⟩ := hr
      exact frame_sizes _ _ _ _ _ _
  | seq initial following =>
      simp only [run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨first, _, second, _, rfl⟩ := hr
      exact frame_sizes _ _ _ _ _ _
  | branch left right =>
      cases input <;> simp only [run, support_map, Set.mem_image] at hr <;>
        obtain ⟨result, _, rfl⟩ := hr <;> exact frame_sizes _ _ _ _ _ _
  | first retained body =>
      simp only [run, support_map, Set.mem_image] at hr
      obtain ⟨result, _, rfl⟩ := hr
      exact frame_sizes _ _ _ _ _ _
  | loop body stop fuel => exact loop_sizes _ _ _ _ fuel input r hr
  | iterate counter body =>
      simp only [run, support_map, Set.mem_image] at hr
      obtain ⟨result, _, rfl⟩ := hr
      exact frame_sizes _ _ _ _ _ _

theorem Within.price {A B : Type} {a : C.Str A} {b : C.Str B}
    (program : Code Q spec iface a b) (input : A) (work visits queries width counter : Nat)
    (allowed : I → Prop) (h : Within program input work visits queries width counter allowed)
    (route query : Nat) (r : Result I B) (hr : r ∈ support (run program input)) :
    r.2.price route query ≤ work + visits * route + queries * query := by
  obtain ⟨hw, hv, hq, _⟩ := h r hr
  exact Nat.add_le_add (Nat.add_le_add hw (Nat.mul_le_mul_right route hv))
    (Nat.mul_le_mul_right query hq)

end Signatures.Runtime.BackendProgram.ExecutionProfile
