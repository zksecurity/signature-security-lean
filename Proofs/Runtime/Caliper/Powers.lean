import Proofs.Runtime.Caliper.PowersBase

/-! Construct a fixed-dimensional power vector with a proved scratch bound.
The generated program contains one multiplication and copied frame per stage;
neither the power function nor the complete generator is a supplied primitive. -/
namespace Signatures.Runtime.CaliperBackend.Powers
open Caliper BoundedSource
variable {w capacity : Nat} {F : Type} [Mul F] (layout : Layouts w F capacity)
    {slots : Nat} (reserve : baseSlots slots + capacity < 2 ^ w)

def prepend {n : Nat} (bound : n + 1 ≤ capacity) {f : F × F → Fin n → F}
    (tail : Implementation .unit layout.input (layout.vector n (by omega)) f)
    (tailBuffers : tail.program.code.memBound ≤ baseSlots slots + n) :
    Implementation .unit layout.input (layout.vector (n + 1) bound)
      (fun input => Fin.cases input.2 (f input)) where
  preserves input valid := Fin.cases valid.2 (tail.preserves input valid)
  program := ((current layout).pair tail (by decide) layout.wordFits
    (nameFits reserve _ ((current_buffers layout).trans (by unfold baseSlots; omega)))
    (nameFits reserve _ (tailBuffers.trans (by omega)))
    (layout.fits_of_le (by have := layout.input_le; omega))
    (layout.fits_of_le (by have := layout.input_le; have := layout.scalar_le; omega))
    (layout.fits_of_le (by have := layout.scalar_le; have := layout.vector_le n (by omega); omega))).program.viewOutput
      _ _ (fun _ => rfl)

omit [Mul F] in
theorem prepend_buffers {n : Nat} (bound : n + 1 ≤ capacity) {f : F × F → Fin n → F}
    (tail : Implementation .unit layout.input (layout.vector n (by omega)) f)
    (tailBuffers : tail.program.code.memBound ≤ baseSlots slots + n) :
    (prepend layout reserve bound tail tailBuffers).program.code.memBound ≤ baseSlots slots + (n + 1) := by
  have paired := Implementation.pair_buffers (current layout) tail layout.wordFits
    (nameFits reserve _ ((current_buffers layout).trans (by unfold baseSlots; omega)))
    (nameFits reserve _ (tailBuffers.trans (by omega)))
    (layout.fits_of_le (by have := layout.input_le; omega))
    (layout.fits_of_le (by have := layout.input_le; have := layout.scalar_le; omega))
    (layout.fits_of_le (by have := layout.scalar_le; have := layout.vector_le n (by omega); omega))
    (current_buffers layout) tailBuffers
  exact paired.trans (by unfold baseSlots; omega)

omit [Mul F] in
theorem prepend_bounded {n : Nat} (bound : n + 1 ≤ capacity) {f : F × F → Fin n → F}
    (tail : Implementation .unit layout.input (layout.vector n (by omega)) f)
    (tailBuffers : tail.program.code.memBound ≤ baseSlots slots + n)
    {time words : Nat} (budget : tail.BoundedBy time words) :
    (prepend layout reserve bound tail tailBuffers).BoundedBy
      (time + 120 * layout.width) (words + 400 * layout.width + 200) := by
  have paired := Implementation.pair_boundedBy (current layout) tail layout.wordFits
    (nameFits reserve _ ((current_buffers layout).trans (by unfold baseSlots; omega)))
    (nameFits reserve _ (tailBuffers.trans (by omega)))
    (layout.fits_of_le (by have := layout.input_le; omega))
    (layout.fits_of_le (by have := layout.input_le; have := layout.scalar_le; omega))
    (layout.fits_of_le (by have := layout.scalar_le; have := layout.vector_le n (by omega); omega))
    (Implementation.second_boundedBy _ _ _ _) budget
  refine ⟨fun input => (paired.time_le input).trans ?_, paired.code_le.trans ?_⟩
  all_goals
    have inputBound := layout.input_le
    have scalarBound := layout.scalar_le
    have vectorBound := layout.vector_le n (by omega)
    dsimp only [Layouts.input, Layout.prod, Representation.transport, Representation.prod,
      Encoding.transport, Encoding.prod, Encoding.checked] at inputBound ⊢
    omega

omit [Mul F] in
theorem prepend_names {n : Nat} (bound : n + 1 ≤ capacity) {f : F × F → Fin n → F}
    (tail : Implementation .unit layout.input (layout.vector n (by omega)) f)
    (tailBuffers : tail.program.code.memBound ≤ baseSlots slots + n)
    {names : Nat} (named : NamesAccounted tail.program.code names) :
    NamesAccounted (prepend layout reserve bound tail tailBuffers).program.code names :=
  Implementation.pair_names (current layout) tail layout.wordFits
    (nameFits reserve _ ((current_buffers layout).trans (by unfold baseSlots; omega)))
    (nameFits reserve _ (tailBuffers.trans (by omega)))
    (layout.fits_of_le (by have := layout.input_le; omega))
    (layout.fits_of_le (by have := layout.input_le; have := layout.scalar_le; omega))
    (layout.fits_of_le (by have := layout.scalar_le; have := layout.vector_le n (by omega); omega))
    (Implementation.second_names _ _ _ _ _) named

structure Compiled (n : Nat) (bound : n ≤ capacity) where
  implementation : Implementation .unit layout.input (layout.vector n bound) (values n)
  buffers : implementation.program.code.memBound ≤ baseSlots slots + n

variable (mul : Implementation .unit layout.input layout.scalar (fun input => input.1 * input.2))
    (mulBuffers : mul.program.code.memBound ≤ slots)

def compile : (n : Nat) → (bound : n ≤ capacity) → Compiled layout (slots := slots) n bound
  | 0, bound =>
      { implementation := Implementation.constant layout.input (layout.vector 0 bound)
          ⟨Fin.elim0, fun i => Fin.elim0 i⟩ layout.wordFits
        buffers := (Implementation.constant_buffers _ _ _ _).trans (by unfold baseSlots; omega) }
  | n + 1, bound =>
      let rest := compile n (by omega)
      let tail := (step layout mul mulBuffers reserve).then rest.implementation
      have tailBuffers : tail.program.code.memBound ≤ baseSlots slots + n :=
        max_le ((step_buffers layout mul mulBuffers reserve).trans (by omega)) rest.buffers
      { implementation := prepend layout reserve bound tail tailBuffers
        buffers := prepend_buffers layout reserve bound tail tailBuffers }

def timeBudget (mulTime n : Nat) : Nat := n * (mulTime + 500 * layout.width)
def codeBudget (mulWords n : Nat) : Nat := 14 + n * (mulWords + 1700 * layout.width + 500)

theorem bounded {mulTime mulWords : Nat} (budget : mul.BoundedBy mulTime mulWords)
    (n : Nat) (bound : n ≤ capacity) :
    (compile layout reserve mul mulBuffers n bound).implementation.BoundedBy
      (timeBudget layout mulTime n) (codeBudget layout mulWords n) := by
  induction n with
  | zero =>
    apply (Implementation.constant_bounded layout.input (layout.vector 0 bound)
      ⟨Fin.elim0, fun i => Fin.elim0 i⟩ layout.wordFits).mono <;> simp [timeBudget, codeBudget, Layouts.vector,
        Layout.vector, vectorEncoding, Encoding.transport, Encoding.unit, Encoding.checked]
  | succ n ih =>
    have tailBuffers :
        ((step layout mul mulBuffers reserve).then
          (compile layout reserve mul mulBuffers n (by omega)).implementation).program.code.memBound ≤ baseSlots slots + n :=
      max_le ((step_buffers layout mul mulBuffers reserve).trans (by omega))
        (compile layout reserve mul mulBuffers n (by omega)).buffers
    apply (prepend_bounded layout reserve bound _ tailBuffers
      ((step_bounded layout mul mulBuffers reserve budget).then (ih (by omega)))).mono
    all_goals
      simp only [timeBudget, codeBudget, Nat.add_mul, Nat.one_mul]
      omega

theorem names {names : Nat} (named : NamesAccounted mul.program.code names)
    (n : Nat) (bound : n ≤ capacity) :
    NamesAccounted (compile layout reserve mul mulBuffers n bound).implementation.program.code names := by
  induction n with
  | zero => exact Implementation.constant_names _ _ _ _ names
  | succ n ih =>
    have tailBuffers :
        ((step layout mul mulBuffers reserve).then
          (compile layout reserve mul mulBuffers n (by omega)).implementation).program.code.memBound ≤ baseSlots slots + n :=
      max_le ((step_buffers layout mul mulBuffers reserve).trans (by omega))
        (compile layout reserve mul mulBuffers n (by omega)).buffers
    exact prepend_names layout reserve bound _ tailBuffers
      ((step_names layout mul mulBuffers reserve named).seq (ih (by omega)))

section Source
variable {F : Type} [CommMonoid F]

theorem values_eq (n : Nat) (input : F × F) (i : Fin n) :
    values n input i = input.2 * input.1 ^ i.val := by
  induction n generalizing input with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [values]
    · simpa [values, next, pow_succ, mul_assoc, mul_comm, mul_left_comm] using ih (next input) j
end Source

end Signatures.Runtime.CaliperBackend.Powers
