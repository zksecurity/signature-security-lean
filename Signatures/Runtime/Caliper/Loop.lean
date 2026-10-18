import Signatures.Runtime.Caliper.Branch

/-! Bounded local control with actual machine code. The body returns either a
result or the next state. At exhausted fuel the stop routine is executed.

This compiler unrolls the *bound*, leaving a runtime branch after each body call.
Both generated code size and execution time are bounded linearly in that bound;
it does not claim the source's one-copy loop code footprint. Interactive oracle
suspension and reachable-capacity refinement remain separate obligations.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper

variable {w : Nat} {S B : Type}

def loopFunction (body : S → B ⊕ S) (stop : S → B) : Nat → S → B
  | 0, state => stop state
  | fuel + 1, state => Sum.elim id (loopFunction body stop fuel) (body state)

/-- The local compiler implements the same stopping convention as the shared
reduction language's loop, specialized to local deterministic computation. -/
theorem loopFunction_eq_source (body : S → B ⊕ S) (stop : S → B) (fuel : Nat) (state : S) :
    loopFunction body stop fuel state = BackendProgram.loopDenote (m := Id) body stop fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    simp only [loopFunction, BackendProgram.loopDenote]
    cases body state with
    | inl result => rfl
    | inr next => exact ih next

def loopRealizer (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (state : Representation w S) (result : Representation w B) (hw : 16 < 2 ^ w)
    (fits : 1 + max result.encoding.words state.encoding.words < 2 ^ w)
    {f : S → B ⊕ S} {g : S → B}
    (body : Realizer cost state (result.sum state (width_pos hw) fits) f)
    (stop : Realizer cost state result g) :
    (fuel : Nat) → Realizer cost state result (loopFunction f g fuel)
  | 0 => stop
  | fuel + 1 => body.then (branchRealizer cost allocation result state result
      (Realizer.identity (width_pos hw) result)
      (loopRealizer cost allocation state result hw fits body stop fuel) hw fits)

/-- Every stored copy of the body, branch and payload normalization is counted.
The bound is not hidden in a constant-cost host iterator. -/
theorem loopRealizer_descriptionWords (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (state : Representation w S) (result : Representation w B) (hw : 16 < 2 ^ w)
    (fits : 1 + max result.encoding.words state.encoding.words < 2 ^ w)
    {f : S → B ⊕ S} {g : S → B}
    (body : Realizer cost state (result.sum state (width_pos hw) fits) f)
    (stop : Realizer cost state result g) (fuel : Nat) :
    descriptionWords (loopRealizer cost allocation state result hw fits body stop fuel).code =
      descriptionWords stop.code + fuel *
        (descriptionWords body.code + 26 * result.encoding.words + 26 * state.encoding.words + 39) := by
  induction fuel with
  | zero => simp [loopRealizer]
  | succ fuel ih =>
    simp only [loopRealizer, Realizer.then, branchRealizer, Realizer.identity,
      descriptionWords_seq, Dispatch.code_descriptionWords] at *
    rw [ih]
    simp only [descriptionWords, description, List.length_cons, List.length_nil]
    ring

/-- A uniform body/stop bound gives a concrete linear runtime bound. Payload
copying and tag dispatch contribute at every iteration, including early exit. -/
theorem loopRealizer_time_le (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (state : Representation w S) (result : Representation w B) (hw : 16 < 2 ^ w)
    (fits : 1 + max result.encoding.words state.encoding.words < 2 ^ w)
    {f : S → B ⊕ S} {g : S → B}
    (body : Realizer cost state (result.sum state (width_pos hw) fits) f)
    (stop : Realizer cost state result g) (bodyBound stopBound : Nat)
    (body_bound : ∀ value, body.time value ≤ bodyBound)
    (stop_bound : ∀ value, stop.time value ≤ stopBound) (fuel : Nat) (value : S) :
    (loopRealizer cost allocation state result hw fits body stop fuel).time value ≤
      fuel * (bodyBound + cost.memLoad + cost.branch +
        max ((selectSlice (w := w) 1 result.encoding.words).staticTime cost)
          ((selectSlice (w := w) 1 state.encoding.words).staticTime cost)) + stopBound := by
  induction fuel generalizing value with
  | zero => simpa [loopRealizer] using stop_bound value
  | succ fuel ih =>
    have hb := body_bound value
    have hl := le_max_left ((selectSlice (w := w) 1 result.encoding.words).staticTime cost)
      ((selectSlice (w := w) 1 state.encoding.words).staticTime cost)
    have hr := le_max_right ((selectSlice (w := w) 1 result.encoding.words).staticTime cost)
      ((selectSlice (w := w) 1 state.encoding.words).staticTime cost)
    simp only [loopRealizer, Realizer.then, branchRealizer]
    cases next : f value with
    | inl answer =>
      simp only [Dispatch.time, Realizer.identity, Nat.add_zero]
      rw [Nat.succ_mul]
      omega
    | inr nextState =>
      have bound := ih nextState
      simp only [Dispatch.time]
      rw [Nat.succ_mul]
      omega

end Signatures.Runtime.CaliperBackend
