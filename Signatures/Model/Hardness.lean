import Mathlib.Basic.ENNReal.Basic

/-!
# Hardness within an explicitly supplied resource class

`within budget B` must mean that an implementation of `B` meets the chosen resource budget
and any model restrictions (such as algebraicity) required by the hardness assumption.
This interface does not assign a runtime to an extensional Lean function. A concrete backend
must supply implementation/cost evidence; counting oracle queries alone is not enough.
Hardness is a caller hypothesis, never a local axiom or a claim about unbounded algorithms.
-/

namespace Model

/-- Every solver certified within `budget` has advantage at most `epsilon`.
The resource predicate is explicit; this definition supplies no runtime certificate. -/
def HardWithin {Solver : Type*} (advantage : Solver → ENNReal)
    (within : Nat → Solver → Prop) (budget : Nat) (epsilon : ENNReal) : Prop :=
  ∀ B, within budget B → advantage B ≤ epsilon

end Model
