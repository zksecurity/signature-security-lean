import Signatures.Runtime.BackendWithin
import Signatures.Runtime.PolynomialNegligible

/-! Nonuniform families in one fixed quantitative backend. Encodings and input
caps are fixed before quantifying over algorithms. Each security parameter has
one program that works at every input, with a fixed polynomial bound on its
entire stored code/advice and on online time. No uniform program generator is
claimed by this convention. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {I : Type} {spec : OracleSpec I} {iface : Interface (C := C) spec}
  {control : ControlCosts} {queryCost : (i : I) → spec.Range i → Nat}
  (backend : Backend.{v, w, x} Q spec iface control queryCost)
  (sizes : DescriptionSize Q) (factor : Nat) (description : backend.DescriptionBound sizes factor)
  {A B : Nat → Type} (a : ∀ n, C.Str (A n)) (b : ∀ n, C.Str (B n))
  (inputSize : Nat → Nat)

def NonuniformWithin (algorithm : ∀ n, A n → OracleComp spec (B n)) : Prop :=
  PolynomiallyBounded inputSize ∧
  ∃ codeSize time : Nat → Nat, PolynomiallyBounded codeSize ∧ PolynomiallyBounded time ∧
    ∀ n, Within backend sizes factor description (a n) (b n) (inputSize n) (codeSize n) (time n) (algorithm n)

theorem NonuniformWithin.of_pointwise (algorithm : ∀ n, A n → OracleComp spec (B n))
    (codeSize time : Nat → Nat) (hi : PolynomiallyBounded inputSize)
    (hc : PolynomiallyBounded codeSize) (ht : PolynomiallyBounded time)
    (hw : ∀ n, Within backend sizes factor description (a n) (b n) (inputSize n) (codeSize n) (time n) (algorithm n)) :
    NonuniformWithin backend sizes factor description a b inputSize algorithm := ⟨hi, codeSize, time, hc, ht, hw⟩

/-- The family class has an actual program family, with all fixed advice in
the charged description. The selection is by parameter, never by challenge. -/
theorem NonuniformWithin.executable_family (algorithm : ∀ n, A n → OracleComp spec (B n))
    (h : NonuniformWithin backend sizes factor description a b inputSize algorithm) :
    ∃ programs : ∀ n, backend.Program (a n) (b n), ∃ codeSize time : Nat → Nat,
      PolynomiallyBounded codeSize ∧ PolynomiallyBounded time ∧
      (∀ n, description.size (programs n) ≤ codeSize n) ∧
      (∀ n input, Run.value <$> backend.execute (programs n) input = algorithm n input) ∧
      ∀ n input, Q.size (a n) input ≤ inputSize n →
        ∀ z ∈ support (backend.execute (programs n) input), z.steps ≤ time n := by
  classical
  obtain ⟨_, codeSize, time, hc, ht, hw⟩ := h
  choose programs hp using hw
  exact ⟨programs, codeSize, time, hc, ht, fun n => (hp n).1,
    fun n => (hp n).2.1, fun n => (hp n).2.2⟩

/-- Asymptotic hardness against this explicit polynomial-time, polynomial-code
nonuniform class. The backend and encodings are parameters of the assumption. -/
def NonuniformHardness (advantage : ∀ n, (A n → OracleComp spec (B n)) → ENNReal) : Prop :=
  ∀ algorithm, NonuniformWithin backend sizes factor description a b inputSize algorithm →
    negligible (fun n => advantage n (algorithm n))

theorem NonuniformHardness.apply_of_pointwise
    (advantage : ∀ n, (A n → OracleComp spec (B n)) → ENNReal)
    (hardness : NonuniformHardness backend sizes factor description a b inputSize advantage)
    (algorithm : ∀ n, A n → OracleComp spec (B n)) (codeSize time : Nat → Nat)
    (hi : PolynomiallyBounded inputSize) (hc : PolynomiallyBounded codeSize) (ht : PolynomiallyBounded time)
    (hw : ∀ n, Within backend sizes factor description (a n) (b n) (inputSize n) (codeSize n) (time n) (algorithm n)) :
    negligible (fun n => advantage n (algorithm n)) :=
  hardness algorithm (NonuniformWithin.of_pointwise backend sizes factor description a b inputSize algorithm codeSize time hi hc ht hw)

end Signatures.Runtime.BackendProgram
