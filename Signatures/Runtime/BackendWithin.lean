import Signatures.Runtime.BackendBudget
import Signatures.Model.Hardness

/-! Resource classes for the common backend.

Hardness ranges over the backend's actual program type, which can include the
general caller's local code. It is not limited to the old arithmetic language.
Code size and input size are explicit, separate from online execution time.
The backend, encodings, execution/description measures, and their adequacy are
fixed parameters, never chosen afresh for an individual solver or challenge.
-/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {I : Type} {spec : OracleSpec I} {iface : Interface (C := C) spec}
  {control : ControlCosts} {queryCost : (i : I) → spec.Range i → Nat}
  (backend : Backend.{v, w, x} Q spec iface control queryCost)
  (sizes : DescriptionSize Q) (factor : Nat) (description : backend.DescriptionBound sizes factor)

/-- One fixed program, including its stored code/data description, realizes
the algorithm at every input. Its execution bound holds on all supported paths
for inputs within the stated encoded-size cap. -/
def Within {A B : Type} (a : C.Str A) (b : C.Str B)
    (inputSize codeSize time : Nat) (algorithm : A → OracleComp spec B) : Prop :=
  ∃ executable : backend.Program a b,
    description.size executable ≤ codeSize ∧
    (∀ input, Run.value <$> backend.execute executable input = algorithm input) ∧
    ∀ input, Q.size a input ≤ inputSize → ∀ z ∈ support (backend.execute executable input),
      z.steps ≤ time

theorem Within.mono {A B : Type} {a : C.Str A} {b : C.Str B}
    {inputSize codeSize time codeSize' time' : Nat} {algorithm : A → OracleComp spec B}
    (h : Within backend sizes factor description a b inputSize codeSize time algorithm)
    (hc : codeSize ≤ codeSize') (ht : time ≤ time') :
    Within backend sizes factor description a b inputSize codeSize' time' algorithm := by
  obtain ⟨code, hd, he, hr⟩ := h
  exact ⟨code, hd.trans hc, he, fun input hi z hz => (hr input hi z hz).trans ht⟩

/-- Compilation constructs the implementation witness. The syntax budget is
proved using the component rules, and the code-size bound follows from the
backend's structural description-expansion contract. -/
theorem within_compile {A B : Type} {a : C.Str A} {b : C.Str B}
    (code : Code Q spec iface a b) (inputSize time : Nat)
    (algorithm : A → OracleComp spec B)
    (he : ∀ input, code.denote input = algorithm input)
    (hb : Bounds control queryCost code (fun input => Q.size a input ≤ inputSize) (fun _ => True) time) :
    Within backend sizes factor description a b inputSize
      (factor * code.descriptionSize sizes) time algorithm := by
  refine ⟨backend.compile code, backend.compile_descriptionSize sizes factor description code, ?_, ?_⟩
  · intro input
    rw [backend.compile_erase, he]
  · intro input hi z hz
    rw [backend.compile_execute] at hz
    exact (hb input hi z hz).2

/-- A hardness assumption can now quantify over this same implementation class.
Instantiating `within_compile` supplies its resource premise without changing the
attacker's internal language. Scheme probability theorems supply the advantage relation. -/
theorem advantage_le_of_compile {A B : Type} {a : C.Str A} {b : C.Str B}
    (code : Code Q spec iface a b) (inputSize time : Nat)
    (algorithm : A → OracleComp spec B)
    (advantage : (A → OracleComp spec B) → ENNReal) (epsilon : ENNReal)
    (hardness : Model.HardWithin advantage
      (Within backend sizes factor description a b inputSize (factor * code.descriptionSize sizes))
      time epsilon)
    (he : ∀ input, code.denote input = algorithm input)
    (hb : Bounds control queryCost code (fun input => Q.size a input ≤ inputSize) (fun _ => True) time) :
    advantage algorithm ≤ epsilon :=
  hardness algorithm (within_compile backend sizes factor description code inputSize time algorithm he hb)

end Signatures.Runtime.BackendProgram
