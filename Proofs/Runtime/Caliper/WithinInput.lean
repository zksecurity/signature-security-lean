import Proofs.Runtime.Caliper.Within

/-! Change the mathematical view of a bounded program's input only when the
stored bytes are equal. The executable and all resource bounds stay the same. -/
namespace Signatures.Runtime.CaliperBackend.Interactive
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {A B D I : Type} {spec : OracleSpec I}
    {port : Port w spec} {input : Layout w A} {output : Layout w B}
    {words memory time : Nat} {algorithm : input.Value → OracleComp spec B}

theorem Within.viewInput (bounded : Within port input output words memory time algorithm)
    (newInput : Layout w D) (view : newInput.Value → input.Value)
    (sameBytes : ∀ value, input.representation.encoding.encode (view value) =
      newInput.representation.encoding.encode value) :
    Within port newInput output words memory time (fun value => algorithm (view value)) := by
  obtain ⟨code, fits, stored, semantics, resources⟩ := bounded
  have sameState (value : newInput.Value) : input.representation.initial (view value) =
      newInput.representation.initial value := by
    have sameWords : input.representation.encoding.words = newInput.representation.encoding.words := by
      rw [← input.representation.encoding.encode_length (view value), sameBytes value,
        newInput.representation.encoding.encode_length value]
    unfold Representation.initial
    rw [sameBytes value, sameWords]
  refine ⟨code, fits, stored, ?_, ?_⟩
  · intro tape value
    simpa only [sameState value] using semantics tape (view value)
  · intro tape value finished reached
    rw [← sameState value] at reached ⊢
    exact resources tape (view value) finished reached

end Signatures.Runtime.CaliperBackend.Interactive
