import Signatures.Runtime.Caliper.SchnorrROMEnumeratedSampler

/-! The concrete caller implements the canonical one-query uniform sampler as
an exact query program. No distribution-only substitution changes replay order. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Enumerated
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F : Type} (params : Parameters w F)

theorem original_typed (input : (tape params).unit.Value) :
    original (layout params) (caller params) 1 (terminates params) input =
      (fun answer : Fin (params.bound + 1) => (⟨params.index.symm answer, trivial⟩ : (scalar params).Value)) <$>
        (unifSpec.query params.bound : ProbComp (Fin (params.bound + 1))) := by
  have implemented := CallerMachine.ofCaller_implements (spec := unifSpec) Subtype.val (representReply (layout params))
    (advance params) (initial params) 1 (terminates params) input
  change (do
    let answer ← (unifSpec.query params.bound : ProbComp (Fin (params.bound + 1)))
    pure (some (normalized params ((), representReply (layout params) (request params) answer)))) =
      some <$> original (layout params) (caller params) 1 (terminates params) input at implemented
  apply (map_inj_right (fun h => Option.some.inj h)).mp
  rw [← implemented]
  change (do
    let answer ← (unifSpec.query params.bound : ProbComp (Fin (params.bound + 1)))
    pure (some (normalized params ((), representReply (layout params) (request params) answer)))) = (do
      let answer ← (unifSpec.query params.bound : ProbComp (Fin (params.bound + 1)))
      pure (some (⟨params.index.symm answer, trivial⟩ : (scalar params).Value)))
  apply bind_congr
  intro answer
  congr 1
  apply congrArg some
  apply Subtype.ext
  change params.index.symm ⟨answer.val % (params.bound + 1), _⟩ = params.index.symm answer
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt answer.isLt)

theorem original_scalar (input : (tape params).unit.Value) :
    Subtype.val <$> original (layout params) (caller params) 1 (terminates params) input =
      params.index.symm <$> (unifSpec.query params.bound : ProbComp (Fin (params.bound + 1))) := by
  rw [original_typed]
  rfl

/-- A lawful canonical sampler associated with the chosen scalar index. -/
@[reducible] def sampleable : SampleableType F := SampleableType.ofEquiv params.index.symm

theorem samples (input : (tape params).unit.Value) :
    letI := sampleable params
    Subtype.val <$> original (layout params) (caller params) 1 (terminates params) input = ($ᵗ F : ProbComp F) := by
  exact original_scalar params input

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Enumerated
