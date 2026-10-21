import Signatures.Runtime.Caliper.SchnorrROMReplayExtract

/-! Exact source correspondence of the executed extractor with the original
`extractFork` on the observed controller result, for every input: fork failure,
a cutoff first or second pass, different commitments, equal challenges and
success. Every fallback is the uniform draw `$ᵗ F`. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Extract
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

theorem finish_fallback :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    Subtype.val <$> finish config (fallbackValue config) = ($ᵗ F : ProbComp F) :=
  PrivateSampler.Enumerated.Direct.uniform config.sampler

variable [Field F] [DecidableEq F] [DecidableEq G]

theorem source_original (value : Result config) :
    letI := PrivateSampler.Enumerated.sampleable config.sampler
    Subtype.val <$> source config value = Schnorr.extractFork (G₂ := G) (K := M) (observed config value) := by
  let := PrivateSampler.Enumerated.sampleable config.sampler
  rcases value with _ | ⟨⟨first, firstStore⟩, ⟨second, secondStore⟩⟩
  · exact finish_fallback config
  · rcases first with _ | ⟨forgeFirst, challengeFirst⟩ <;> rcases second with _ | ⟨forgeSecond, challengeSecond⟩
    · exact finish_fallback config
    · exact finish_fallback config
    · exact finish_fallback config
    · rcases forgeFirst with ⟨⟨messageFirst, commitmentFirst, responseFirst⟩, validFirst⟩
      rcases forgeSecond with ⟨⟨messageSecond, commitmentSecond, responseSecond⟩, validSecond⟩
      rcases challengeFirst with ⟨challengeFirst, _⟩
      rcases challengeSecond with ⟨challengeSecond, _⟩
      change Subtype.val <$> finish config (choiceOf config (coreValue ((commitmentFirst, commitmentSecond),
          ((responseFirst, responseSecond), (challengeFirst, challengeSecond))))) =
        Schnorr.extractValues (G₂ := G) (K := M)
          (((messageFirst, commitmentFirst, responseFirst), challengeFirst), firstStore.val.1, [])
          (((messageSecond, commitmentSecond, responseSecond), challengeSecond), secondStore.val.1, [])
      unfold coreValue Schnorr.extractValues
      by_cases accepted : commitmentFirst = commitmentSecond ∧ challengeFirst ≠ challengeSecond
      · simp only [accepted, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
        rfl
      · simp only [accepted, ↓reduceIte]
        exact finish_fallback config

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Extract
