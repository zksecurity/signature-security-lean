import Proofs.Runtime.Caliper.SchnorrROMFinEnumSampler
import Proofs.Runtime.Caliper.UniformSamplingBounds

/-! A direct uniform scalar draw for the public challenge oracle. Unlike the
private signing caller, its internal uniform query is not itself replayed.
The surrounding raw oracle records the single scalar-family cell. The finite
index and scalar have identical encoded bytes, so their view needs no code. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Enumerated.Direct
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F : Type} (params : Parameters w F)

def request : Fin (Fresh.randomBound (w := w) + 1) :=
  ⟨params.bound, by rw [Fresh.randomSize]; have := params.rangeFits; omega⟩

def code : Interactive.Code w :=
  UniformSampling.code Fresh.randomBound params.wordFits Fresh.randomFits (request params)

def source : ProbComp (scalar params).Value :=
  (fun answer : Fin (params.bound + 1) => (⟨params.index.symm answer, trivial⟩ : (scalar params).Value)) <$>
    (unifSpec.query params.bound : ProbComp (Fin (params.bound + 1)))

theorem refines : Interactive.Refines (Fresh.port (tape params)) .unit
    (tape params).unit.representation (scalar params).representation (fun _ => source params) (code params) := by
  have drawn := (UniformSampling.refines Fresh.randomBound params.wordFits Fresh.randomFits (request params)).viewOutput
    (scalar params).representation (fun value => ⟨params.index.symm value.val, trivial⟩) (by
      intro value
      change [BitVec.ofNat w (params.index (params.index.symm value.val)).val] = [BitVec.ofNat w value.val.val]
      exact congrArg (fun answer : Fin (params.bound + 1) => [BitVec.ofNat w answer.val])
        (params.index.apply_symm_apply value.val))
  change Interactive.Refines (UniformQuery.port Fresh.randomBound params.wordFits Fresh.randomFits) .unit
    (UniformSampling.input (w := w)).representation (scalar params).representation (fun _ => source params)
    (UniformSampling.code Fresh.randomBound params.wordFits Fresh.randomFits (request params))
  simpa only [UniformSampling.source, Functor.map_map, source, request] using drawn

theorem uniform :
    letI := sampleable params
    Subtype.val <$> source params = ($ᵗ F : ProbComp F) := rfl

theorem uniform_finEnum [FinEnum F] [Nonempty F] (capacity : Nat)
    (wordFits : 16 < 2 ^ w) (rangeFits : FinEnum.card F + 1 < 2 ^ w)
    (storageFits : 16 * (4 + (capacity + 2) * 3) < 2 ^ w) :
    Subtype.val <$> source (Parameters.ofFinEnum w F capacity wordFits rangeFits storageFits) = ($ᵗ F : ProbComp F) := by
  have same := sampleable_finEnum capacity wordFits rangeFits storageFits
  have sampled := uniform (Parameters.ofFinEnum w F capacity wordFits rangeFits storageFits)
  rw [same] at sampled
  exact sampled

theorem time_bound : Interactive.TimeBound (Fresh.port (tape params)) .unit
    (tape params).unit.representation (code params) 26 :=
  UniformSampling.time_bound Fresh.randomBound params.wordFits Fresh.randomFits (request params)

theorem code_words : ((code params).lower (Fresh.port (tape params))).descriptionWords ≤ 125 :=
  UniformSampling.code_words Fresh.randomBound params.wordFits Fresh.randomFits (request params)

theorem names : WordIO.NamesBound ((code params).lower (Fresh.port (tape params))) 3 :=
  UniformSampling.names Fresh.randomBound params.wordFits Fresh.randomFits (request params)

theorem buffers : ((code params).lower (Fresh.port (tape params))).memBound ≤ 2 := by
  change 2 ≤ 2
  rfl

theorem descriptionFits : ((code params).lower (Fresh.port (tape params))).DescriptionFits :=
  UniformSampling.descriptionFits Fresh.randomBound params.wordFits Fresh.randomFits (request params)

/-- The sampler's complete local cost, including stored code and total memory. -/
theorem within :
    letI := sampleable params
    Interactive.Within (Fresh.port (tape params)) (tape params).unit (scalar params)
      125 166 26 (fun _ => ($ᵗ F : ProbComp F)) := by
  have bounded := Interactive.within_of_refines (refines params) (time_bound params)
    (code_words params) (names params) (descriptionFits params)
  exact bounded.congr (fun _ => uniform params)

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Enumerated.Direct
