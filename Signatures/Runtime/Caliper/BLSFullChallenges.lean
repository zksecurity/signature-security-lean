import Signatures.Runtime.Caliper.BLSFullProgram
import VCVio.OracleComp.Constructions.SampleableType.Basic

/-! The scalar sampler's full support forces every scalar to be representable.
Primitive scaling then proves that every sampled DLog challenge fits, from just
the represented generators. No challenge-coverage or complete-solver premise is
added to the reduction certificate. -/
namespace Signatures.Runtime.CaliperBackend.BLSFull
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {M F G K A : Type}
    [Zero F] [Mul F] [Add F] [Sub F] [Neg F] [Div F] [SMul F G] [Add G] [SMul F K]
    (layout : Layouts w M F G K A) (routines : Routines layout)
    [SampleableType F] (drawSource : ProbComp layout.scheme.cache.value.Value)
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ F : ProbComp F))

omit [Zero F] [Mul F] [Add F] [Sub F] [Neg F] [Div F] [SMul F G] [Add G] [SMul F K] in
include drawLaw in
theorem scalar_valid (scalar : F) : layout.scheme.cache.value.valid scalar := by
  have reached : scalar ∈ support (Subtype.val <$> drawSource) := by
    rw [drawLaw]
    exact mem_support_uniformSample F
  rw [support_map, Set.mem_image] at reached
  obtain ⟨represented, _, equal⟩ := reached
  exact equal ▸ represented.property

include routines drawLaw in
theorem point_valid (generator : layout.scheme.point.Value)
    (generates : Function.Surjective (fun scalar : F => scalar • generator.val))
    (point : G) : layout.scheme.point.valid point := by
  obtain ⟨scalar, rfl⟩ := generates point
  exact routines.groupScale.preserves (scalar, generator.val)
    ⟨scalar_valid layout drawSource drawLaw scalar, generator.property⟩

include routines drawLaw in
theorem challenge_valid (generator : layout.scheme.point.Value) (keyGenerator : layout.key.Value) (scalar : F) :
    layout.setup.challenge.valid ((generator.val, scalar • generator.val), (keyGenerator.val, scalar • keyGenerator.val)) := by
  have represented := scalar_valid layout drawSource drawLaw scalar
  exact ⟨⟨generator.property, routines.groupScale.preserves (scalar, generator.val) ⟨represented, generator.property⟩⟩,
    keyGenerator.property, routines.keyScale.preserves (scalar, keyGenerator.val) ⟨represented, keyGenerator.property⟩⟩
end Signatures.Runtime.CaliperBackend.BLSFull
