import Proofs.Runtime.Caliper.CoronServiceLayout
import VCVio.OracleComp.Constructions.SampleableType.Basic

/-! All co-CDH challenges are represented. Uniform scalar sampling supplies
scalar coverage; implemented scaling and a cyclic generator supply point
coverage. Public-key coverage also follows from implemented scaling. -/
namespace Signatures.Runtime.CaliperBackend.CoronFull
open Caliper BoundedSource OracleComp OracleSpec
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G K : Type}
    (service : CoronService.Layouts w M F G randomBound qS) (key : Layout w K)
    (fits : key.representation.encoding.words + service.service.config.representation.encoding.words < 2 ^ w)

def sourceChallenge : Layout w (K × (G × (G × G))) := key.prod service.service.config fits

variable [SampleableType F] (sampler : CoronService.Sampler service)
include sampler in
theorem scalar_valid (scalar : F) : service.cache.value.valid scalar := by
  have reached : scalar ∈ support (Subtype.val <$> sampler.source) := by
    rw [sampler.law]
    exact mem_support_uniformSample F
  rw [support_map, Set.mem_image] at reached
  obtain ⟨represented, _, equal⟩ := reached
  exact equal ▸ represented.property

variable [SMul F G] [Add G] [Zero G] (routines : CoronService.Routines service)
    (generator : service.point.Value)
    (generates : Function.Surjective (fun scalar : F => scalar • generator.val))
include sampler routines generates in
theorem point_valid (point : G) : service.point.valid point := by
  obtain ⟨scalar, rfl⟩ := generates point
  exact routines.scale.preserves (scalar, generator.val)
    ⟨scalar_valid service sampler scalar, generator.property⟩

variable [SMul F K]
    (scalarKeyFits : service.cache.value.representation.encoding.words + key.representation.encoding.words < 2 ^ w)
    (keyScale : Implementation .unit (service.cache.value.prod key scalarKeyFits) key (fun value => value.1 • value.2))
    (keyGenerator : key.Value)
include sampler routines generates keyScale in
theorem challenge_valid (scalar : F) (point : G) :
    (sourceChallenge service key fits).valid (scalar • keyGenerator.val, generator.val, scalar • generator.val, point) := by
  have represented := scalar_valid service sampler scalar
  exact ⟨keyScale.preserves (scalar, keyGenerator.val) ⟨represented, keyGenerator.property⟩,
    generator.property, routines.scale.preserves (scalar, generator.val) ⟨represented, generator.property⟩,
    point_valid service sampler routines generator generates point⟩

end Signatures.Runtime.CaliperBackend.CoronFull
