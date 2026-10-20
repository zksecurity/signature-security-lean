import Signatures.Runtime.Caliper.SchnorrAGMFullBounds
import Signatures.Runtime.Caliper.CyclicDLog
import VCVio.OracleComp.Constructions.SampleableType.Basic

/-! The complete generated Schnorr reduction belongs to the cyclic DLog class.
Full-support scalar sampling and implemented group scaling establish challenge
coverage from a represented generator. No solver certificate is assumed. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Full
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS randomBound : Nat} {M F G A : Type}
    (layout : CallerExtraction.Layouts w M F G qH qS randomBound A)
    [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq M] [DecidableEq G] [SampleableType F]
    (routines : Routines layout) (sampleSource : ProbComp layout.service.scheme.scalar.Value)
    (uniform : Subtype.val <$> sampleSource = ($ᵗ F : ProbComp F))

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq M] [DecidableEq G] in
include uniform in
theorem scalar_valid (scalar : F) : layout.service.scheme.scalar.valid scalar := by
  have reached : scalar ∈ support (Subtype.val <$> sampleSource) := by
    rw [uniform]
    exact mem_support_uniformSample F
  rw [support_map, Set.mem_image] at reached
  obtain ⟨represented, _, equal⟩ := reached
  exact equal ▸ represented.property

omit [DecidableEq F] [DecidableEq M] [DecidableEq G] in
include uniform routines in
theorem challenge_valid (generator : layout.service.scheme.point.Value) (scalar : F) :
    layout.service.scheme.config.valid (generator.val, scalar • generator.val) :=
  ⟨generator.property, routines.handler.scale.preserves (scalar, generator.val)
    ⟨scalar_valid layout sampleSource uniform scalar, generator.property⟩⟩

variable (caller : Caller layout) (bound : Routines.Bounds layout routines) (limits : Caller.Limits)
    (bounded : Caller.Bounds layout caller limits) (sampler : Interactive.Code w) (fuel : Nat)
    {sampleTime sampleWords sampleSlots : Nat}
    (sampleBound : Interactive.TimeBound layout.service.random.port .unit (PairSampling.input w).representation sampler sampleTime)
    (sampleStored : (sampler.lower layout.service.random.port).descriptionWords ≤ sampleWords)
    (sampleNames : WordIO.NamesBound (sampler.lower layout.service.random.port) sampleSlots)
    (sampleFits : (sampler.lower layout.service.random.port).DescriptionFits)
    (addresses : AddressBounds layout routines bound sampleSlots sampleWords)
    (sampleCorrect : Interactive.Refines layout.service.random.port .unit (PairSampling.input w).representation
      layout.service.scheme.scalar.representation (fun _ => sampleSource) sampler)
    (invariant : Caller.Invariant layout caller fuel) (witness : Caller.Source layout caller fuel invariant)
    (adversary : _root_.Schnorr.AGM.Adversary F G M)
    (same : ∀ value, (fun answer => Signatures.Runtime.SchnorrAGM.Native.Interface.decodeForgery answer.val) <$>
      witness.program (witness.inputView value) = adversary.main (_root_.Schnorr.AGM.initial value.val.1 value.val.2))
    (generator : layout.service.scheme.point.Value)

include uniform bounded sampleBound sampleStored sampleNames sampleFits addresses sampleCorrect same in
theorem dlogWithin :
    cyclicDLogWithin layout.service.random.port layout.service.scheme.config layout.service.scheme.scalar generator.val
      (codeBudget layout routines bound limits sampleWords fuel)
      (memoryBudget layout routines bound limits sampleTime sampleWords sampleSlots fuel)
      (timeBudget layout routines bound limits sampleTime fuel)
      (Signatures.Runtime.SchnorrAGM.dlogReduction adversary) :=
  ⟨challenge_valid layout routines sampleSource uniform generator,
    within_original layout routines caller bound limits bounded sampler fuel sampleBound sampleStored sampleNames sampleFits addresses
      sampleSource sampleCorrect uniform invariant witness adversary same⟩

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Full
