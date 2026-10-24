import Proofs.Runtime.Caliper.SchnorrAGMFullDLog
import Proofs.Runtime.SchnorrAGMSecurity

/-! Concrete Schnorr AGM security against the fixed Caliper DLog class.
The complete reduction witness is constructed from local caller code and named
primitive implementations. The original shared-AGM game and probability bound
are unchanged; code, time and total-memory limits are derived above. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Full
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS randomBound : Nat} {M F G A : Type}
    (layout : CallerExtraction.Layouts w M F G qH qS randomBound A)
    [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq M] [DecidableEq G] [SampleableType F] [Fintype F]
    (routines : Routines layout) (sampleSource : ProbComp layout.service.scheme.scalar.Value)
    (uniform : Subtype.val <$> sampleSource = ($ᵗ F : ProbComp F))
    (caller : Caller layout) (bound : Routines.Bounds layout routines) (limits : Caller.Limits)
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
    (generates : Function.Injective (fun scalar : F => scalar • generator.val))
    (signQueries : ∀ pk, IsQueryBoundP (adversary.main (_root_.Schnorr.AGM.initial generator.val pk))
      (fun q => _root_.Schnorr.AGM.Reduction.signRequest q = true) qS)
    (hashQueries : ∀ pk, IsQueryBoundP (adversary.main (_root_.Schnorr.AGM.initial generator.val pk))
      (fun q => _root_.Schnorr.AGM.Reduction.hashRequest q = true) qH)

include uniform bounded sampleBound sampleStored sampleNames sampleFits addresses sampleCorrect same generates signQueries hashQueries in
theorem security :
    𝒟[_root_.Schnorr.AGM.game generator.val adversary] {true} ≤
      cyclicDLogSuccessBound layout.service.random.port layout.service.scheme.config layout.service.scheme.scalar generator.val
        (codeBudget layout routines bound limits sampleWords fuel)
        (memoryBudget layout routines bound limits sampleTime sampleWords sampleSlots fuel)
        (timeBudget layout routines bound limits sampleTime fuel) +
      (qH + 1 : ENNReal) * (Fintype.card F : ENNReal)⁻¹ +
      (qS : ENNReal) * (qS + qH) * (Fintype.card F : ENNReal)⁻¹ := by
  have implemented := dlogWithin layout routines sampleSource uniform caller bound limits bounded sampler fuel sampleBound sampleStored
    sampleNames sampleFits addresses sampleCorrect invariant witness adversary same generator
  have hardness := Model.le_advantageBound (fun solver => 𝒟[DiffieHellman.dlogExperiment generator.val solver] {true})
    _ _ implemented
  exact (Signatures.Runtime.SchnorrAGM.security generator.val generates adversary qS qH signQueries hashQueries).trans
    (add_le_add (add_le_add hardness le_rfl) le_rfl)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Full
