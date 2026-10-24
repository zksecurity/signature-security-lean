import Proofs.Runtime.Caliper.SchnorrROMNonzeroSigningHandlerBounds
import Proofs.Runtime.Caliper.SchnorrROMHandlerSource

/-! The executed nonzero-nonce signing branch as a `Handler.SigningBranch`, with
its source law to the nonzero-nonce list backend. The branch is built over a
full-field operation record for its point routines; the resulting handler is
that record with this branch and one more buffer name. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Handler
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec

section Branch
variable {w : Nat} {M F G : Type} [Zero F] [SMul F G] [Sub G] [Add F] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (base : Operations config)
    (arith : NonzeroSigning.Arithmetic config) (positive : 0 < config.sampler.bound)
    {scaleTime scaleWords subTime subWords addTime addWords : Nat}
    (scaleBound : base.scale.BoundedBy scaleTime scaleWords) (subBound : base.sub.BoundedBy subTime subWords)
    (addBound : arith.add.BoundedBy addTime addWords)

def nonzero : SigningBranch config (NonzeroSigning.slots config base arith + 1) where
  code := NonzeroSigning.code config base arith positive
  source := NonzeroSigning.source config base arith positive
  refines := NonzeroSigning.refines config base arith positive
  time := NonzeroSigning.handlerTime config scaleTime subTime addTime
  words := NonzeroSigning.handlerWords config positive scaleWords subWords addWords
  nameSlots := NonzeroSigning.handlerNames config (NonzeroSigning.slots config base arith)
  time_bound := NonzeroSigning.time_bound config base arith positive scaleBound subBound addBound
  code_bound := NonzeroSigning.code_bound config base arith positive scaleBound subBound addBound
  names := NonzeroSigning.handler_names config base arith positive _
    (base.scaleNames.mono (Nat.le_max_left _ _)).accounted (base.subNames.mono (Nat.le_max_left _ _)).accounted
    (arith.addNames.mono (Nat.le_max_right _ _)).accounted
  buffers := by
    have := NonzeroSigning.handler_buffers config base arith positive
    omega
  descriptionFits := NonzeroSigning.descriptionFits config base arith positive
  preserves_config := by
    intro value answer reached
    simp only [NonzeroSigning.source, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at reached
    obtain ⟨sampled, _, nonce, _, rfl⟩ := reached
    rfl
  preserves_live := NonzeroSigning.preserves_live config base arith positive
  managed_length := NonzeroSigning.managed_length config base arith positive
  tape_lengths := by
    intro value valid answer reached
    simp only [NonzeroSigning.source, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at reached
    obtain ⟨sampled, supported, nonce, nonceSupported, rfl⟩ := reached
    have pair := PrivateSampler.Pair.tape_lengths config.handler.sampler (PrivateSampler.Enumerated.caller config.sampler)
      trivial 1 (Signing.Handler.tapes config.handler value) (NonzeroSigning.pair_ready config value valid) sampled supported
    have third := PrivateSampler.Service.tape_lengths config.handler.sampler (NonzeroSigning.nonzeroCaller config positive)
      trivial 1 _ (NonzeroSigning.nonce_ready config value valid sampled supported) nonce nonceSupported
    change nonce.val.2.1.length ≤ value.val.2.2.1.length + 3 ∧ nonce.val.2.2.length ≤ value.val.2.2.2.length
    change sampled.val.2.2.1.length ≤ value.val.2.2.1.length + (1 + 1) ∧ sampled.val.2.2.2.length ≤ value.val.2.2.2.length at pair
    change nonce.val.2.1.length ≤ sampled.val.2.2.1.length + 1 ∧ nonce.val.2.2.length ≤ sampled.val.2.2.2.length at third
    exact ⟨by omega, by omega⟩

/-- The nonzero-nonce handler: the base point routines with the nonzero branch. -/
def withNonzero (reserve : NonzeroSigning.slots config base arith + 1 + 3 < 2 ^ w) : Operations config where
  scale := base.scale
  sub := base.sub
  slots := NonzeroSigning.slots config base arith + 1
  scaleNames := base.scaleNames.mono (by unfold NonzeroSigning.slots; omega)
  subNames := base.subNames.mono (by unfold NonzeroSigning.slots; omega)
  reserve := reserve
  signing := nonzero config base arith positive scaleBound subBound addBound

end Branch

section Law
variable {w : Nat} {M F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (base : Operations config)
    (arith : NonzeroSigning.Arithmetic config) (positive : 0 < config.sampler.bound)
    {scaleTime scaleWords subTime subWords addTime addWords : Nat}
    (scaleBound : base.scale.BoundedBy scaleTime scaleWords) (subBound : base.sub.BoundedBy subTime subWords)
    (addBound : arith.add.BoundedBy addTime addWords)

/-- The branch's original semantics: the nonzero-nonce list backend, under the
enumerated field sampler and its canonical nonzero-scalar sampler. -/
def nonzeroLaw : SigningLaw config (nonzero config base arith positive scaleBound subBound addBound) where
  target := letI := PrivateSampler.Enumerated.sampleable config.sampler
    letI := PrivateSampler.Enumerated.Nonzero.unitsSampleable config.sampler
    Schnorr.NonzeroListROM.handler
  shared _ := rfl
  source_original value valid := NonzeroSigning.source_original config base arith value valid

end Law
end Signatures.Runtime.CaliperBackend.SchnorrROM.Handler
