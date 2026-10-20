import Signatures.Runtime.Caliper.SchnorrAGMSigningDispatchBounds

/-! Actual signing buffer footprints, including both scalar draws and their
saved request. These bounds locate an outer saved configuration safely. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Sampling
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS : Nat} {M F G I : Type} [Zero F] [SMul F G] [Sub G] [Neg F]
    [DecidableEq M] [DecidableEq G] {spec : OracleSpec I}
    (layout : Histories.Layouts w M F G qH qS) (zeroValid : layout.scheme.scalar.valid 0)
    (scale : Implementation .unit layout.signing.arithmetic.scaleArgs layout.scheme.point (fun args => args.1 • args.2))
    (sub : Implementation .unit layout.signing.arithmetic.points layout.scheme.point (fun args => args.1 - args.2))
    (negate : Implementation .unit layout.scheme.scalar layout.scheme.scalar Neg.neg)
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots)
    (subBuffers : sub.program.code.memBound ≤ slots) (negateBuffers : negate.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w) (port : Interactive.Port w spec)

theorem buffers (sampler : Interactive.Code w) {sampleSlots : Nat}
    (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) :
    ((code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port).memBound ≤
      max 9 (max (slots + 3) (sampleSlots + 2)) := by
  have paired := (PairSampling.names layout.scheme.scalar layout.scheme.scalar layout.scheme.wordFits (pairFits layout) port
    sampler sampler sampleNames sampleNames).buffers
  change ((pairs layout port sampler).lower port).memBound ≤ PairSampling.slots sampleSlots sampleSlots at paired
  have saved := Interactive.retain_buffers port (pairs layout port sampler) 0
    layout.scheme.affine.representation.encoding.words (input layout).representation.encoding.words
  change ((sample layout port sampler).lower port).memBound ≤ _ at saved
  have computed := Sampled.buffers layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve
  change max ((sample layout port sampler).lower port).memBound
    (Sampled.implementation layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve).program.code.memBound ≤ _
  unfold PairSampling.slots at paired
  omega
end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Sampling

namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.SigningDispatch
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS : Nat} {M F G I : Type} [Zero F] [SMul F G] [Sub G] [Neg F]
    [DecidableEq M] [DecidableEq G] {spec : OracleSpec I}
    (layout : Layouts w M F G qH qS) (zeroValid : layout.scheme.scalar.valid 0)
    (scale : Implementation .unit layout.signing.signing.arithmetic.scaleArgs layout.scheme.point (fun args => args.1 • args.2))
    (sub : Implementation .unit layout.signing.signing.arithmetic.points layout.scheme.point (fun args => args.1 - args.2))
    (negate : Implementation .unit layout.scheme.scalar layout.scheme.scalar Neg.neg)
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots)
    (subBuffers : sub.program.code.memBound ≤ slots) (negateBuffers : negate.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w) (port : Interactive.Port w spec)

theorem buffers (sampler : Interactive.Code w) {sampleSlots : Nat}
    (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) :
    ((code layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port).memBound ≤
      max 9 (max (slots + 3) (sampleSlots + 2)) := by
  have selected := selector_buffers layout
  have packed := accept_buffers layout
  have sampled := Signing.Sampling.buffers layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler sampleNames
  have wrapped := wrap_buffers layout
  have rejected := reject_buffers layout zeroValid
  have branches := Interactive.dispatch_buffers port
    (accepted layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler)
    (.compute (SigningDispatch.rejected layout zeroValid).code) layout.yes.representation.encoding.words layout.no.representation.encoding.words
  change ((dispatch layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port).memBound ≤
    max 2 (max (max (accept layout).code.memBound
      (max ((Signing.Sampling.code layout.signing zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port).memBound
        (wrap layout).code.memBound)) (reject layout zeroValid).code.memBound) at branches
  change max (selector layout).program.code.memBound
    ((dispatch layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve port sampler).lower port).memBound ≤ _
  omega
end Signatures.Runtime.CaliperBackend.SchnorrAGM.SigningDispatch
