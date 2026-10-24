import Proofs.Runtime.Caliper.SchnorrAGMSampling

/-! Equality with the original accepted-signing oracle. Sampling order,
collisions, chronological histories and the source flags are preserved. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Sampling
open Caliper BoundedSource OracleComp OracleSpec
open Signatures.Runtime.SchnorrAGM
open Signatures.Runtime.SchnorrAGM.Native
open _root_.Schnorr.AGM
variable {w qH qS : Nat} {M F G : Type} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq M] [DecidableEq G] (layout : Histories.Layouts w M F G qH qS)

omit [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G] in
theorem reserved_ready {hashes signatures : Nat} {state : Signatures.Runtime.SchnorrAGM.State F G M}
    (room : layout.scheme.Reserved hashes (signatures + 1) state) (generator publicKey : G) (message : M) :
    ready layout (generator, publicKey, message, encodeState state) := by
  change (state.cache.map _).length ≤ qH + qS ∧ (state.representations.map _).length < qS + 2 ∧ state.signed.length < qS
  simp only [List.length_map]
  have cache := room.2.1
  have basis := room.2.2.1
  have signed := room.2.2.2
  omega

omit [AddCommGroup G] [Module F G] [DecidableEq M] [DecidableEq G] in
theorem input_valid (scalars : ∀ scalar, layout.scheme.scalar.valid scalar) (points : ∀ point, layout.scheme.point.valid point)
    {hashes signatures : Nat} {state : Signatures.Runtime.SchnorrAGM.State F G M}
    (room : layout.scheme.Reserved hashes (signatures + 1) state) (generator publicKey : G) (message : M)
    (messageValid : layout.scheme.message.valid message) :
    (input layout).valid (generator, publicKey, message, encodeState state) :=
  ⟨⟨points generator, points publicKey, messageValid, CaliperBackend.SchnorrAGM.Layouts.Reserved.encoded layout.scheme room scalars points⟩,
    reserved_ready layout room generator publicKey message⟩

variable (zeroValid : layout.scheme.scalar.valid 0)
    (scale : Implementation .unit layout.signing.arithmetic.scaleArgs layout.scheme.point (fun args => args.1 • args.2))
    (sub : Implementation .unit layout.signing.arithmetic.points layout.scheme.point (fun args => args.1 - args.2))
    (negate : Implementation .unit layout.scheme.scalar layout.scheme.scalar Neg.neg)
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots)
    (subBuffers : sub.program.code.memBound ≤ slots) (negateBuffers : negate.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w)

theorem uniform [SampleableType F] (sampler : ProbComp layout.scheme.scalar.Value)
    (law : Subtype.val <$> sampler = ($ᵗ F : ProbComp F)) (args : (input layout).Value) :
    Subtype.val <$> denote layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampler args = (do
      let challenge ← ($ᵗ F : ProbComp F)
      let response ← ($ᵗ F : ProbComp F)
      pure (Signatures.Runtime.SchnorrAGM.Native.Signing.signedValue ((challenge, response), args.val))) := by
  rw [erase, law]
  rfl

theorem source_original [DecidableEq F] [SampleableType F] (sampler : ProbComp layout.scheme.scalar.Value)
    (law : Subtype.val <$> sampler = ($ᵗ F : ProbComp F))
    (state : Signatures.Runtime.SchnorrAGM.State F G M) (generator publicKey : G) (message : M) (coefficients : List (List F))
    (valid : (input layout).valid (generator, publicKey, message, encodeState state)) :
    (fun result => (signingReply result.val.1.1 result.val.1.2, result.val.2)) <$>
      denote layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampler
        ⟨(generator, publicKey, message, encodeState state), valid⟩ =
      (fun result => (result.1, encodeState result.2)) <$>
        (Signatures.Runtime.SchnorrAGM.handler generator publicKey ⟨⟨.sign message, fun _ => []⟩, fun _ => coefficients⟩).run state := by
  have erased := uniform layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampler law
    ⟨(generator, publicKey, message, encodeState state), valid⟩
  have observed := congrArg (fun computation : ProbComp ((G × F) × EncodedState F G M) =>
    (fun result => (signingReply result.1.1 result.1.2, result.2)) <$> computation) erased
  have together := (PFunctor.FreeM.comp_map (fun result : (G × F) × EncodedState F G M =>
      (signingReply result.1.1 result.1.2, result.2)) Subtype.val
    (denote layout zeroValid scale sub negate scaleBuffers subBuffers negateBuffers reserve sampler
      ⟨(generator, publicKey, message, encodeState state), valid⟩)).trans observed
  refine together.trans ?_
  simp only [map_bind, map_pure, Signatures.Runtime.SchnorrAGM.Native.Signing.signedValue_source,
    Signatures.Runtime.SchnorrAGM.handler, StateT.run, ne_eq, not_true_eq_false, ite_false]
  rfl

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Sampling
