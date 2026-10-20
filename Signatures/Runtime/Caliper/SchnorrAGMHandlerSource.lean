import Signatures.Runtime.Caliper.SchnorrAGMHandler
import Signatures.Runtime.BackendSchnorrAGMInterface
import Signatures.Runtime.Caliper.SchnorrAGMHandlerRandomSource

/-! The complete service preserves the original dependent request and the joint
reply/store query tree. Erasure interprets stored packet bytes; it supplies no
machine conversion or free request storage. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler
open Caliper BoundedSource OracleComp OracleSpec Schnorr.AGM AlgebraicGroupModel.Interaction
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS randomBound : Nat} {M F G : Type} [DecidableEq M] [DecidableEq G]
    (layout : Layouts w M F G qH qS randomBound)

def admissible (q : Interface.NativeRequest F G M) (saved : (G × G) × EncodedState F G M) : Prop :=
  match q with
  | .inl args => layout.randomInput.valid (args, saved)
  | .inr (.inl args) => layout.hashInput.valid (args, saved)
  | .inr (.inr args) => layout.signingInput.valid (args, saved)
def inputFor (q : Interface.NativeRequest F G M) (saved : (G × G) × EncodedState F G M)
    (valid : admissible layout q saved) : Dispatch.Input layout :=
  match q with
  | .inl args => .inl ⟨(args, saved), valid⟩
  | .inr (.inl args) => .inr (.inl ⟨(args, saved), valid⟩)
  | .inr (.inr args) => .inr (.inr ⟨(args, saved), valid⟩)

def eraseReply : Dispatch.Output layout → Interface.SourceIndex F G M × ((G × G) × EncodedState F G M)
  | .inl (answer, args) => (Interface.randomTag (args.val, answer.val.1), answer.val.2)
  | .inr (.inl (answer, args)) => (Interface.scalarTag false (args.val, answer.val.1), answer.val.2)
  | .inr (.inr (answer, args)) => (Interface.scalarTag true (args.val, answer.val.1), answer.val.2)

variable [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [SampleableType F]
    (ops : Operations layout) (sampler : ProbComp layout.scheme.scalar.Value)
    (uniform : Subtype.val <$> sampler = ($ᵗ F : ProbComp F))

include uniform in
theorem source_original (q : Interface.NativeRequest F G M) (g pk : G) (state : Signatures.Runtime.SchnorrAGM.State F G M)
    (valid : admissible layout q ((g, pk), encodeState state)) :
    eraseReply layout <$> source layout ops sampler (inputFor layout q ((g, pk), encodeState state) valid) =
      (fun result => ((⟨Interface.decodeRequest q, result.1⟩ : Interface.SourceIndex F G M), (g, pk), encodeState result.2)) <$>
        (Signatures.Runtime.SchnorrAGM.handler g pk (Interface.decodeRequest q)).run state := by
  rcases q with ⟨n, groups, rows⟩ | ⟨message, groups, rows⟩ | ⟨message, groups, rows⟩
  · have core := RandomComponent.source_original layout g pk state n groups rows valid
    have lifted := congrArg (Functor.map (fun p : (Nat × List G) × ((G × G) × EncodedState F G M) =>
      (Interface.randomTag (M := M) ((n, groups, rows), p.1), p.2))) core
    dsimp only [OracleSpec.Range, explainedSpec, Reply] at lifted ⊢
    simp only [Functor.map_map, Interface.randomTag_fin] at lifted
    simp only [source, Dispatch.source, Dispatch.randomSource, inputFor, Sum.elim, Functor.map_map,
      eraseReply, Dispatch.randomRequest, Interface.decodeRequest] at lifted ⊢
    convert lifted using 1
    congr 1
  · have core := HashComponent.source_original layout ops.zeroValid ops.mul ops.add ops.mulNames.buffers ops.addNames.buffers ops.reserve
      sampler uniform g pk state message groups rows valid
    have lifted := congrArg (Functor.map (fun p : (F × List G) × ((G × G) × EncodedState F G M) =>
      (Interface.scalarTag false ((message, groups, rows), p.1), p.2))) core
    dsimp only [OracleSpec.Range, explainedSpec, Reply] at lifted ⊢
    simp only [Functor.map_map] at lifted
    simp only [source, Dispatch.source, Dispatch.hashSource, hashSource, inputFor, Sum.elim, Functor.map_map,
      eraseReply, Dispatch.hashRequest, Interface.decodeRequest, Interface.scalarTag, Bool.false_eq_true, ↓reduceIte,
      decodeGroupReply] at lifted ⊢
    convert lifted using 1
    congr 1
  · have core := SigningComponent.source_original layout ops.zeroValid ops.scale ops.sub ops.negate ops.scaleNames.buffers ops.subNames.buffers
      ops.negateNames.buffers ops.reserve sampler uniform g pk state message groups rows valid
    have lifted := congrArg (Functor.map (fun p : (F × List G) × ((G × G) × EncodedState F G M) =>
      (Interface.scalarTag true ((message, groups, rows), p.1), p.2))) core
    dsimp only [OracleSpec.Range, explainedSpec, Reply] at lifted ⊢
    simp only [Functor.map_map] at lifted
    simp only [source, Dispatch.source, Dispatch.signingSource, signingSource, inputFor, Sum.elim, Functor.map_map,
      eraseReply, Dispatch.signingRequest, Interface.decodeRequest, Interface.scalarTag, ↓reduceIte,
      decodeGroupReply] at lifted ⊢
    convert lifted using 1
    congr 1

include uniform in
theorem source_request (q : Interface.SourceRequest F G M) (g pk : G) (state : Signatures.Runtime.SchnorrAGM.State F G M)
    (valid : admissible layout (Interface.encodeRequest q) ((g, pk), encodeState state)) :
    eraseReply layout <$> source layout ops sampler (inputFor layout (Interface.encodeRequest q) ((g, pk), encodeState state) valid) =
      (fun result => ((⟨q, result.1⟩ : Interface.SourceIndex F G M), (g, pk), encodeState result.2)) <$>
        (Signatures.Runtime.SchnorrAGM.handler g pk q).run state := by
  generalize encoded : Interface.encodeRequest q = native at valid ⊢
  have decoded : Interface.decodeRequest native = q := by rw [← encoded, Interface.decode_encodeRequest]
  subst q
  exact source_original layout ops sampler uniform native g pk state valid

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler
