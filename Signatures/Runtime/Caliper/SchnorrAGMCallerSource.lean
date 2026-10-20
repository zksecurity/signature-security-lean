import Signatures.Runtime.Caliper.SchnorrAGMCallerHandler
import Signatures.Runtime.Caliper.SynchronizesObservations

/-! The caller-facing service has the original dependent request/reply law.
The encoded-state relation is explicit: unused optional-entry padding need not
be canonical for arbitrary stored values, whereas reachable source states are. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerHandler
open Caliper BoundedSource OracleComp OracleSpec CallerPackets
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS randomBound : Nat} {M F G : Type}
    (layout : Handler.Layouts w M F G qH qS randomBound)

def nativeRequest : Request layout → Interface.NativeRequest F G M
  | .inl args => .inl args.val
  | .inr (.inl args) => .inr (.inl args.val)
  | .inr (.inr args) => .inr (.inr args.val)
def query (args : Request layout) : Interface.SourceRequest F G M := Interface.decodeRequest (nativeRequest layout args)
def replyValue : Reply layout → Interface.SourceIndex F G M
  | .inl (answer, args) => Interface.randomTag (args.val, answer.val)
  | .inr (.inl (answer, args)) => Interface.scalarTag false (args.val, answer.val)
  | .inr (.inr (answer, args)) => Interface.scalarTag true (args.val, answer.val)
def observed (value : Reply layout × layout.scheme.store.Value) := (replyValue layout value.1, value.2.val)
/-- The stored random answer is in the requested range, before dependent tagging. -/
def canonicalReply : Reply layout → Prop
  | .inl (answer, args) => answer.val.1 ≤ args.val.1
  | .inr _ => True
theorem observed_finished (value : Handler.Dispatch.Output layout) :
    observed layout (finished layout value) = Handler.eraseReply layout value := by
  rcases value with value | (value | value) <;> rfl

variable [DecidableEq M] [DecidableEq G]
theorem admissible_request (value : Packet layout) (valid : ready layout value) :
    Handler.admissible layout (nativeRequest layout value.1) value.2.val := by
  rcases value with ⟨args | (args | args), saved⟩
  · exact ⟨args.property, saved.property⟩
  · exact ⟨⟨args.property, saved.property⟩, valid⟩
  · exact ⟨⟨args.property, saved.property⟩, valid⟩
theorem serviceRequest_inputFor (value : Packet layout) (valid : ready layout value) :
    serviceRequest layout value valid = Handler.inputFor layout (nativeRequest layout value.1) value.2.val
      (admissible_request layout value valid) := by
  rcases value with ⟨args | (args | args), saved⟩ <;> rfl

variable [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [SampleableType F]
    (ops : Handler.Operations layout) (sampler : ProbComp layout.scheme.scalar.Value)
    (uniform : Subtype.val <$> sampler = ($ᵗ F : ProbComp F))

omit [SampleableType F] in
theorem source_canonical (value : Packet layout) (answer : Reply layout × layout.scheme.store.Value)
    (reached : answer ∈ support (source layout ops sampler value)) :
    canonicalReply layout answer.1 := by
  unfold source at reached
  split at reached
  · rcases value with ⟨args | (args | args), saved⟩
    · simp only [Handler.source, Handler.Dispatch.source, serviceRequest, Sum.elim,
        Handler.Dispatch.randomSource, Functor.map_map, support_map, Set.mem_image] at reached
      obtain ⟨result, supported, rfl⟩ := reached
      exact (Handler.RandomComponent.reply_bound layout _ result supported).1
    · simp only [Handler.source, Handler.Dispatch.source, serviceRequest, Sum.elim,
        Handler.Dispatch.hashSource, Functor.map_map, support_map, Set.mem_image] at reached
      obtain ⟨result, _, rfl⟩ := reached
      trivial
    · simp only [Handler.source, Handler.Dispatch.source, serviceRequest, Sum.elim,
        Handler.Dispatch.signingSource, Functor.map_map, support_map, Set.mem_image] at reached
      obtain ⟨result, _, rfl⟩ := reached
      trivial
  · obtain rfl := (mem_support_pure_iff _ _).mp reached
    rcases value with ⟨args | (args | args), saved⟩
    · exact Nat.zero_le _
    · trivial
    · trivial

include uniform in
theorem source_original (value : Packet layout) (valid : ready layout value)
    (state : Signatures.Runtime.SchnorrAGM.State F G M) (encoded : value.2.val.2 = encodeState state) :
    observed layout <$> source layout ops sampler value =
      (fun result => ((⟨query layout value.1, result.1⟩ : Interface.SourceIndex F G M),
        value.2.val.1, encodeState result.2)) <$>
          (Signatures.Runtime.SchnorrAGM.handler value.2.val.1.1 value.2.val.1.2 (query layout value.1)).run state := by
  rw [source, dite_eq_left valid, Functor.map_map]
  change (fun answer => observed layout (finished layout answer)) <$> _ = _
  simp only [observed_finished]
  rw [serviceRequest_inputFor]
  have core := Handler.source_original layout ops sampler uniform (nativeRequest layout value.1)
    value.2.val.1.1 value.2.val.1.2 state (by
      simpa only [← encoded] using admissible_request layout value valid)
  simpa only [← encoded, Prod.mk.eta, query] using core

include uniform in
theorem synchronizes (value : Packet layout) (valid : ready layout value)
    (state : Signatures.Runtime.SchnorrAGM.State F G M) (encoded : value.2.val.2 = encodeState state) :
    Synchronizes (fun represented original =>
      replyValue layout represented.1 = (⟨query layout value.1, original.1⟩ : Interface.SourceIndex F G M) ∧
      represented.2.val = (value.2.val.1, encodeState original.2))
      (source layout ops sampler value)
      ((Signatures.Runtime.SchnorrAGM.handler value.2.val.1.1 value.2.val.1.2 (query layout value.1)).run state) := by
  have joint := Synchronizes.of_map_eq (observed layout)
    (fun result : (Interface.sourceSpec F G M).Range (query layout value.1) × Signatures.Runtime.SchnorrAGM.State F G M =>
      ((⟨query layout value.1, result.1⟩ : Interface.SourceIndex F G M), value.2.val.1, encodeState result.2))
      (source_original layout ops sampler uniform value valid state encoded)
  exact joint.mono (fun _ _ equal => Prod.mk.inj equal)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerHandler
