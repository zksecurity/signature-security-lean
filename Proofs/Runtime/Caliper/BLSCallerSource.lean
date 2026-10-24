import Proofs.Runtime.Caliper.BLSCallerHandler
import Proofs.Runtime.Caliper.SynchronizesObservations

/-! Joint original-oracle semantics of the generated BLS caller handler.
Random replies retain their query range as well as their answer, so the
correspondence covers the complete dependent reply packet. -/

namespace Signatures.Runtime.CaliperBackend.BLSCallerHandler
open Caliper BoundedSource OracleComp OracleSpec BLSCallerPackets Model.LazyAGM

section Observations
variable {w : Nat} {M R C G : Type} (layout : BLSReply.Layouts w M R C G) (randomBound : Nat)

def query : Request layout randomBound → (advSpec M M G).Domain
  | .inl n => .inl (.inl n.val)
  | .inr (.inl message) => .inl (.inr message.val)
  | .inr (.inr message) => .inr message.val

def replyValue : Reply layout randomBound → (Nat × Nat) ⊕ G
  | .inl packet => .inl (packet.1.val, packet.2.val)
  | .inr point => .inr point.val

def answer : (q : Request layout randomBound) → (advSpec M M G).Range (query layout randomBound q) → (Nat × Nat) ⊕ G
  | .inl n, value => .inl (n.val, value.val)
  | .inr (.inl _), value | .inr (.inr _), value => .inr value

def observed (value : Reply layout randomBound × layout.store.Value) : ((Nat × Nat) ⊕ G) × BLSReply.Store M R C G :=
  (replyValue layout randomBound value.1, value.2.val)

def replyMatches (q : Request layout randomBound) (value : Reply layout randomBound)
    (original : (advSpec M M G).Range (query layout randomBound q)) : Prop :=
  replyValue layout randomBound value = answer layout randomBound q original

end Observations

variable {w : Nat} {C G : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    (layout : BLSReply.Layouts w (key.Value base) (val.Value base) C G)
    (default : layout.cache.value.Value) (randomBound : Nat)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op) (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit layout.responseInput layout.point (respond signing))
    {slots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w)
    (drawSource : ProbComp layout.cache.value.Value)
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

noncomputable def original (respond : Bool → val.Value base × C → G) :
    QueryImpl (advSpec (key.Value base) (key.Value base) G)
      (StateT (BLSReply.Store (key.Value base) (val.Value base) C G) ProbComp) :=
  fun q saved => (fun reply => (reply.1, saved.1, reply.2)) <$>
    ((LazyAGM.listOracle (fun sample => respond false (sample, saved.1)) (fun sample => respond true (sample, saved.1))) q).run saved.2

include drawLaw in
theorem denote_source (value : Packet layout randomBound) (valid : ready layout default randomBound value) :
    observed layout randomBound <$> denote layout default randomBound P comparison correct response responseBuffers reserve drawSource value =
      (fun out => (answer layout randomBound value.1 out.1, out.2)) <$>
        ((original respond) (query layout randomBound value.1)).run value.2.val := by
  rw [denote, dite_eq_left valid]
  rcases value with ⟨n | (message | message), saved⟩
  · simp only [serviceRequest, BLSOracle.denote, Sum.elim_inl, UniformQuery.forwardSource, UniformQuery.source,
      Functor.map_map, query]
    rfl
  · have law := BLSDispatch.denote_source layout default P comparison correct response responseBuffers reserve drawSource drawLaw false
      ⟨(message.val, saved.val), ⟨message.property, saved.property⟩, valid⟩
    have mapped := congrArg (fun computation : ProbComp (G × BLSReply.Store (key.Value base) (val.Value base) C G) =>
      (fun out => ((Sum.inr out.1 : (Nat × Nat) ⊕ G), out.2)) <$> computation) law
    simp only [serviceRequest, BLSOracle.denote, Sum.elim_inr, Functor.map_map, observed, finished, replyValue,
      query, answer, original, BLSDispatch.request, LazyAGM.listOracle, StateT.run] at mapped ⊢
    convert mapped using 1
    rfl
  · have law := BLSDispatch.denote_source layout default P comparison correct response responseBuffers reserve drawSource drawLaw true
      ⟨(message.val, saved.val), ⟨message.property, saved.property⟩, valid⟩
    have mapped := congrArg (fun computation : ProbComp (G × BLSReply.Store (key.Value base) (val.Value base) C G) =>
      (fun out => ((Sum.inr out.1 : (Nat × Nat) ⊕ G), out.2)) <$> computation) law
    simp only [serviceRequest, BLSOracle.denote, Sum.elim_inr, Functor.map_map, observed, finished, replyValue,
      query, answer, original, BLSDispatch.request, LazyAGM.listOracle, StateT.run] at mapped ⊢
    convert mapped using 1
    rfl

include drawLaw in
theorem synchronizes (value : Packet layout randomBound) (valid : ready layout default randomBound value) :
    Synchronizes (fun represented source => replyMatches layout randomBound value.1 represented.1 source.1 ∧
      represented.2.val = source.2)
      (denote layout default randomBound P comparison correct response responseBuffers reserve drawSource value)
      (((original respond) (query layout randomBound value.1)).run value.2.val) := by
  have joint := Synchronizes.of_map_eq (observed layout randomBound)
    (fun out : (advSpec (key.Value base) (key.Value base) G).Range (query layout randomBound value.1) ×
      BLSReply.Store (key.Value base) (val.Value base) C G => (answer layout randomBound value.1 out.1, out.2))
    (denote_source layout default randomBound P comparison correct response responseBuffers reserve drawSource drawLaw value valid)
  exact joint.mono (fun _ _ equal => Prod.mk.inj equal)

end Signatures.Runtime.CaliperBackend.BLSCallerHandler
