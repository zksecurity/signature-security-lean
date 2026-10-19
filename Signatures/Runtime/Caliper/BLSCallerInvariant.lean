import Signatures.Runtime.Caliper.BLSCallerSource

/-! The constructed BLS handler consumes one reserved query slot. A represented
message is admitted by construction; cache and transcript room follow from the
existing source reservation invariant and are preserved by the actual handler's
proved source semantics. -/

namespace Signatures.Runtime.CaliperBackend.BLSCallerHandler
open Caliper BoundedSource OracleComp OracleSpec BLSCallerPackets Model.LazyAGM

section Readiness
variable {w : Nat} {M R C G : Type} [DecidableEq M]
    (layout : BLSReply.Layouts w M R C G) (default : layout.cache.value.Value) (randomBound : Nat)

omit [DecidableEq M] in
theorem query_allowed (q : Request layout randomBound) :
    BLSRecord.allowedQuery layout.records (query layout randomBound q) := by
  rcases q with n | (message | message)
  · trivial
  · exact message.property
  · exact message.property

theorem ready_of_reserved (value : Packet layout randomBound) {remaining : Nat}
    (reserved : BLSReply.Reserved layout (remaining + 1) value.2.val) : ready layout default randomBound value := by
  rcases value with ⟨n | (message | message), saved⟩
  · trivial
  · exact (reserved.ready default false message.val message.property).2
  · exact (reserved.ready default true message.val message.property).2

end Readiness

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

include drawLaw in
theorem reserved_after (value : Packet layout randomBound) {remaining : Nat}
    (reserved : BLSReply.Reserved layout (remaining + 1) value.2.val)
    (reply : Reply layout randomBound × layout.store.Value)
    (supported : reply ∈ support (denote layout default randomBound P comparison correct response responseBuffers reserve drawSource value)) :
    BLSReply.Reserved layout remaining reply.2.val := by
  have reached : observed layout randomBound reply ∈ support
      (observed layout randomBound <$> denote layout default randomBound P comparison correct response responseBuffers reserve drawSource value) := by
    rw [support_map]
    exact ⟨reply, supported, rfl⟩
  rw [denote_source layout default randomBound P comparison correct response responseBuffers reserve drawSource drawLaw
    value (ready_of_reserved layout default randomBound value reserved)] at reached
  simp only [original, StateT.run, Functor.map_map, support_map, Set.mem_image] at reached
  obtain ⟨sourceReply, sourceReached, equal⟩ := reached
  have next := BLSReply.query_reserved layout default P comparison correct response responseBuffers reserve drawSource drawLaw
    reserved (query layout randomBound value.1) (query_allowed layout randomBound value.1) sourceReply sourceReached
  have stored : (value.2.val.1, sourceReply.2) = reply.2.val := congrArg Prod.snd equal
  simpa only [stored] using next

end Signatures.Runtime.CaliperBackend.BLSCallerHandler
