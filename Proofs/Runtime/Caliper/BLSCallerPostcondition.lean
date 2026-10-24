import Proofs.Runtime.Caliper.BLSCallerInvariant
import Proofs.Runtime.Caliper.CallerPostcondition

/-! Derived cache/transcript growth at caller completion. Cache space for
extraction is independent of transcript space: private extraction reads need
cache entries, but do not add caller transcript tokens. -/

namespace Signatures.Runtime.CaliperBackend
open Caliper BoundedSource OracleComp OracleSpec BLSCallerPackets Model.LazyAGM

namespace BLSCaller
section Store
variable {w : Nat} {M R C G : Type} (service : BLSReply.Layouts w M R C G)

/-- Sizes and configuration retained at any caller exit. The reserved predicate
also retains entry-domain validity; it does not demand spare transcript slots. -/
structure Postcondition (fuel : Nat) (before after : service.store.Value) : Prop where
  reserved : BLSReply.Reserved service 0 after.val
  config : after.val.1 = before.val.1
  cache : after.val.2.1.length ≤ before.val.2.1.length + fuel
  logs : after.val.2.2.1.length + after.val.2.2.2.length ≤
    before.val.2.2.1.length + before.val.2.2.2.length + fuel

/-- One private read per stored token plus the final message fits. From an empty
store this needs cache capacity `2*fuel + 1`, and only `fuel` log capacity. -/
theorem Postcondition.extraction_room {service : BLSReply.Layouts w M R C G} {fuel : Nat} {before after : service.store.Value}
    (post : Postcondition service fuel before after)
    (room : before.val.2.1.length + before.val.2.2.1.length + before.val.2.2.2.length + 2 * fuel + 1 ≤
      service.cache.capacityPred + 1) :
    after.val.2.1.length + (after.val.2.2.1.length + after.val.2.2.2.length + 1) ≤ service.cache.capacityPred + 1 := by
  have := post.cache
  have := post.logs
  omega


end Store
end BLSCaller

variable {w : Nat} {C G A B : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    (service : BLSReply.Layouts w (key.Value base) (val.Value base) C G)
    (default : service.cache.value.Value) (randomBound : Nat)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op) (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit service.responseInput service.point (respond signing))
    {slots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w)
    (drawSource : ProbComp service.cache.value.Value)
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include drawLaw in
theorem BLSCallerHandler.growth (value : Packet service randomBound)
    (valid : ready service default randomBound value)
    (reply : Reply service randomBound × service.store.Value)
    (supported : reply ∈ support (BLSCallerHandler.denote service default randomBound P comparison correct response responseBuffers reserve drawSource value)) :
    reply.2.val.1 = value.2.val.1 ∧
    reply.2.val.2.1.length ≤ value.2.val.2.1.length + 1 ∧
    reply.2.val.2.2.1.length + reply.2.val.2.2.2.length ≤
      value.2.val.2.2.1.length + value.2.val.2.2.2.length + 1 := by
  obtain ⟨original, reached, related⟩ := (BLSCallerHandler.synchronizes service default randomBound P comparison correct response
    responseBuffers reserve drawSource drawLaw value valid).left_support supported
  simp only [BLSCallerHandler.original, StateT.run, support_map, Set.mem_image] at reached
  obtain ⟨sourceReply, sourceReached, equal⟩ := reached
  have stored : reply.2.val = (value.2.val.1, sourceReply.2) := related.2.trans (congrArg Prod.snd equal).symm
  have growth := LazyAGM.listOracle_growth
    (fun sample => respond false (sample, value.2.val.1)) (fun sample => respond true (sample, value.2.val.1))
    (BLSCallerHandler.query service randomBound value.1) value.2.val.2 sourceReply sourceReached
  rw [stored]
  exact ⟨rfl, growth⟩

namespace BLSCaller

include drawLaw in
theorem start_postcondition (advance : A × Reply service randomBound → B ⊕ (Request service randomBound × A))
    (fuel : Nat) (value : CallerControl.Packet A (Request service randomBound) B service.store.Value)
    (reserved : BLSReply.Reserved service fuel value.2.val)
    (answer) (reached : answer ∈ support (CallerControl.start advance
      (BLSCallerHandler.denote service default randomBound P comparison correct response responseBuffers reserve drawSource) fuel value)) :
    Postcondition service fuel value.2 answer.2 := by
  let invariant (remaining : Nat) (saved : service.store.Value) : Prop :=
    BLSReply.Reserved service remaining saved.val ∧ saved.val.1 = value.2.val.1 ∧
      saved.val.2.1.length + remaining ≤ value.2.val.2.1.length + fuel ∧
      saved.val.2.2.1.length + saved.val.2.2.2.length + remaining ≤
        value.2.val.2.2.1.length + value.2.val.2.2.2.length + fuel
  have weaken : ∀ small large saved, small ≤ large → invariant large saved → invariant small saved := by
    intro small large saved bound valid
    exact ⟨valid.1.weaken bound, valid.2.1, by have := valid.2.2.1; omega,
      by have := valid.2.2.2; omega⟩
  have step : ∀ remaining q saved, invariant (remaining + 1) saved →
      ∀ reply ∈ support (BLSCallerHandler.denote service default randomBound P comparison correct response responseBuffers reserve drawSource (q, saved)),
        invariant remaining reply.2 := by
    intro remaining q saved valid reply supported
    have next := BLSCallerHandler.reserved_after service default randomBound P comparison correct response responseBuffers reserve
      drawSource drawLaw (q, saved) valid.1 reply supported
    have growth := BLSCallerHandler.growth service default randomBound P comparison correct response responseBuffers reserve
      drawSource drawLaw (q, saved) (BLSCallerHandler.ready_of_reserved service default randomBound (q, saved) valid.1) reply supported
    dsimp only [Prod.fst, Prod.snd] at growth
    exact ⟨next, growth.1.trans valid.2.1, by have := valid.2.2.1; have := growth.2.1; omega,
      by have := valid.2.2.2; have := growth.2.2; omega⟩
  have final := CallerControl.start_store advance
    (BLSCallerHandler.denote service default randomBound P comparison correct response responseBuffers reserve drawSource)
    invariant weaken step fuel value ⟨reserved, rfl, le_rfl, le_rfl⟩ answer reached
  exact ⟨final.1, final.2.1, by simpa using final.2.2.1, by simpa using final.2.2.2⟩


end BLSCaller
end Signatures.Runtime.CaliperBackend
