import Signatures.Runtime.Caliper.SchnorrAGMCaller
import Signatures.Runtime.Caliper.CallerPostcondition

/-! Every caller exit retains a canonical source state, the runtime public
configuration and one cache slot for final extraction, including early returns
and fuel cutoffs. Hash/sign allowances remain independent. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Caller
open Caliper BoundedSource OracleComp OracleSpec CallerPackets
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS randomBound : Nat} {M F G A B : Type} [Field F]
    (service : Handler.Layouts w M F G qH qS randomBound)

structure Postcondition (before after : service.scheme.store.Value) : Prop where
  reserved : CallerHandler.Reserved service 0 0 after
  config : after.val.1 = before.val.1

theorem Postcondition.extraction_room {before after : service.scheme.store.Value} (post : Postcondition service before after) :
    after.val.2.1.length + 1 ≤ qH + qS + 1 := by
  obtain ⟨state, encoded, room⟩ := post.reserved
  rw [encoded]
  change (state.cache.map _).length + 1 ≤ qH + qS + 1
  rw [List.length_map]
  simpa only [Nat.add_zero] using room.2.1

variable [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq M] [DecidableEq G] [SampleableType F]
    (ops : Handler.Operations service) (sampleSource : ProbComp service.scheme.scalar.Value)
    (uniform : Subtype.val <$> sampleSource = ($ᵗ F : ProbComp F))
    (domain : Nat → Nat → Nat → Request service × A → Prop)
    (allowed : ∀ remaining hashes signatures q c, domain (remaining + 1) hashes signatures (q, c) →
      CallerHandler.Allowed service hashes signatures q)
    (advance : A × Reply service → B ⊕ (Request service × A))
    (advanceValid : ∀ remaining hashes signatures q c, domain (remaining + 1) hashes signatures (q, c) →
      ∀ represented original, CallerHandler.replyMatches service q represented original →
        HeadValid service domain remaining (hashes - CallerHandler.hashCharge service q) (signatures - CallerHandler.signCharge service q)
          (advance (c, represented)))

include uniform allowed advanceValid in
theorem start_postcondition (fuel : Nat)
    (value : CallerControl.Packet A (Request service) B service.scheme.store.Value)
    (valid : CallerControl.Valid (Invariant service domain) fuel value)
    (reserved : CallerHandler.Reserved service 0 0 value.2)
    (answer) (reached : answer ∈ support (CallerControl.start advance (CallerHandler.source service ops sampleSource) fuel value)) :
    Postcondition service value.2 answer.2 := by
  apply CallerControl.start_store_on advance (CallerHandler.source service ops sampleSource) (Invariant service domain)
    (preserves service ops sampleSource uniform domain allowed advance advanceValid) (Postcondition service value.2)
    _ fuel value valid ⟨reserved, rfl⟩ answer reached
  intro remaining frame invariant post reply supported
  obtain ⟨hashes, signatures, localValid, room⟩ := invariant
  have permitted := allowed remaining hashes signatures _ _ localValid
  have next := CallerHandler.reserved_after service ops sampleSource uniform (frame.1.1, frame.2) room permitted reply supported
  obtain ⟨state, encoded, reserved⟩ := room
  have ready := CallerHandler.ready_of_reserved service (frame.1.1, frame.2) ⟨state, encoded, reserved⟩ permitted
  obtain ⟨original, _, related⟩ := (CallerHandler.synchronizes service ops sampleSource uniform
    (frame.1.1, frame.2) ready state encoded).left_support supported
  exact ⟨CallerHandler.Reserved.mono service next (Nat.zero_le _) (Nat.zero_le _),
    (congrArg Prod.fst related.2).trans post.config⟩

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Caller
