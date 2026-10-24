import Proofs.Runtime.Caliper.SchnorrROMPrivatePair

/-! Relative tape bounds for private sampling. The bounds count actual handler
calls and remain valid at early returns and fuel cutoffs. Replay can only shrink
the remaining tape; each fresh call adds at most one saved cell. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape
open Caliper BoundedSource OracleComp OracleSpec

namespace PrivateHandler
variable {w : Nat} {F : Type} [Zero F] (layout : Layouts w F)
    (zeroValid : layout.scalar.valid 0)

theorem tape_lengths (value : Packet layout) (valid : ready layout value)
    (answer : Response layout × Store layout) (reached : answer ∈ support (source layout zeroValid value)) :
    answer.2.val.1.length ≤ value.2.val.1.length + 1 ∧
      answer.2.val.2.length ≤ value.2.val.2.length := by
  obtain ⟨original, supported, related⟩ := (synchronizes layout zeroValid value valid).left_support reached
  have growth := Schnorr.RawTape.Private.oracle_growth value.1.val (stored layout value.2) original supported
  rw [← related.2] at growth
  exact growth
end PrivateHandler

namespace PrivateSampler
variable {w : Nat} {F C : Type} [Zero F] (layout : Layouts w F C)
    (caller : Caller layout) (zeroValid : layout.tape.scalar.valid 0)

theorem Service.tape_lengths (fuel : Nat) (saved : Store layout) (valid : Service.ready layout fuel saved)
    (answer : (Reply.scalarOutput layout.tape).Value)
    (reached : answer ∈ support (Service.source layout caller zeroValid fuel saved)) :
    answer.val.2.1.length ≤ saved.val.1.length + fuel ∧
      answer.val.2.2.length ≤ saved.val.2.length := by
  simp only [Service.source, support_map, Set.mem_image] at reached
  obtain ⟨packet, supported, rfl⟩ := reached
  have bounded := CallerControl.start_store caller.advance (PrivateHandler.source layout.tape zeroValid)
    (fun remaining current => PrivateHandler.Reserved layout.tape remaining current ∧
      current.val.1.length + remaining ≤ saved.val.1.length + fuel ∧
      current.val.2.length ≤ saved.val.2.length)
    (by
      intro small large current fewer room
      dsimp only [PrivateHandler.Reserved] at *
      exact ⟨by omega, by omega, room.2.2⟩)
    (by
      intro remaining query current room reply supported
      have next := PrivateHandler.reserved_after layout.tape zeroValid (query, current) room.1 reply supported
      have growth := PrivateHandler.tape_lengths layout.tape zeroValid (query, current)
        (PrivateHandler.ready_of_reserved layout.tape (query, current) room.1) reply supported
      exact ⟨next, by dsimp only at growth; omega, growth.2.trans room.2.2⟩)
    fuel (caller.initial (Service.unit layout), saved) ⟨valid, le_rfl, le_rfl⟩ packet supported
  change packet.2.val.1.length ≤ saved.val.1.length + fuel ∧ packet.2.val.2.length ≤ saved.val.2.length
  simpa only [Nat.add_zero] using bounded.2

theorem Pair.tape_lengths (fuel : Nat) (saved : Store layout) (valid : Pair.ready layout fuel saved)
    (answer : (Pair.output layout).Value)
    (reached : answer ∈ support (Pair.source layout caller zeroValid fuel saved)) :
    answer.val.2.2.1.length ≤ saved.val.1.length + (fuel + fuel) ∧
      answer.val.2.2.2.length ≤ saved.val.2.length := by
  simp only [Pair.source, support_bind, Set.mem_iUnion, support_map, Set.mem_image] at reached
  obtain ⟨first, supported, second, secondSupported, rfl⟩ := reached
  have firstGrowth := Service.tape_lengths layout caller zeroValid fuel saved
    (Pair.first_ready layout fuel saved valid) first supported
  have secondGrowth := Service.tape_lengths layout caller zeroValid fuel (Pair.unpack layout first).2
    (Pair.second_ready layout caller zeroValid fuel saved valid first supported) second secondSupported
  change second.val.2.1.length ≤ saved.val.1.length + (fuel + fuel) ∧
    second.val.2.2.length ≤ saved.val.2.length
  change second.val.2.1.length ≤ first.val.2.1.length + fuel ∧
    second.val.2.2.length ≤ first.val.2.2.length at secondGrowth
  exact ⟨by omega, secondGrowth.2.trans firstGrowth.2⟩

end PrivateSampler
end Signatures.Runtime.CaliperBackend.SchnorrROMTape
