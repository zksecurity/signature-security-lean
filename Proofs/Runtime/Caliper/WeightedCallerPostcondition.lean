import Proofs.Runtime.Caliper.WeightedCallerInvariant
import Proofs.Runtime.Caliper.CallerPostcondition

/-! Configuration, cache and reply-log bounds retained at every caller exit,
including early return and cutoff. Extraction headroom is reserved only in the
private cache; expansion need not reserve new hash or signature reply slots. -/
namespace Signatures.Runtime.CaliperBackend.WeightedCaller
open Caliper BoundedSource OracleComp OracleSpec WeightedCallerPackets

section Store
variable {w : Nat} {K M F R C G : Type} (service : WeightedOracle.Layouts w K M F R C G)

structure Postcondition (capacity fuel : Nat) (before after : service.store.Value) : Prop where
  reserved : WeightedOracle.Reserved service capacity 0 after.val
  config : after.val.1 = before.val.1
  cache : after.val.2.1.length ≤ before.val.2.1.length + max 1 capacity * fuel
  logs : after.val.2.2.1.length + after.val.2.2.2.length ≤
    before.val.2.2.1.length + before.val.2.2.2.length + fuel

/-- Room for at most `max(1,capacity)` private reads per retained reply and one
final term list. The later extractor must establish that it meets this count. -/
theorem Postcondition.extraction_room {service : WeightedOracle.Layouts w K M F R C G}
    {capacity fuel : Nat} {before after : service.store.Value}
    (post : Postcondition service capacity fuel before after)
    (room : before.val.2.1.length + max 1 capacity *
      (before.val.2.2.1.length + before.val.2.2.2.length + 2 * fuel + 1) ≤ service.evaluation.cache.capacityPred + 1) :
    after.val.2.1.length + max 1 capacity * (after.val.2.2.1.length + after.val.2.2.2.length + 1) ≤
      service.evaluation.cache.capacityPred + 1 := by
  calc
    _ ≤ (before.val.2.1.length + max 1 capacity * fuel) + max 1 capacity *
        (before.val.2.2.1.length + before.val.2.2.2.length + fuel + 1) :=
      Nat.add_le_add post.cache (Nat.mul_le_mul_left _ (Nat.add_le_add_right post.logs 1))
    _ = before.val.2.1.length + max 1 capacity *
        (before.val.2.2.1.length + before.val.2.2.2.length + 2 * fuel + 1) := by ring
    _ ≤ _ := room
end Store

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M F C G A B : Type}
    [DecidableEq (key.Value base)]
    (service : WeightedOracle.Layouts w (key.Value base) M F (val.Value base) C G)
    (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * (WeightedRows.term service.evaluation).representation.encoding.words +
      service.signing.evaluated.representation.encoding.words < 2 ^ w)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit service.message
      (GeneratedWeighted.terms service.evaluation capacity countFits storageFits) generate)
    (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit service.evaluation.combine service.evaluation.cache.value combine)
    {updateSlots : Nat} (updateBuffers : update.program.code.memBound ≤ updateSlots) (updateReserve : updateSlots + 2 < 2 ^ w)
    (draw : Interactive.Code w)
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit service.responseInput service.point (respond signing))
    {responseSlots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ responseSlots)
    (responseReserve : responseSlots < 2 ^ w)

theorem start_postcondition (source : ProbComp service.evaluation.cache.value.Value)
    (advance : A × Reply service randomBound → B ⊕ (Request service randomBound × A))
    (fuel : Nat) (value : CallerControl.Packet A (Request service randomBound) B service.store.Value)
    (reserved : WeightedOracle.Reserved service capacity fuel value.2.val)
    (answer) (reached : answer ∈ support (CallerControl.start advance
      (WeightedCallerHandler.denote service capacity countFits storageFits generator randomBound P comparison correct update updateBuffers updateReserve response source) fuel value)) :
    Postcondition service capacity fuel value.2 answer.2 := by
  let invariant (remaining : Nat) (saved : service.store.Value) : Prop :=
    WeightedOracle.Reserved service capacity remaining saved.val ∧ saved.val.1 = value.2.val.1 ∧
      saved.val.2.1.length + max 1 capacity * remaining ≤ value.2.val.2.1.length + max 1 capacity * fuel ∧
      saved.val.2.2.1.length + saved.val.2.2.2.length + remaining ≤
        value.2.val.2.2.1.length + value.2.val.2.2.2.length + fuel
  have weaken : ∀ small large saved, small ≤ large → invariant large saved → invariant small saved := by
    intro small large saved bound valid
    have scaled := Nat.mul_le_mul_left (max 1 capacity) bound
    exact ⟨valid.1.weaken bound, valid.2.1, by have := valid.2.2.1; omega, by have := valid.2.2.2; omega⟩
  have step : ∀ remaining q saved, invariant (remaining + 1) saved →
      ∀ reply ∈ support (WeightedCallerHandler.denote service capacity countFits storageFits generator randomBound P comparison correct update updateBuffers updateReserve response source (q, saved)), invariant remaining reply.2 := by
    intro remaining q saved valid reply supported
    have next := WeightedCallerHandler.step service capacity countFits storageFits generator randomBound P comparison correct update updateBuffers updateReserve response source (q, saved) valid.1 reply supported
    dsimp only [Prod.fst, Prod.snd] at next
    refine ⟨next.1, next.2.1.trans valid.2.1, ?_, ?_⟩
    · have previous := valid.2.2.1
      rw [Nat.mul_succ] at previous
      have grew := next.2.2.1
      omega
    · have previous := valid.2.2.2
      have grew := next.2.2.2
      omega
  have final := CallerControl.start_store advance (WeightedCallerHandler.denote service capacity countFits storageFits generator randomBound P comparison correct update updateBuffers updateReserve response source)
    invariant weaken step fuel value ⟨reserved, rfl, le_rfl, le_rfl⟩ answer reached
  exact ⟨final.1, final.2.1, by simpa using final.2.2.1, by simpa using final.2.2.2⟩

end Signatures.Runtime.CaliperBackend.WeightedCaller
