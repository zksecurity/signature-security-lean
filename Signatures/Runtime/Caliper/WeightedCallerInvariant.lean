import Signatures.Runtime.Caliper.WeightedCallerHandler
import Signatures.Runtime.Caliper.WeightedOracleInvariant

/-! Reservations supply caller admission and are preserved by the constructed
handler. Its full store postcondition supports subsequent caller completion
and extraction; random calls leave configuration, cache and logs unchanged. -/
namespace Signatures.Runtime.CaliperBackend.WeightedCallerHandler
open Caliper BoundedSource OracleComp OracleSpec WeightedCallerPackets

section Views
variable {w : Nat} {K M F R C G : Type} [DecidableEq K]
    (layout : WeightedOracle.Layouts w K M F R C G) (randomBound : Nat) (generate : M → List (K × F))

theorem saved_request (value : Packet layout randomBound) (accepted : ready layout randomBound generate value) :
    WeightedOracle.saved layout randomBound (serviceRequest layout randomBound generate value accepted) = value.2.val := by
  rcases value with ⟨n | (index | message), saved⟩ <;> rfl

omit [DecidableEq K] in
theorem saved_finished (value : WeightedOracle.Output layout randomBound) :
    (finished layout randomBound value).2 = WeightedOracle.returned layout randomBound value := by
  cases value <;> rfl
end Views

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M F C G : Type}
    [DecidableEq (key.Value base)]
    (layout : WeightedOracle.Layouts w (key.Value base) M F (val.Value base) C G)
    (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * (WeightedRows.term layout.evaluation).representation.encoding.words +
      layout.signing.evaluated.representation.encoding.words < 2 ^ w)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit layout.message
      (GeneratedWeighted.terms layout.evaluation capacity countFits storageFits) generate)
    (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.evaluation.combine layout.evaluation.cache.value combine)
    {updateSlots : Nat} (updateBuffers : update.program.code.memBound ≤ updateSlots) (updateReserve : updateSlots + 2 < 2 ^ w)
    (draw : Interactive.Code w)
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit layout.responseInput layout.point (respond signing))
    {responseSlots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ responseSlots)
    (responseReserve : responseSlots < 2 ^ w)

include generator in
theorem ready_of_reserved (value : Packet layout randomBound) {remaining : Nat}
    (reserved : WeightedOracle.Reserved layout capacity (remaining + 1) value.2.val) :
    ready layout randomBound generate value := by
  rcases value with ⟨n | (index | message), saved⟩
  · trivial
  · change WeightedOracle.Reserved layout capacity (remaining + 1) saved.val at reserved
    have room := reserved.hash_room
    refine ⟨?_, ?_⟩
    · intro _
      change saved.val.2.1.length ≤ layout.evaluation.cache.capacityPred
      have := room.1
      omega
    · change saved.val.2.2.1.length ≤ layout.hashCapacityPred
      have := room.2.1
      omega
  · change WeightedOracle.Reserved layout capacity (remaining + 1) saved.val at reserved
    have termBound : (generate message.val).length ≤ capacity := (generator.preserves message.val message.property).1
    have room := reserved.sign_room (generate message.val) termBound
    refine ⟨?_, room.1⟩
    change saved.val.2.2.2.length ≤ layout.signCapacityPred
    have := room.2.2
    omega

theorem step (source : ProbComp layout.evaluation.cache.value.Value)
    (value : Packet layout randomBound) {remaining : Nat}
    (reserved : WeightedOracle.Reserved layout capacity (remaining + 1) value.2.val)
    (result : Reply layout randomBound × layout.store.Value)
    (reached : result ∈ support (denote layout capacity countFits storageFits generator randomBound P comparison correct
      update updateBuffers updateReserve response source value)) :
    WeightedOracle.Reserved layout capacity remaining result.2.val ∧
      result.2.val.1 = value.2.val.1 ∧
      result.2.val.2.1.length ≤ value.2.val.2.1.length + max 1 capacity ∧
      result.2.val.2.2.1.length + result.2.val.2.2.2.length ≤ value.2.val.2.2.1.length + value.2.val.2.2.2.length + 1 := by
  have accepted := ready_of_reserved layout capacity countFits storageFits generator randomBound value reserved
  rw [denote, dite_eq_left accepted] at reached
  simp only [support_map, Set.mem_image] at reached
  obtain ⟨answer, supported, rfl⟩ := reached
  have serviceReserved : WeightedOracle.Reserved layout capacity (remaining + 1)
      (WeightedOracle.saved layout randomBound (serviceRequest layout randomBound generate value accepted)) := by
    rwa [saved_request]
  have next := WeightedOracle.step layout capacity countFits storageFits generator randomBound P comparison correct
    update updateBuffers updateReserve response source (serviceRequest layout randomBound generate value accepted) serviceReserved answer supported
  simpa only [saved_request, saved_finished] using next

end Signatures.Runtime.CaliperBackend.WeightedCallerHandler
