import Proofs.Runtime.Caliper.WeightedOracleSource
import Proofs.Runtime.Caliper.WeightedCapacity

/-! Per-query invariants of the complete service. The actual generator bounds
signing reads. All random/hash/sign branches consume one reservation and retain
configuration and bounded cache/log growth for caller completion. -/
namespace Signatures.Runtime.CaliperBackend.WeightedOracle
open Caliper BoundedSource OracleComp OracleSpec

abbrev Reserved {w : Nat} {K M F R C G : Type} (layout : Layouts w K M F R C G) (capacity remaining : Nat)
    (store : WeightedHash.Store K M R C G) :=
  WeightedState.Reserved (layout.evaluation.cache.capacityPred + 1) (layout.hashCapacityPred + 1)
    (layout.signCapacityPred + 1) capacity remaining store

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M F C G : Type}
    [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) M F (val.Value base) C G)
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
theorem valid_of_reserved (value : Input layout randomBound) {remaining : Nat}
    (reserved : Reserved layout capacity (remaining + 1) (saved layout randomBound value)) :
    valid layout (generate := generate) randomBound value := by
  rcases value with random | (hashed | signed)
  · trivial
  · trivial
  · have termBound : (generate signed.val.1).length ≤ capacity :=
      (generator.preserves signed.val.1 signed.property.1.1).1
    exact (reserved.sign_room (generate signed.val.1) termBound).1

theorem step (source : ProbComp layout.evaluation.cache.value.Value)
    (value : Input layout randomBound) {remaining : Nat}
    (reserved : Reserved layout capacity (remaining + 1) (saved layout randomBound value))
    (result : Output layout randomBound)
    (reached : result ∈ support (denote layout capacity countFits storageFits generator randomBound P comparison correct
      update updateBuffers updateReserve response source value)) :
    Reserved layout capacity remaining (returned layout randomBound result).val ∧
      (returned layout randomBound result).val.1 = (saved layout randomBound value).1 ∧
      (returned layout randomBound result).val.2.1.length ≤ (saved layout randomBound value).2.1.length + max 1 capacity ∧
      (returned layout randomBound result).val.2.2.1.length + (returned layout randomBound result).val.2.2.2.length ≤
        (saved layout randomBound value).2.2.1.length + (saved layout randomBound value).2.2.2.length + 1 := by
  rcases value with random | (hashed | signed)
  · simp only [denote, Sum.elim_inl, support_map, Set.mem_image] at reached
    obtain ⟨reply, supported, rfl⟩ := reached
    simp only [UniformQuery.forwardSource, support_map, Set.mem_image] at supported
    obtain ⟨sample, _, rfl⟩ := supported
    exact ⟨reserved.weaken (Nat.le_succ _), rfl, Nat.le_add_right _ _, Nat.le_succ _⟩
  · simp only [denote, groupDenote, Sum.elim_inr, support_map, Set.mem_image] at reached
    obtain ⟨reply, supported, rfl⟩ := reached
    have changed := WeightedHash.growth layout.hashing P comparison correct (response false) source hashed reply supported
    refine ⟨changed.reserved_after reserved (Nat.le_max_left _ _), changed.config,
      changed.cache.trans (Nat.add_le_add_left (Nat.le_max_left _ _) _), ?_⟩
    change reply.val.2.2.2.1.length + reply.val.2.2.2.2.length ≤
      hashed.val.2.2.2.1.length + hashed.val.2.2.2.2.length + 1
    rw [changed.logs]
    simp only [WeightedAGM.Reply.record, List.length_cons]
    omega
  · simp only [denote, groupDenote, Sum.elim_inr, support_map, Set.mem_image] at reached
    obtain ⟨reply, supported, rfl⟩ := reached
    have termBound : (generate signed.val.1).length ≤ capacity :=
      (generator.preserves signed.val.1 signed.property.1.1).1
    have changed := WeightedSign.growth layout.signing layout.zero capacity countFits storageFits generator layout.default
      P comparison correct update updateBuffers updateReserve (response true) source signed
      (reserved.sign_room (generate signed.val.1) termBound).1 reply supported
    have reads : (generate signed.val.1).length ≤ max 1 capacity := termBound.trans (Nat.le_max_right _ _)
    refine ⟨changed.reserved_after reserved reads, changed.config,
      changed.cache.trans (Nat.add_le_add_left reads _), ?_⟩
    change reply.val.2.2.2.1.length + reply.val.2.2.2.2.length ≤
      signed.val.2.2.2.1.length + signed.val.2.2.2.2.length + 1
    rw [changed.logs]
    simp only [WeightedAGM.Reply.record, List.length_cons]
    omega

end Signatures.Runtime.CaliperBackend.WeightedOracle
