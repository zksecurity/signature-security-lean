import Proofs.Runtime.Caliper.WeightedHandlerGrowth

/-! Query reservations for weighted services. Private cache and the two reply
logs have independent capacities. A query reserves at most the larger of one
private read and one generated term list; no domain cardinality occurs. -/
namespace Signatures.Runtime.CaliperBackend.WeightedState
open Caliper BoundedSource
variable {K M R C G : Type}

structure Reserved (cacheCapacity hashCapacity signCapacity termBound remaining : Nat)
    (store : WeightedHash.Store K M R C G) : Prop where
  cache : store.2.1.length + max 1 termBound * remaining ≤ cacheCapacity
  hashes : store.2.2.1.length + remaining ≤ hashCapacity
  signatures : store.2.2.2.length + remaining ≤ signCapacity

theorem Reserved.weaken {cacheCapacity hashCapacity signCapacity termBound small large : Nat}
    {store : WeightedHash.Store K M R C G}
    (reserved : Reserved cacheCapacity hashCapacity signCapacity termBound large store) (bound : small ≤ large) :
    Reserved cacheCapacity hashCapacity signCapacity termBound small store := by
  have scaled := Nat.mul_le_mul_left (max 1 termBound) bound
  exact ⟨by have := reserved.cache; omega, by have := reserved.hashes; omega,
    by have := reserved.signatures; omega⟩

theorem Reserved.room {cacheCapacity hashCapacity signCapacity termBound remaining reads : Nat}
    {store : WeightedHash.Store K M R C G}
    (reserved : Reserved cacheCapacity hashCapacity signCapacity termBound (remaining + 1) store)
    (bounded : reads ≤ max 1 termBound) :
    store.2.1.length + reads ≤ cacheCapacity ∧
      store.2.2.1.length < hashCapacity ∧ store.2.2.2.length < signCapacity := by
  have cache := reserved.cache
  have hashes := reserved.hashes
  have signatures := reserved.signatures
  rw [Nat.mul_succ] at cache
  omega

theorem Change.reserved_after {cacheCapacity hashCapacity signCapacity termBound remaining reads : Nat}
    {before : WeightedHash.Store K M R C G} {answer : G × WeightedHash.Store K M R C G} {request : K ⊕ M}
    (changed : Change before answer request reads)
    (reserved : Reserved cacheCapacity hashCapacity signCapacity termBound (remaining + 1) before)
    (bounded : reads ≤ max 1 termBound) :
    Reserved cacheCapacity hashCapacity signCapacity termBound remaining answer.2 := by
  have cache := reserved.cache
  have hashes := reserved.hashes
  have signatures := reserved.signatures
  have grew := changed.cache
  have logs := changed.logs
  rw [Nat.mul_succ] at cache
  constructor
  · omega
  · cases request <;> rw [logs] <;>
      simp only [WeightedAGM.Reply.record, List.length_cons] <;> omega
  · cases request <;> rw [logs] <;>
      simp only [WeightedAGM.Reply.record, List.length_cons] <;> omega

theorem Reserved.empty (config : C) (cacheCapacity hashCapacity signCapacity termBound queries : Nat)
    (cache : max 1 termBound * queries ≤ cacheCapacity)
    (hashes : queries ≤ hashCapacity) (signatures : queries ≤ signCapacity) :
    Reserved cacheCapacity hashCapacity signCapacity termBound queries
      (config, ([] : List (K × R)), ([] : List (K × G)), ([] : List (M × G))) := by
  exact ⟨by simpa using cache, by simpa using hashes, by simpa using signatures⟩

/-- The generated term list fits before signing, while hash and signing logs
each retain a free entry. These are the arithmetic facts used to form inputs. -/
theorem Reserved.sign_room {cacheCapacity hashCapacity signCapacity termBound remaining : Nat}
    {store : WeightedHash.Store K M R C G} {F : Type} (terms : List (K × F))
    (reserved : Reserved cacheCapacity hashCapacity signCapacity termBound (remaining + 1) store)
    (bounded : terms.length ≤ termBound) :
    store.2.1.length + terms.length ≤ cacheCapacity ∧
      store.2.2.1.length < hashCapacity ∧ store.2.2.2.length < signCapacity :=
  reserved.room (bounded.trans (Nat.le_max_right _ _))

theorem Reserved.hash_room {cacheCapacity hashCapacity signCapacity termBound remaining : Nat}
    {store : WeightedHash.Store K M R C G}
    (reserved : Reserved cacheCapacity hashCapacity signCapacity termBound (remaining + 1) store) :
    store.2.1.length + 1 ≤ cacheCapacity ∧
      store.2.2.1.length < hashCapacity ∧ store.2.2.2.length < signCapacity :=
  reserved.room (Nat.le_max_left _ _)

end Signatures.Runtime.CaliperBackend.WeightedState
