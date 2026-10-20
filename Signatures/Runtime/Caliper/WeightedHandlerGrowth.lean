import Signatures.Runtime.Caliper.WeightedHash
import Signatures.Runtime.Caliper.WeightedSign

/-! State growth of the constructed weighted handlers. These facts use the
executed cache/generator semantics and do not assume uniform sampling or
algebraic response laws. They supply the per-query capacity steps. -/
namespace Signatures.Runtime.CaliperBackend
open Caliper BoundedSource OracleComp OracleSpec

namespace WeightedState
variable {K M R C G : Type}

structure Change (before : WeightedHash.Store K M R C G) (answer : G × WeightedHash.Store K M R C G)
    (request : K ⊕ M) (reads : Nat) : Prop where
  config : answer.2.1 = before.1
  cache : answer.2.2.1.length ≤ before.2.1.length + reads
  logs : answer.2.2.2 = WeightedAGM.Reply.record request answer.1 before.2.2

private theorem read_growth {I : Type} {spec : OracleSpec I} [DecidableEq K]
    (draw : OracleComp spec R) (key : K) (cache : List (K × R)) (answer : R × List (K × R))
    (reached : answer ∈ support ((QueryImpl.ListCache.handler (fun _ => draw) key).run cache)) :
    answer.2.length ≤ cache.length + 1 := by
  cases found : cache.lookup key with
  | none =>
    simp only [StateT.run, QueryImpl.ListCache.handler, found, support_map, Set.mem_image] at reached
    obtain ⟨value, _, equal⟩ := reached
    rw [← equal]
    exact le_rfl
  | some value =>
    simp only [StateT.run, QueryImpl.ListCache.handler, found, support_pure, Set.mem_singleton_iff] at reached
    rw [reached]
    exact Nat.le_succ _

end WeightedState

namespace WeightedHash
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M C G : Type}
    [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) M (val.Value base) C G)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {respond : val.Value base × C → G} (response : Implementation .unit layout.responseInput layout.point respond)
    {I : Type} {spec : OracleSpec I}

theorem growth (source : OracleComp spec layout.cache.value.Value) (value : layout.input.Value)
    (answer : layout.output.Value) (reached : answer ∈ support (denote layout P comparison correct response source value)) :
    WeightedState.Change value.val.2 answer.val (.inl value.val.1) 1 := by
  simp only [denote, support_map, Set.mem_image] at reached
  obtain ⟨cached, supported, rfl⟩ := reached
  have exposed : cached.val ∈ support (Subtype.val <$>
      EncodedCacheRead.denote layout.cache P comparison correct source (argument layout value)) := by
    rw [support_map]
    exact ⟨cached, supported, rfl⟩
  rw [EncodedCacheRead.listCache] at exposed
  have grown := WeightedState.read_growth (Subtype.val <$> source) value.val.1 value.val.2.2.1 cached.val exposed
  exact ⟨rfl, grown, rfl⟩
end WeightedHash

namespace WeightedSign
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M F C G : Type}
    [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) M F (val.Value base) C G)
    (zero : layout.evaluation.cache.value.Value)
    (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * (WeightedRows.term layout.evaluation).representation.encoding.words +
      layout.evaluated.representation.encoding.words < 2 ^ w)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit layout.message
      (GeneratedWeighted.terms layout.evaluation capacity countFits storageFits) generate)
    (default : layout.evaluation.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.evaluation.combine layout.evaluation.cache.value combine)
    {updateSlots : Nat} (updateBuffers : update.program.code.memBound ≤ updateSlots)
    (updateReserve : updateSlots + 2 < 2 ^ w)
    {respond : val.Value base × C → G} (response : Implementation .unit layout.responseInput layout.point respond)
    {I : Type} {spec : OracleSpec I}

theorem growth (source : OracleComp spec layout.evaluation.cache.value.Value)
    (value : layout.input.Value) (admitted : valid layout (generate := generate) value)
    (answer : layout.output.Value)
    (reached : answer ∈ support (denote layout zero capacity countFits storageFits generator default P comparison correct
      update updateBuffers updateReserve response source value)) :
    WeightedState.Change value.val.2 answer.val (.inr value.val.1) (generate value.val.1).length := by
  simp only [denote, support_map, Set.mem_image] at reached
  obtain ⟨cached, supported, rfl⟩ := reached
  have grown := GeneratedWeighted.cache_growth layout.evaluation layout.message capacity countFits storageFits generator
    default P comparison correct update updateBuffers updateReserve source (argument layout zero value) admitted cached supported
  exact ⟨rfl, grown, rfl⟩
end WeightedSign

end Signatures.Runtime.CaliperBackend
