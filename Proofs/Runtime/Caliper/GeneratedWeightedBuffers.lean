import Proofs.Runtime.Caliper.GeneratedWeightedBounds

/-! Buffer names depend on component footprints, not the unrolled term count.
This supplies the address reservation for retaining a complete evaluator. -/
namespace Signatures.Runtime.CaliperBackend
open Caliper BoundedSource

namespace GeneratedWeighted
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {F M : Type}
    [DecidableEq (key.Value base)]
    (layout : CacheAccumulate.Layouts w (key.Value base) F (val.Value base))
    (domain : Layout w M) (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * (WeightedRows.term layout).representation.encoding.words +
      (WeightedRows.rows layout).state.representation.encoding.words < 2 ^ w)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit domain (terms layout capacity countFits storageFits) generate)
    {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    (default : layout.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.combine layout.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    (draw : Interactive.Code w)

theorem buffers :
    ((code layout domain capacity countFits storageFits generator port default P comparison correct
      update updateBuffers reserve draw).lower port).memBound ≤
      max (max 2 generator.program.code.memBound + 1)
        (max 2 (max (max 8 ((draw.lower port).memBound + 1) + 1) (max 4 slots + 1)) + 1) := by
  have prepared := Interactive.retain_buffers port (.compute generator.program.code)
    domain.representation.encoding.words (terms layout capacity countFits storageFits).representation.encoding.words
    (WeightedRows.rows layout).state.representation.encoding.words
  have body := RowEvaluation.buffers (WeightedRows.rows layout) default P comparison correct update updateBuffers reserve port draw
  have folded := InteractiveFold.buffers port
    (RowEvaluation.code (WeightedRows.rows layout) default P comparison correct update updateBuffers reserve port draw)
    (WeightedRows.rows layout).row.representation.encoding.words
    (WeightedRows.rows layout).state.representation.encoding.words capacity
  change ((prepare layout domain capacity countFits storageFits generator port).lower port).memBound ≤
    max 2 generator.program.code.memBound + 1 at prepared
  change ((WeightedRows.code layout default P comparison correct update updateBuffers reserve capacity port draw).lower port).memBound ≤ _ at folded
  change max ((prepare layout domain capacity countFits storageFits generator port).lower port).memBound
    ((WeightedRows.code layout default P comparison correct update updateBuffers reserve capacity port draw).lower port).memBound ≤ _
  exact max_le (prepared.trans (Nat.le_max_left _ _)) (folded.trans (by omega))

theorem savedNameFits {generatorSlots drawSlots : Nat}
    (generatorBound : generator.program.code.memBound ≤ generatorSlots) (generatorReserve : generatorSlots + 1 < 2 ^ w)
    (drawBound : WordIO.NamesBound (draw.lower port) drawSlots) (drawReserve : drawSlots + 3 < 2 ^ w) :
    Interactive.savedBuffer port
      (code layout domain capacity countFits storageFits generator port default P comparison correct
        update updateBuffers reserve draw) < 2 ^ w := by
  have bound := buffers layout domain capacity countFits storageFits generator port default P comparison correct
    update updateBuffers reserve draw
  have sampler := drawBound.buffers
  have hw := layout.cache.wordFits
  unfold Interactive.savedBuffer
  omega
end GeneratedWeighted
end Signatures.Runtime.CaliperBackend
