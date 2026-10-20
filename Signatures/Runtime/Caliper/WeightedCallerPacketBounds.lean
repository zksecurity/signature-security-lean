import Signatures.Runtime.Caliper.WeightedCallerPackets

/-! Linear overhead of the actual weighted caller packet converters, including stored
branches, copied private state and zero padding. -/

namespace Signatures.Runtime.CaliperBackend.WeightedCallerPackets
open Caliper BoundedSource

variable {w : Nat} {K M F R C G : Type}
    (layout : WeightedOracle.Layouts w K M F R C G) (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)

theorem widths :
    (input layout randomBound randomFits).encoding.words ≤ width layout ∧
    (groupInput layout).encoding.words ≤ width layout ∧
    (groupOutput layout).encoding.words ≤ width layout ∧
    (layout.randomInput randomBound randomFits).encoding.words ≤ width layout ∧
    (raw layout randomBound randomFits).encoding.words ≤ width layout ∧
    (output layout randomBound randomFits).encoding.words ≤ width layout := by
  change 1 + max 1 (1 + max layout.evaluation.cache.key.representation.encoding.words layout.message.representation.encoding.words) + _ ≤ _ ∧
    (1 + max layout.evaluation.cache.key.representation.encoding.words layout.message.representation.encoding.words) + _ ≤ _ ∧
    1 + max (layout.evaluation.cache.key.representation.encoding.words + layout.store.representation.encoding.words)
      (layout.message.representation.encoding.words + layout.store.representation.encoding.words) ≤ _ ∧
    1 + layout.store.representation.encoding.words ≤ _ ∧
    1 + max (1 + layout.store.representation.encoding.words)
      (1 + max (layout.evaluation.cache.key.representation.encoding.words + layout.store.representation.encoding.words)
        (layout.message.representation.encoding.words + layout.store.representation.encoding.words)) ≤ _ ∧
    1 + max 2 layout.point.representation.encoding.words + layout.store.representation.encoding.words ≤ _
  dsimp only [width]
  omega

theorem prepare_time (value : Packet layout randomBound) :
    (prepare layout randomBound randomFits).time value ≤ 64 * width layout + 6 := by
  have sizes := widths layout randomBound randomFits
  have outer := SumContext.time (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits).request
    (groupRequest layout) layout.store.representation layout.evaluation.cache.wordFits (input layout randomBound randomFits).fits value
  change _ ≤ 24 * (input layout randomBound randomFits).encoding.words + 2 at outer
  rcases value with ⟨n | group, saved⟩
  · have tag := inl_time (layout.randomInput randomBound randomFits) (groupOutput layout)
      layout.evaluation.cache.wordFits (raw layout randomBound randomFits).fits (n, saved)
    change _ ≤ 8 * (raw layout randomBound randomFits).encoding.words at tag
    change _ + (1 + (1 + ((selectSlice (w := w) 1 (layout.randomInput randomBound randomFits).encoding.words).staticTime .unit + _))) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, CostModel.unit]
    dsimp only [CostModel.unit] at outer tag
    dsimp only [inlRealizer, Assembly.realizer] at tag ⊢
    omega
  · have inner := SumContext.time layout.evaluation.cache.key.representation layout.message.representation
      layout.store.representation layout.evaluation.cache.wordFits (groupInput layout).fits (group, saved)
    have tag := inr_time (layout.randomInput randomBound randomFits) (groupOutput layout)
      layout.evaluation.cache.wordFits (raw layout randomBound randomFits).fits (SumContext.view (group, saved))
    change _ ≤ 24 * (groupInput layout).encoding.words + 2 at inner
    change _ ≤ 8 * (raw layout randomBound randomFits).encoding.words at tag
    change _ + (1 + (1 + ((selectSlice (w := w) 1 (groupInput layout).encoding.words).staticTime .unit + (_ + _)))) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, CostModel.unit]
    dsimp only [CostModel.unit] at outer inner tag
    omega

theorem prepare_words : descriptionWords (prepare layout randomBound randomFits).code ≤ 420 * width layout + 270 := by
  have sizes := widths layout randomBound randomFits
  have outer := SumContext.words (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits).request
    (groupRequest layout) layout.store.representation layout.evaluation.cache.wordFits (input layout randomBound randomFits).fits
  have inner := SumContext.words layout.evaluation.cache.key.representation layout.message.representation
    layout.store.representation layout.evaluation.cache.wordFits (groupInput layout).fits
  have left := inl_words (layout.randomInput randomBound randomFits) (groupOutput layout)
    layout.evaluation.cache.wordFits (raw layout randomBound randomFits).fits
  have right := inr_words (layout.randomInput randomBound randomFits) (groupOutput layout)
    layout.evaluation.cache.wordFits (raw layout randomBound randomFits).fits
  change _ ≤ 156 * (input layout randomBound randomFits).encoding.words + 95 at outer
  change _ ≤ 156 * (groupInput layout).encoding.words + 95 at inner
  change _ ≤ 26 * (raw layout randomBound randomFits).encoding.words + 14 at left right
  change descriptionWords (_ ;; Dispatch.code _ (_ ;; _) (layout.randomInput randomBound randomFits).encoding.words
    (groupInput layout).encoding.words) ≤ _
  rw [descriptionWords_seq, Dispatch.code_descriptionWords, descriptionWords_seq]
  omega

theorem prepare_names : NamesAccounted (prepare layout randomBound randomFits).code 3 :=
  (SumContext.names (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits).request
    (groupRequest layout) layout.store.representation layout.evaluation.cache.wordFits (input layout randomBound randomFits).fits).seq
      (Dispatch.names (inl_names _ _ layout.evaluation.cache.wordFits (raw layout randomBound randomFits).fits).accounted
        ((SumContext.names layout.evaluation.cache.key.representation layout.message.representation layout.store.representation
          layout.evaluation.cache.wordFits (groupInput layout).fits).seq
            (inr_names _ _ layout.evaluation.cache.wordFits (raw layout randomBound randomFits).fits).accounted) _ _)

theorem finish_time (value) : (finish layout randomBound randomFits).time value ≤ 44 * width layout + 2 := by
  have bound := SumContext.merge_time (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits).reply
    layout.point.representation layout.store.representation layout.evaluation.cache.wordFits (output layout randomBound randomFits).fits
    (Sum.map id (productView layout.point layout.store) value)
  have sizes := widths layout randomBound randomFits
  exact bound.trans (by change 44 * (output layout randomBound randomFits).encoding.words + 2 ≤ _; omega)

theorem finish_words : descriptionWords (finish layout randomBound randomFits).code ≤ 286 * width layout + 143 := by
  have bound := SumContext.merge_words (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits).reply
    layout.point.representation layout.store.representation layout.evaluation.cache.wordFits (output layout randomBound randomFits).fits
  have sizes := widths layout randomBound randomFits
  exact bound.trans (by change 286 * (output layout randomBound randomFits).encoding.words + 143 ≤ _; omega)

theorem finish_names : NamesAccounted (finish layout randomBound randomFits).code 3 :=
  SumContext.merge_names (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits).reply
    layout.point.representation layout.store.representation layout.evaluation.cache.wordFits (output layout randomBound randomFits).fits

end Signatures.Runtime.CaliperBackend.WeightedCallerPackets
