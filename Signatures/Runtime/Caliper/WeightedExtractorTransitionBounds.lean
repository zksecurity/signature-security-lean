import Signatures.Runtime.Caliper.WeightedExtractorTransition

/-! The local numerator step charges both permutations, retained state,
the arithmetic routine and its temporary buffer. -/
namespace Signatures.Runtime.CaliperBackend.WeightedExtractor
open Caliper BoundedSource
variable {w : Nat} {K M G F R : Type} (layout : Layouts w K M G F R)
    {numerator : F × R → F}
    (sum : Implementation .unit layout.numeratorInput layout.scalar numerator)
    {sumSlots : Nat} (sumBuffers : sum.program.code.memBound ≤ sumSlots) (sumReserve : sumSlots + 1 < 2 ^ w)

def transitionTime (sumTime : Nat) : Nat :=
  8 * layout.prepared.encoding.words +
    (sumTime + 8 * layout.numeratorInput.representation.encoding.words +
      8 * layout.scalar.representation.encoding.words + 12 * layout.saved.representation.encoding.words) +
    8 * layout.computed.encoding.words
def transitionWords (sumWords : Nat) : Nat :=
  (26 * layout.prepared.encoding.words + 14) +
    (sumWords + 26 * layout.numeratorInput.representation.encoding.words +
      26 * layout.scalar.representation.encoding.words + 39 * layout.saved.representation.encoding.words + 39) +
    (26 * layout.computed.encoding.words + 14) + 2

theorem prepare_time (value : layout.input.Value) : (prepare layout).time value ≤ 8 * layout.hashInput.encoding.words :=
  ByteRoute.time _ _ _ _ _ _ _ _ value
theorem prepare_words : descriptionWords (prepare layout).code ≤ 26 * layout.hashInput.encoding.words + 14 :=
  ByteRoute.codeWords _ _ _ _ _ _ _ _
theorem prepare_buffers : (prepare layout).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
theorem prepare_names (names : Nat) : NamesAccounted (prepare layout).code names := ByteRoute.names _ _ _ _ _ _ _ _ names
theorem prepareBad_time (value : layout.input.Value) :
    (prepareBad layout).time value ≤ 8 * (WeightedSignatureTail.input layout.signing).encoding.words :=
  ByteRoute.time _ _ _ _ _ _ _ _ value
theorem prepareBad_words : descriptionWords (prepareBad layout).code ≤
    26 * (WeightedSignatureTail.input layout.signing).encoding.words + 14 := ByteRoute.codeWords _ _ _ _ _ _ _ _
theorem prepareBad_buffers : (prepareBad layout).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
theorem prepareBad_names (names : Nat) : NamesAccounted (prepareBad layout).code names := ByteRoute.names _ _ _ _ _ _ _ _ names

theorem transition_time {sumTime sumWords : Nat} (bound : sum.BoundedBy sumTime sumWords) (value : layout.HashOutput) :
    (transition layout sum sumBuffers sumReserve).time value ≤ transitionTime layout sumTime := by
  have first := ByteRoute.time _ _ _ (transitionParts layout) layout.signing.rows.accumulation.cache.wordFits
    (transitionParts_valid layout) (transitionParts_words layout) (transitionParts_bytes layout) value
  have held := sum.program.retain_time_unit_le layout.saved.representation layout.signing.rows.accumulation.cache.wordFits
    (numeratorNameFits layout sum sumBuffers sumReserve) layout.prepared.fits layout.computed.fits (layout.numeratorValue value)
  have added := bound.time_le (layout.numeratorValue value).1
  have last := Pairing.swap_time_unit_le layout.scalar.representation layout.saved.representation
    layout.signing.rows.accumulation.cache.wordFits layout.computed.fits
    (⟨numerator (layout.numeratorValue value).1.val, sum.preserves _ (layout.numeratorValue value).1.property⟩,
      (layout.numeratorValue value).2)
  change (prepareNumerator layout).time value + (retainNumerator layout sum sumBuffers sumReserve).time _ +
    (finishNumerator layout).time _ ≤ _
  unfold transitionTime
  exact Nat.add_le_add (Nat.add_le_add first (held.trans (by omega))) last

theorem transition_words {sumTime sumWords : Nat} (bound : sum.BoundedBy sumTime sumWords) :
    descriptionWords (transition layout sum sumBuffers sumReserve).code ≤ transitionWords layout sumWords := by
  have first := ByteRoute.codeWords _ _ _ (transitionParts layout) layout.signing.rows.accumulation.cache.wordFits
    (transitionParts_valid layout) (transitionParts_words layout) (transitionParts_bytes layout)
  have held := sum.program.retain_descriptionWords_le (by decide) layout.saved.representation
    layout.signing.rows.accumulation.cache.wordFits (numeratorNameFits layout sum sumBuffers sumReserve)
    layout.prepared.fits layout.computed.fits
  have added := bound.code_le
  have last := Pairing.swap_descriptionWords_le .unit (by decide) layout.scalar.representation layout.saved.representation
    layout.signing.rows.accumulation.cache.wordFits layout.computed.fits
  change descriptionWords (((prepareNumerator layout).code ;; (retainNumerator layout sum sumBuffers sumReserve).code) ;;
    (finishNumerator layout).code) ≤ _
  rw [descriptionWords_seq, descriptionWords_seq]
  unfold transitionWords
  change descriptionWords (prepareNumerator layout).code ≤ _ at first
  change descriptionWords (retainNumerator layout sum sumBuffers sumReserve).code ≤ _ at held
  change descriptionWords (finishNumerator layout).code ≤ 26 * layout.computed.encoding.words + 14 at last
  omega

theorem transition_names {names : Nat} (bound : NamesAccounted sum.program.code names) :
    NamesAccounted (transition layout sum sumBuffers sumReserve).code names :=
  ((ByteRoute.names _ _ _ _ _ _ _ _ names).seq (Retain.names bound _ _ _)).seq (Reorder.names _ _ _ names)
theorem transition_buffers : (transition layout sum sumBuffers sumReserve).code.memBound ≤ max 2 sumSlots + 1 := by
  have first : (prepareNumerator layout).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
  have held := (Retain.code_names sum.program.code sum.program.savedBuffer
    layout.numeratorInput.representation.encoding.words layout.scalar.representation.encoding.words
    layout.saved.representation.encoding.words (Nat.le_max_left _ _) (Nat.le_max_right _ _)).2
  have last : (finishNumerator layout).code.memBound ≤ 2 := Reorder.buffers _ _ _
  change (retainNumerator layout sum sumBuffers sumReserve).code.memBound ≤ max 2 sum.program.code.memBound + 1 at held
  change max (max (prepareNumerator layout).code.memBound (retainNumerator layout sum sumBuffers sumReserve).code.memBound)
    (finishNumerator layout).code.memBound ≤ _
  omega

end Signatures.Runtime.CaliperBackend.WeightedExtractor
