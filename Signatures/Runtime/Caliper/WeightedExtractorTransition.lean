import Signatures.Runtime.Caliper.WeightedExtractorRouting

/-! The hash sum and the runtime forgery scalar enter an actual local
arithmetic routine. Its saved signing input includes the returned private cache.
Both permutations and every retained word are executed copies. -/
namespace Signatures.Runtime.CaliperBackend.WeightedExtractor
open Caliper BoundedSource ByteRoute
variable {w : Nat}

namespace Layouts
variable {K M G F R : Type} (layout : Layouts w K M G F R)
def numeratorInput := layout.scalar.prod layout.signing.rows.accumulation.cache.value
  (layout.fits (by
    have stateBound := layout.base_sizes.2.2.2.2.2.2.2
    change layout.signing.rows.accumulation.cache.value.representation.encoding.words +
      layout.table.representation.encoding.words ≤ layout.width at stateBound
    have scalarBound := layout.base_sizes.2.1
    omega))
theorem numeratorInput_size : layout.numeratorInput.representation.encoding.words ≤ 2 * layout.width := by
  have stateBound := layout.base_sizes.2.2.2.2.2.2.2
  change layout.signing.rows.accumulation.cache.value.representation.encoding.words +
    layout.table.representation.encoding.words ≤ layout.width at stateBound
  change layout.scalar.representation.encoding.words +
    layout.signing.rows.accumulation.cache.value.representation.encoding.words ≤ _
  have := layout.base_sizes.2.1
  omega
def saved := layout.signing.input.prod layout.message
  (layout.fits (by have := layout.signing.input_size; have := layout.base_sizes.1; have := layout.width_eq; omega))
theorem saved_size : layout.saved.representation.encoding.words ≤ 4 * layout.width := by
  change layout.signing.input.representation.encoding.words + layout.message.representation.encoding.words ≤ _
  have := layout.signing.input_size
  have := layout.base_sizes.1
  have := layout.width_eq
  omega
abbrev Prepared := layout.numeratorInput.Value × layout.saved.Value
abbrev Computed := layout.scalar.Value × layout.saved.Value
def prepared : Representation w layout.Prepared :=
  layout.numeratorInput.representation.prod layout.saved.representation
    (layout.fits (by have := layout.numeratorInput_size; have := layout.saved_size; omega))
def computed : Representation w layout.Computed :=
  layout.scalar.representation.prod layout.saved.representation
    (layout.fits (by have := layout.base_sizes.2.1; have := layout.saved_size; omega))
def numeratorValue (value : layout.HashOutput) : layout.Prepared :=
  (⟨(value.2.val.1.2, value.1.val.1), value.2.property.1.2, value.1.property.1⟩,
   ⟨((value.2.val.2, value.1.val.2), value.2.val.1.1),
     ⟨value.2.property.2, value.1.property.2⟩, value.2.property.1.1⟩)
def tailValue (value : layout.Computed) : WeightedSignatureTail.Input layout.signing :=
  (⟨value.2.val.1, value.2.property.1⟩, ⟨(value.2.val.2, value.1.val), value.2.property.2, value.1.property⟩)
end Layouts

def numeratorParts (result table message scalar signature : Nat) : List (Part w) :=
  [.slice (result + table + message) scalar, .slice 0 result,
   .slice (result + table + message + scalar) signature, .slice result (table + message)]
theorem numeratorParts_valid (result table message scalar signature : Nat) :
    Valid (result + table + message + scalar + signature)
      (numeratorParts (w := w) result table message scalar signature) := by
  simp only [numeratorParts, Valid]
  exact ⟨by omega, by omega, by omega, by omega, trivial⟩
theorem numeratorParts_words (result table message scalar signature : Nat) :
    words (numeratorParts (w := w) result table message scalar signature) =
      (scalar + result) + ((signature + table) + message) := by
  simp only [numeratorParts, words]
  omega
theorem numeratorParts_bytes (result table message scalar signature : List (Word w)) :
    bytes (result ++ table ++ message ++ scalar ++ signature)
      (numeratorParts result.length table.length message.length scalar.length signature.length) =
      (scalar ++ result) ++ ((signature ++ table) ++ message) := by
  have scalarBlock := slice_block (result ++ table ++ message) scalar signature
  have resultBlock := slice_block [] result (table ++ message ++ scalar ++ signature)
  have signatureBlock := slice_block (result ++ table ++ message ++ scalar) signature []
  have savedBlock := slice_block result (table ++ message) (scalar ++ signature)
  simp only [List.length_append, List.length_nil, List.nil_append, List.append_nil, List.append_assoc]
    at scalarBlock resultBlock signatureBlock savedBlock
  simp only [numeratorParts, bytes, List.append_assoc, Nat.add_assoc,
    scalarBlock, resultBlock, signatureBlock, savedBlock, List.append_nil]

variable {K M G F R : Type} (layout : Layouts w K M G F R)
def transitionParts := numeratorParts (w := w)
  layout.signing.rows.accumulation.cache.value.representation.encoding.words
  layout.table.representation.encoding.words layout.message.representation.encoding.words
  layout.scalar.representation.encoding.words layout.signature.representation.encoding.words
theorem transitionParts_valid : Valid layout.hashOutput.encoding.words (transitionParts layout) := by
  have size : layout.hashOutput.encoding.words =
      layout.signing.rows.accumulation.cache.value.representation.encoding.words +
        layout.table.representation.encoding.words + layout.message.representation.encoding.words +
        layout.scalar.representation.encoding.words + layout.signature.representation.encoding.words := by
    change (layout.signing.rows.accumulation.cache.value.representation.encoding.words +
      layout.table.representation.encoding.words) + ((layout.message.representation.encoding.words +
      layout.scalar.representation.encoding.words) + layout.signature.representation.encoding.words) = _
    dsimp only [Layouts.message, Layouts.scalar]
    omega
  rw [size]
  exact numeratorParts_valid _ _ _ _ _
theorem transitionParts_words : words (transitionParts layout) = layout.prepared.encoding.words :=
  numeratorParts_words _ _ _ _ _
theorem transitionParts_bytes (value : layout.HashOutput) :
    bytes (layout.hashOutput.encoding.encode value) (transitionParts layout) =
      layout.prepared.encoding.encode (layout.numeratorValue value) := by
  let result := layout.signing.rows.accumulation.cache.value.representation.encoding.encode ⟨value.1.val.1, value.1.property.1⟩
  let table := layout.table.representation.encoding.encode ⟨value.1.val.2, value.1.property.2⟩
  let message := layout.message.representation.encoding.encode ⟨value.2.val.1.1, value.2.property.1.1⟩
  let scalar := layout.scalar.representation.encoding.encode ⟨value.2.val.1.2, value.2.property.1.2⟩
  let signature := layout.signature.representation.encoding.encode ⟨value.2.val.2, value.2.property.2⟩
  have routed := numeratorParts_bytes result table message scalar signature
  simp only [result, table, message, scalar, signature, Encoding.encode_length] at routed
  change bytes ((result ++ table) ++ ((message ++ scalar) ++ signature)) (numeratorParts _ _ _ _ _) =
    (scalar ++ result) ++ ((signature ++ table) ++ message)
  simpa only [List.append_assoc] using routed

def prepareNumerator : Realizer .unit layout.hashOutput layout.prepared layout.numeratorValue :=
  ByteRoute.realizer _ _ _ (transitionParts layout) layout.signing.rows.accumulation.cache.wordFits
    (transitionParts_valid layout) (transitionParts_words layout) (transitionParts_bytes layout)
def finishNumerator : Realizer .unit layout.computed (WeightedSignatureTail.input layout.signing) layout.tailValue :=
  (Pairing.swap .unit (by decide) layout.scalar.representation layout.saved.representation
    layout.signing.rows.accumulation.cache.wordFits layout.computed.fits).viewOutput _ layout.tailValue (by
      intro value
      change _ ++ (_ ++ _) = (_ ++ _) ++ _
      exact (List.append_assoc _ _ _).symm)

variable {numerator : F × R → F}
    (sum : Implementation .unit layout.numeratorInput layout.scalar numerator)
    {sumSlots : Nat} (sumBuffers : sum.program.code.memBound ≤ sumSlots) (sumReserve : sumSlots + 1 < 2 ^ w)
include sumBuffers sumReserve in
theorem numeratorNameFits : sum.program.savedBuffer < 2 ^ w := by
  have := layout.signing.rows.accumulation.cache.wordFits
  change max 2 sum.program.code.memBound < _
  omega
def retainNumerator :=
  sum.program.retain (by decide) layout.saved.representation layout.signing.rows.accumulation.cache.wordFits
    (numeratorNameFits layout sum sumBuffers sumReserve) layout.prepared.fits layout.computed.fits
def transitionValue (value : layout.HashOutput) : WeightedSignatureTail.Input layout.signing :=
  layout.tailValue
    (⟨numerator (layout.numeratorValue value).1.val,
      sum.preserves (layout.numeratorValue value).1.val (layout.numeratorValue value).1.property⟩,
     (layout.numeratorValue value).2)
def transition : Realizer .unit layout.hashOutput (WeightedSignatureTail.input layout.signing) (transitionValue layout sum) :=
  ((prepareNumerator layout).then (retainNumerator layout sum sumBuffers sumReserve)).then (finishNumerator layout)
theorem transition_ready (value : layout.HashOutput) (admitted : layout.afterHashReady value) :
    WeightedSignatureTail.ready layout.signing (transitionValue layout sum value) := admitted

end Signatures.Runtime.CaliperBackend.WeightedExtractor
