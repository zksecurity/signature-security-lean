import Signatures.Runtime.Caliper.BLSSignatureTailLayout

/-! The original algebraic forgery, both reverse-stored transcripts, and the
private cache have explicit bounded encodings. These layouts do not identify a
reordering with a free operation: the following routing programs copy the words.
Transcript and explanation capacities are independent. -/
namespace Signatures.Runtime.CaliperBackend.BLSExtractorFrame
open Caliper BoundedSource
variable {w : Nat} {M G F R : Type} (layout : TokenEvaluation.Layouts w M G F R)

abbrev message := layout.rows.accumulation.cache.key
abbrev scalar := layout.rows.accumulation.coefficient
abbrev coefficients := layout.assembly.values
abbrev tokens := layout.assembly.keys
abbrev table := layout.rows.accumulation.cache.lookup.table

theorem base_sizes : (message layout).representation.encoding.words ≤ layout.width ∧
    (scalar layout).representation.encoding.words ≤ layout.width ∧
    (coefficients layout).representation.encoding.words ≤ layout.width ∧
    (tokens layout).representation.encoding.words ≤ layout.width ∧
    (table layout).representation.encoding.words ≤ layout.width := by
  have assembly := layout.assembly.base_sizes
  have bounds := layout.base_sizes
  change (message layout).representation.encoding.words + layout.rows.point.representation.encoding.words ≤ layout.assembly.width ∧ _ at assembly
  change _ ∧ _ ∧ _ ∧ _ ∧ _
  exact ⟨by omega, by exact assembly.2.1.trans bounds.1,
    assembly.2.2.2.2.1.trans bounds.1, assembly.2.2.2.1.trans bounds.1, bounds.2.2.1⟩

def explanations : Layout w (List F × List F) := (coefficients layout).prod (coefficients layout)
  (layout.fits_of_le (by have := base_sizes layout; dsimp only [message, scalar, coefficients, tokens, table] at *; omega))
def forgeryTail : Layout w (F × (List F × List F)) := (scalar layout).prod (explanations layout)
  (layout.fits_of_le (by change _ + (_ + _) ≤ _; have := base_sizes layout; dsimp only [message, scalar, coefficients, tokens, table] at *; omega))
def forgery : Layout w (M × (F × (List F × List F))) := (message layout).prod (forgeryTail layout)
  (layout.fits_of_le (by change _ + (_ + (_ + _)) ≤ _; have := base_sizes layout; dsimp only [message, scalar, coefficients, tokens, table] at *; omega))
def logs : Layout w (List (M × G) × List (M × G)) := (tokens layout).prod (tokens layout)
  (layout.fits_of_le (by have := base_sizes layout; dsimp only [message, scalar, coefficients, tokens, table] at *; omega))
def store : Layout w (List (M × R) × (List (M × G) × List (M × G))) := (table layout).prod (logs layout)
  (layout.fits_of_le (by change _ + (_ + _) ≤ _; have := base_sizes layout; dsimp only [message, scalar, coefficients, tokens, table] at *; omega))
def input := (forgery layout).prod (store layout)
  (layout.fits_of_le (by change (_ + (_ + (_ + _))) + (_ + (_ + _)) ≤ _; have := base_sizes layout; dsimp only [message, scalar, coefficients, tokens, table] at *; omega))

def target : Layout w (M × F) := (message layout).prod (scalar layout)
  (layout.fits_of_le (by have := base_sizes layout; dsimp only [message, scalar, coefficients, tokens, table] at *; omega))
abbrev signature := TokenRows.input layout.assembly
def context := (target layout).prod (signature layout)
  (layout.fits_of_le (by change (_ + _) + (_ + _) ≤ _; have := base_sizes layout; dsimp only [message, scalar, coefficients, tokens, table] at *; omega))
def prepared := layout.input.prod (context layout)
  (layout.fits_of_le (by change ((_ + _) + _) + ((_ + _) + (_ + _)) ≤ _; have := base_sizes layout; dsimp only [message, scalar, coefficients, tokens, table] at *; omega))
def returned := layout.rows.state.prod (context layout)
  (layout.fits_of_le (by change _ + ((_ + _) + (_ + _)) ≤ _; have := base_sizes layout; have := layout.base_sizes; dsimp only [message, scalar, coefficients, tokens, table] at *; omega))
def signatureInput := layout.input.prod (target layout)
  (layout.fits_of_le (by change ((_ + _) + _) + (_ + _) ≤ _; have := base_sizes layout; dsimp only [message, scalar, coefficients, tokens, table] at *; omega))

def prepareValue (value : (input layout).Value) : (prepared layout).Value :=
  ⟨(((value.val.2.2.1, value.val.1.2.2.1), value.val.2.1),
      ((value.val.1.1, value.val.1.2.1), (value.val.2.2.2, value.val.1.2.2.2))),
    ⟨⟨value.property.2.2.1, value.property.1.2.2.1⟩, value.property.2.1⟩,
    ⟨value.property.1.1, value.property.1.2.1⟩, value.property.2.2.2, value.property.1.2.2.2⟩
def signatureValue (value : (input layout).Value) : (signatureInput layout).Value :=
  ⟨(((value.val.2.2.2, value.val.1.2.2.2), value.val.2.1), (value.val.1.1, value.val.1.2.1)),
    ⟨⟨value.property.2.2.2, value.property.1.2.2.2⟩, value.property.2.1⟩,
    value.property.1.1, value.property.1.2.1⟩

def ready (value : (input layout).Value) : Prop :=
  value.val.2.1.length + value.val.2.2.1.length + value.val.2.2.2.length + 1 ≤ layout.rows.accumulation.cache.capacityPred + 1
def signatureReady (value : (input layout).Value) : Prop :=
  value.val.2.1.length + value.val.2.2.2.length + 1 ≤ layout.rows.accumulation.cache.capacityPred + 1
theorem signatureReady_of_ready (value : (input layout).Value) (reserved : ready layout value) : signatureReady layout value := by
  unfold ready at reserved
  unfold signatureReady
  omega

end Signatures.Runtime.CaliperBackend.BLSExtractorFrame
