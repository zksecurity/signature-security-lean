import Proofs.Runtime.Caliper.WeightedSignatureTailMemory
import Proofs.Runtime.Caliper.WeightedSignatureTailSource
import Proofs.Runtime.Caliper.TokenEvaluationBuffers
import Proofs.Runtime.Caliper.TokenEvaluationOracle

/-! Full weighted extraction stores a forgery, independent hash/signing
transcripts and coefficients, and one private cache. Hash keys and signed
messages need not have the same type or encoding. -/
namespace Signatures.Runtime.CaliperBackend.WeightedExtractor
open Caliper BoundedSource

def hashRows {w : Nat} {K M G F R : Type} (signing : WeightedExtraction.Layouts w K M G F R) :
    RowRequest.Layouts w K G F R where
  accumulation := signing.rows.accumulation
  point := signing.rows.point
  storageFits := by
    have fits := signing.rows.storageFits
    unfold WeightedCoefficient.Layouts.width at fits
    dsimp only [WeightedToken.Layouts.accumulation]
    omega
def hashWidth {w : Nat} {K M G F R : Type} (signing : WeightedExtraction.Layouts w K M G F R)
    (capacity coefficients : Nat) : Nat :=
  4 + (capacity + 1) *
    ((hashRows signing).token.representation.encoding.words + signing.rows.accumulation.coefficient.representation.encoding.words) +
    (coefficients + 1) * signing.rows.accumulation.coefficient.representation.encoding.words +
    signing.rows.state.representation.encoding.words

structure Layouts (w : Nat) (K M G F R : Type) where
  signing : WeightedExtraction.Layouts w K M G F R
  hashCapacity : Nat
  gammaCapacity : Nat
  hashCounterFits : hashCapacity + 2 ≤ 2 ^ w
  gammaCountFits : gammaCapacity < 2 ^ w
  storageFits : 16 * (signing.width + hashWidth signing hashCapacity gammaCapacity) < 2 ^ w

namespace Layouts
variable {w : Nat} {K M G F R : Type} (layout : Layouts w K M G F R)
def width := layout.signing.width + hashWidth layout.signing layout.hashCapacity layout.gammaCapacity
theorem fits {words : Nat} (bound : words ≤ 16 * layout.width) : words < 2 ^ w := bound.trans_lt layout.storageFits
def hashes : TokenEvaluation.Layouts w K G F R where
  rows := hashRows layout.signing
  capacity := layout.hashCapacity
  coefficients := layout.gammaCapacity
  counterFits := layout.hashCounterFits
  coefficientCountFits := layout.gammaCountFits
  storageFits := layout.fits (by
    change 16 * hashWidth layout.signing layout.hashCapacity layout.gammaCapacity ≤ _
    unfold width
    omega)
theorem width_eq : layout.width = layout.signing.width + layout.hashes.width := rfl
abbrev message := layout.signing.rows.weighted.message
abbrev scalar := layout.signing.rows.accumulation.coefficient
abbrev gamma := layout.hashes.assembly.values
abbrev xi := layout.signing.assembly.values
abbrev hashTokens := layout.hashes.assembly.keys
abbrev signTokens := layout.signing.assembly.keys
abbrev table := layout.signing.rows.accumulation.cache.lookup.table
abbrev state := layout.signing.rows.state
abbrev signature := TokenRows.input layout.signing.assembly
abbrev target := WeightedSignatureTail.context layout.signing

theorem base_sizes :
    layout.message.representation.encoding.words ≤ layout.width ∧
    layout.scalar.representation.encoding.words ≤ layout.width ∧
    layout.gamma.representation.encoding.words ≤ layout.width ∧
    layout.xi.representation.encoding.words ≤ layout.width ∧
    layout.hashTokens.representation.encoding.words ≤ layout.width ∧
    layout.signTokens.representation.encoding.words ≤ layout.width ∧
    layout.table.representation.encoding.words ≤ layout.width ∧
    layout.state.representation.encoding.words ≤ layout.width := by
  have signed := layout.signing.assembly.base_sizes
  have hashed := layout.hashes.assembly.base_sizes
  have sb := layout.signing.base_sizes
  have hb := layout.hashes.base_sizes
  have msg : layout.message.representation.encoding.words + layout.signing.rows.point.representation.encoding.words ≤
      layout.signing.assembly.width := signed.1
  rw [width_eq]
  exact ⟨by omega, signed.2.1.trans (sb.1.trans (Nat.le_add_right _ _)),
    hashed.2.2.2.2.1.trans (hb.1.trans (Nat.le_add_left _ _)),
    signed.2.2.2.2.1.trans (sb.1.trans (Nat.le_add_right _ _)),
    hashed.2.2.2.1.trans (hb.1.trans (Nat.le_add_left _ _)),
    signed.2.2.2.1.trans (sb.1.trans (Nat.le_add_right _ _)),
    sb.2.2.1.trans (Nat.le_add_right _ _), sb.2.1.trans (Nat.le_add_right _ _)⟩

def explanations := layout.gamma.prod layout.xi
  (layout.fits (by have := layout.base_sizes; omega))
def forgeryTail := layout.scalar.prod layout.explanations
  (layout.fits (by change _ + (_ + _) ≤ _; have := layout.base_sizes; omega))
def forgery := layout.message.prod layout.forgeryTail
  (layout.fits (by change _ + (_ + (_ + _)) ≤ _; have := layout.base_sizes; omega))
def logs := layout.hashTokens.prod layout.signTokens
  (layout.fits (by have := layout.base_sizes; omega))
def store := layout.table.prod layout.logs
  (layout.fits (by change _ + (_ + _) ≤ _; have := layout.base_sizes; omega))
def input := layout.forgery.prod layout.store
  (layout.fits (by change (_ + (_ + (_ + _))) + (_ + (_ + _)) ≤ _; have := layout.base_sizes; omega))
def context := layout.target.prod layout.signature
  (layout.fits (by
    change (layout.message.representation.encoding.words + layout.scalar.representation.encoding.words) +
      (layout.signTokens.representation.encoding.words + layout.xi.representation.encoding.words) ≤ _
    have := layout.base_sizes
    omega))
theorem context_size : layout.context.representation.encoding.words ≤ 4 * layout.width := by
  change (layout.message.representation.encoding.words + layout.scalar.representation.encoding.words) +
    (layout.signTokens.representation.encoding.words + layout.xi.representation.encoding.words) ≤ _
  have := layout.base_sizes
  omega
abbrev HashInput := layout.hashes.input.Value × layout.context.Value
abbrev HashOutput := layout.state.Value × layout.context.Value
def hashInput : Representation w layout.HashInput :=
  layout.hashes.input.representation.prod layout.context.representation
    (layout.fits (by have := layout.hashes.input_size; have := layout.context_size; have := layout.width_eq; omega))
def hashOutput : Representation w layout.HashOutput :=
  layout.state.representation.prod layout.context.representation
    (layout.fits (by have := layout.base_sizes; have := layout.context_size; omega))

def preparedValue (value : layout.input.Value) : layout.HashInput :=
  (⟨((value.val.2.2.1, value.val.1.2.2.1), value.val.2.1),
      ⟨value.property.2.2.1, value.property.1.2.2.1⟩, value.property.2.1⟩,
   ⟨((value.val.1.1, value.val.1.2.1), (value.val.2.2.2, value.val.1.2.2.2)),
      ⟨value.property.1.1, value.property.1.2.1⟩, value.property.2.2.2, value.property.1.2.2.2⟩)
def signatureValue (value : layout.input.Value) : WeightedSignatureTail.Input layout.signing :=
  (⟨((value.val.2.2.2, value.val.1.2.2.2), value.val.2.1),
      ⟨value.property.2.2.2, value.property.1.2.2.2⟩, value.property.2.1⟩,
   ⟨(value.val.1.1, value.val.1.2.1), value.property.1.1, value.property.1.2.1⟩)

def ready (value : layout.input.Value) : Prop :=
  value.val.2.1.length + value.val.2.2.1.length +
    layout.signing.terms * value.val.2.2.2.length + layout.signing.terms ≤
      layout.signing.rows.accumulation.cache.capacityPred + 1
def badReady (value : layout.input.Value) : Prop := WeightedSignatureTail.ready layout.signing (layout.signatureValue value)
def hashReady (value : layout.HashInput) : Prop :=
  value.1.val.2.length + value.1.val.1.1.length +
    layout.signing.terms * value.2.val.2.1.length + layout.signing.terms ≤
      layout.signing.rows.accumulation.cache.capacityPred + 1
def afterHashReady (value : layout.HashOutput) : Prop :=
  value.1.val.2.length + layout.signing.terms * value.2.val.2.1.length + layout.signing.terms ≤
    layout.signing.rows.accumulation.cache.capacityPred + 1
theorem prepare_ready (value : layout.input.Value) (admitted : layout.ready value) :
    layout.hashReady (layout.preparedValue value) := admitted
theorem hash_evaluation_ready (value : layout.HashInput) (admitted : layout.hashReady value) : layout.hashes.ready value.1 := by
  change value.1.val.2.length + value.1.val.1.1.length ≤ layout.signing.rows.accumulation.cache.capacityPred + 1
  unfold hashReady at admitted
  omega
instance (value : layout.input.Value) : Decidable (layout.ready value) := inferInstanceAs (Decidable (_ ≤ _))
instance (value : layout.input.Value) : Decidable (layout.badReady value) := inferInstanceAs (Decidable (_ ≤ _))
end Layouts
end Signatures.Runtime.CaliperBackend.WeightedExtractor
