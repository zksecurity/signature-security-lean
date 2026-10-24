import Proofs.Runtime.Caliper.WeightedCoefficientLayout

/-! Paid copies assemble the generated evaluator's input and retain the
coefficient/old accumulator. The existing cache accumulator finish code
consumes the returned message value and the saved pair. -/
namespace Signatures.Runtime.CaliperBackend.WeightedCoefficient
open Caliper BoundedSource ByteRoute
variable {w : Nat} {K M F R : Type} (layout : Layouts w K M F R)

def prepareParts (zero : layout.evaluation.cache.value.Value) : List (Part w) :=
  [.slice 0 layout.message.representation.encoding.words,
   .literal (layout.evaluation.cache.value.representation.encoding.encode zero),
   .slice (layout.message.representation.encoding.words +
     layout.evaluation.coefficient.representation.encoding.words +
     layout.evaluation.cache.value.representation.encoding.words)
     layout.evaluation.cache.lookup.table.representation.encoding.words,
   .slice layout.message.representation.encoding.words
     layout.evaluation.saved.representation.encoding.words]

theorem prepareParts_valid (zero : layout.evaluation.cache.value.Value) :
    ByteRoute.Valid layout.input.representation.encoding.words (prepareParts layout zero) := by
  change (0 + _ ≤ _ + (_ + (_ + _))) ∧
    (_ + _ + _ + _ ≤ _ + (_ + (_ + _))) ∧
    (_ + (_ + _) ≤ _ + (_ + (_ + _))) ∧ True
  dsimp only [WeightedRows.rows]
  exact ⟨by omega, by omega, by omega, trivial⟩

theorem prepareParts_words (zero : layout.evaluation.cache.value.Value) :
    ByteRoute.words (prepareParts layout zero) = layout.prepared.encoding.words := by
  simp only [prepareParts, ByteRoute.words, Encoding.encode_length]
  change _ + (_ + (_ + ((_ + _) + 0))) = (_ + (_ + _)) + (_ + _)
  dsimp only [WeightedRows.rows]
  omega

theorem prepare_bytes (zero : layout.evaluation.cache.value.Value) (value : layout.input.Value) :
    ByteRoute.bytes (layout.input.representation.encoding.encode value) (prepareParts layout zero) =
      layout.prepared.encoding.encode (prepareValue layout zero value) := by
  let m := layout.message.representation.encoding.encode (message layout value)
  let a := layout.evaluation.coefficient.representation.encoding.encode
    ⟨value.val.2.1, value.property.2.1⟩
  let old := layout.evaluation.cache.value.representation.encoding.encode
    ⟨value.val.2.2.1, value.property.2.2.1⟩
  let t := layout.evaluation.cache.lookup.table.representation.encoding.encode (cache layout value)
  have hm : m.length = layout.message.representation.encoding.words := Encoding.encode_length _ _
  have ha : a.length = layout.evaluation.coefficient.representation.encoding.words := Encoding.encode_length _ _
  have ho : old.length = layout.evaluation.cache.value.representation.encoding.words := Encoding.encode_length _ _
  have ht : t.length = layout.evaluation.cache.lookup.table.representation.encoding.words := Encoding.encode_length _ _
  have messageRead := ByteRoute.slice_block [] m (a ++ (old ++ t))
  have cacheRead := ByteRoute.slice_block (m ++ a ++ old) t []
  have savedRead := ByteRoute.slice_block m (a ++ old) t
  simp only [List.nil_append, List.append_nil, List.length_nil, List.length_append,
    hm, ha, ho, ht, List.append_assoc] at messageRead cacheRead savedRead
  change ((m ++ (a ++ (old ++ t))).drop 0).take _ ++
    (_ ++ (((m ++ (a ++ (old ++ t))).drop (_ + _ + _)).take _ ++
      (((m ++ (a ++ (old ++ t))).drop _).take (_ + _) ++ []))) = _
  simp only [Nat.add_assoc]
  rw [messageRead, cacheRead, savedRead]
  change _ = (m ++ (layout.evaluation.cache.value.representation.encoding.encode zero ++ t)) ++ (a ++ old)
  simp only [List.append_nil, List.append_assoc]

def prepare (zero : layout.evaluation.cache.value.Value) :
    Realizer .unit layout.input.representation layout.prepared (prepareValue layout zero) :=
  ByteRoute.realizer _ _ _ (prepareParts layout zero) layout.evaluation.cache.wordFits
    (prepareParts_valid layout zero) (prepareParts_words layout zero) (prepare_bytes layout zero)

end Signatures.Runtime.CaliperBackend.WeightedCoefficient
