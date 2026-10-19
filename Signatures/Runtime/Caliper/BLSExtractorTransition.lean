import Signatures.Runtime.Caliper.BLSExtractorRouting

/-! After the hash pass, an executed permutation moves the retained signature
log and coefficients into the evaluator input. The computed hash sum is saved
alongside the original forgery target and beta for the signature tail. -/
namespace Signatures.Runtime.CaliperBackend.BLSExtractorFrame
open Caliper BoundedSource Assembly
variable {w : Nat}

def transitionOperands (scalar entries header signature : Nat) : List (Operand w) :=
  reads 0 (scalar + entries + header) signature ++ reads 0 scalar entries ++
  reads 0 (scalar + entries) header ++ reads 0 0 scalar
theorem transitionOperands_length (scalar entries header signature : Nat) :
    (transitionOperands (w := w) scalar entries header signature).length =
      signature + entries + (header + scalar) := by
  simp only [transitionOperands, List.length_append, reads_length]
  omega
theorem transitionOperands_names (scalar entries header signature : Nat) :
    SourcesBound (transitionOperands (w := w) scalar entries header signature) 1 := by
  simp only [transitionOperands, sourcesBound_append]
  exact ⟨⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩, sourcesBound_reads _ _ _ _ (by decide)⟩
theorem transitionOperands_fit (scalar entries header signature : Nat) :
    ∀ operand ∈ transitionOperands (w := w) scalar entries header signature, operand.NamesFit := by
  intro operand member
  simp only [transitionOperands, List.mem_append] at member
  rcases member with ((member | member) | member) | member <;>
    exact reads_namesFit 0 _ _ (by positivity) operand member
theorem transitionOperands_valid (scalar entries header signature : Nat) (before : State w)
    (size : (before.bufs 0).size = scalar + entries + header + signature)
    (fits : (before.bufs 0).size < 2 ^ w) : Valid 1 before (transitionOperands scalar entries header signature) := by
  intro operand member
  simp only [transitionOperands, List.mem_append] at member
  rcases member with ((member | member) | member) | member <;>
    exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member
theorem transitionOperands_values (scalar entries header signature : List (Word w)) (before : State w)
    (contents : (before.bufs 0).toList = (scalar ++ entries) ++ (header ++ signature)) :
    values (transitionOperands scalar.length entries.length header.length signature.length) before =
      (signature ++ entries) ++ (header ++ scalar) := by
  have s := ListFold.reads_block (scalar ++ entries ++ header) signature [] before
    (by simpa only [List.append_nil, List.append_assoc] using contents)
  have e := ListFold.reads_block scalar entries (header ++ signature) before
    (by simpa only [List.append_assoc] using contents)
  have h := ListFold.reads_block (scalar ++ entries) header signature before
    (by simpa only [List.append_assoc] using contents)
  have a := ListFold.reads_block [] scalar (entries ++ header ++ signature) before
    (by simpa only [List.nil_append, List.append_assoc] using contents)
  simp only [List.length_append, List.length_nil, values] at s e h a
  simp only [transitionOperands, values, List.map_append, s, e, h, a, List.append_assoc]

variable {M G F : Type} (layout : BLSTokens.Layouts w M G F)
theorem goodTailFits : layout.good.input.representation.encoding.words +
    (BLSSignatureTail.goodContext layout).representation.encoding.words < 2 ^ w :=
  layout.good.fits_of_le (by
    change (((tokens layout.good).representation.encoding.words + (coefficients layout.good).representation.encoding.words) +
      (table layout.good).representation.encoding.words) + ((message layout.good).representation.encoding.words +
        ((scalar layout.good).representation.encoding.words + (scalar layout.good).representation.encoding.words)) ≤ _
    have := base_sizes layout.good
    omega)
theorem badTailFits : layout.bad.input.representation.encoding.words +
    (BLSSignatureTail.badContext layout).representation.encoding.words < 2 ^ w :=
  (signatureInput layout.bad).representation.fits

def transitionValue (value : (returned layout.good).Value) : BLSSignatureTail.GoodInput layout :=
  (⟨(value.val.2.2, value.val.1.2), value.property.2.2, value.property.1.2⟩,
    ⟨(value.val.2.1.1, (value.val.2.1.2, value.val.1.1)),
      value.property.2.1.1, value.property.2.1.2, value.property.1.1⟩)
theorem transitionValue_bytes (value : (returned layout.good).Value) :
    (BLSSignatureTail.goodInput layout (goodTailFits layout)).encoding.encode (transitionValue layout value) =
      ((signature layout.good).representation.encoding.encode ⟨value.val.2.2, value.property.2.2⟩ ++
        (table layout.good).representation.encoding.encode ⟨value.val.1.2, value.property.1.2⟩) ++
      ((target layout.good).representation.encoding.encode ⟨value.val.2.1, value.property.2.1⟩ ++
        (scalar layout.good).representation.encoding.encode ⟨value.val.1.1, value.property.1.1⟩) := by
  let s := (signature layout.good).representation.encoding.encode ⟨value.val.2.2, value.property.2.2⟩
  let e := (table layout.good).representation.encoding.encode ⟨value.val.1.2, value.property.1.2⟩
  let m := (message layout.good).representation.encoding.encode ⟨value.val.2.1.1, value.property.2.1.1⟩
  let b := (scalar layout.good).representation.encoding.encode ⟨value.val.2.1.2, value.property.2.1.2⟩
  let a := (scalar layout.good).representation.encoding.encode ⟨value.val.1.1, value.property.1.1⟩
  change (s ++ e) ++ (m ++ (b ++ a)) = (s ++ e) ++ ((m ++ b) ++ a)
  simp only [List.append_assoc]

theorem transition_size :
    (transitionOperands (w := w) (scalar layout.good).representation.encoding.words (table layout.good).representation.encoding.words
      (target layout.good).representation.encoding.words (signature layout.good).representation.encoding.words).length =
      (BLSSignatureTail.goodInput layout (goodTailFits layout)).encoding.words := by
      rw [transitionOperands_length]
      change ((signature layout.good).representation.encoding.words + (table layout.good).representation.encoding.words) +
        (((message layout.good).representation.encoding.words + (scalar layout.good).representation.encoding.words) +
          (scalar layout.good).representation.encoding.words) =
        ((signature layout.good).representation.encoding.words + (table layout.good).representation.encoding.words) +
          ((message layout.good).representation.encoding.words + ((scalar layout.good).representation.encoding.words +
            (scalar layout.good).representation.encoding.words))
      omega

def transition : Realizer .unit (returned layout.good).representation
    (BLSSignatureTail.goodInput layout (goodTailFits layout)) (transitionValue layout) :=
  Assembly.realizer .unit (by decide) _ _ _
    (transitionOperands (scalar layout.good).representation.encoding.words (table layout.good).representation.encoding.words
      (target layout.good).representation.encoding.words (signature layout.good).representation.encoding.words)
    layout.rows.accumulation.cache.wordFits
    (transition_size layout)
    (transitionOperands_fit _ _ _ _)
    (by
      intro value state represented
      have size := represented_size _ represented
      change (state.bufs 0).size = ((scalar layout.good).representation.encoding.words + (table layout.good).representation.encoding.words) +
        ((target layout.good).representation.encoding.words + (signature layout.good).representation.encoding.words) at size
      exact transitionOperands_valid _ _ _ _ state (by omega)
        (by rw [Assembly.represented_size _ represented]; exact (returned layout.good).representation.fits))
    (by
      intro value state represented
      rw [transitionValue_bytes]
      have result := transitionOperands_values
        ((scalar layout.good).representation.encoding.encode ⟨value.val.1.1, value.property.1.1⟩)
        ((table layout.good).representation.encoding.encode ⟨value.val.1.2, value.property.1.2⟩)
        ((target layout.good).representation.encoding.encode ⟨value.val.2.1, value.property.2.1⟩)
        ((signature layout.good).representation.encoding.encode ⟨value.val.2.2, value.property.2.2⟩) state represented.2.1
      simpa only [Encoding.encode_length] using result)

def badValue (value : (input layout.bad).Value) : BLSSignatureTail.BadInput layout :=
  productView layout.bad.input (target layout.bad) (signatureValue layout.bad value)
def prepareBad : Realizer .unit (input layout.bad).representation
    (BLSSignatureTail.badInput layout (badTailFits layout)) (badValue layout) :=
  (selectSignature layout.bad).viewOutput _ _ (fun _ => rfl)
theorem badReady (value : (input layout.bad).Value) (reserved : signatureReady layout.bad value) :
    BLSSignatureTail.badReady layout (badValue layout value) := reserved
theorem transitionReady (value : (returned layout.good).Value)
    (reserved : value.val.1.2.length + value.val.2.2.1.length + 1 ≤ layout.rows.accumulation.cache.capacityPred + 1) :
    BLSSignatureTail.goodReady layout (transitionValue layout value) := reserved

end Signatures.Runtime.CaliperBackend.BLSExtractorFrame
