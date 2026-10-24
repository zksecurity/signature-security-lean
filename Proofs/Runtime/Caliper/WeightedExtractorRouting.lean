import Proofs.Runtime.Caliper.WeightedExtractorLayout

/-! Executed routing of the complete forgery/store frame. Independent
coefficient and transcript widths are copied explicitly; discarded bad-branch
fields remain accounted in the original input storage. -/
namespace Signatures.Runtime.CaliperBackend.WeightedExtractor
open Caliper BoundedSource ByteRoute
variable {w : Nat}

def prepareParts (header gamma xi table hashes signs : Nat) : List (Part w) :=
  [.slice (header + gamma + xi + table) hashes, .slice header gamma,
   .slice (header + gamma + xi) table, .slice 0 header,
   .slice (header + gamma + xi + table + hashes) signs, .slice (header + gamma) xi]
def signatureParts (header gamma xi table hashes signs : Nat) : List (Part w) :=
  [.slice (header + gamma + xi + table + hashes) signs, .slice (header + gamma) xi,
   .slice (header + gamma + xi) table, .slice 0 header]
theorem prepareParts_valid (header gamma xi table hashes signs : Nat) :
    Valid (header + gamma + xi + table + hashes + signs) (prepareParts (w := w) header gamma xi table hashes signs) := by
  simp only [prepareParts, Valid]
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, trivial⟩
theorem signatureParts_valid (header gamma xi table hashes signs : Nat) :
    Valid (header + gamma + xi + table + hashes + signs) (signatureParts (w := w) header gamma xi table hashes signs) := by
  simp only [signatureParts, Valid]
  exact ⟨by omega, by omega, by omega, by omega, trivial⟩
theorem prepareParts_words (header gamma xi table hashes signs : Nat) :
    words (prepareParts (w := w) header gamma xi table hashes signs) =
      ((hashes + gamma) + table) + (header + (signs + xi)) := by
  simp only [prepareParts, words]
  omega
theorem signatureParts_words (header gamma xi table hashes signs : Nat) :
    words (signatureParts (w := w) header gamma xi table hashes signs) = ((signs + xi) + table) + header := by
  simp only [signatureParts, words]
  omega

theorem prepareParts_bytes (header gamma xi table hashes signs : List (Word w)) :
    bytes (header ++ gamma ++ xi ++ table ++ hashes ++ signs)
      (prepareParts header.length gamma.length xi.length table.length hashes.length signs.length) =
        ((hashes ++ gamma) ++ table) ++ (header ++ (signs ++ xi)) := by
  have h := slice_block (header ++ gamma ++ xi ++ table) hashes signs
  have g := slice_block header gamma (xi ++ table ++ hashes ++ signs)
  have t := slice_block (header ++ gamma ++ xi) table (hashes ++ signs)
  have b := slice_block [] header (gamma ++ xi ++ table ++ hashes ++ signs)
  have s := slice_block (header ++ gamma ++ xi ++ table ++ hashes) signs []
  have x := slice_block (header ++ gamma) xi (table ++ hashes ++ signs)
  simp only [List.length_append, List.length_nil, List.nil_append, List.append_nil, List.append_assoc] at h g t b s x
  simp only [prepareParts, bytes, List.append_assoc, Nat.add_assoc, h, g, t, b, s, x, List.append_nil]
theorem signatureParts_bytes (header gamma xi table hashes signs : List (Word w)) :
    bytes (header ++ gamma ++ xi ++ table ++ hashes ++ signs)
      (signatureParts header.length gamma.length xi.length table.length hashes.length signs.length) =
        ((signs ++ xi) ++ table) ++ header := by
  have s := slice_block (header ++ gamma ++ xi ++ table ++ hashes) signs []
  have x := slice_block (header ++ gamma) xi (table ++ hashes ++ signs)
  have t := slice_block (header ++ gamma ++ xi) table (hashes ++ signs)
  have b := slice_block [] header (gamma ++ xi ++ table ++ hashes ++ signs)
  simp only [List.length_append, List.length_nil, List.nil_append, List.append_nil, List.append_assoc] at s x t b
  simp only [signatureParts, bytes, List.append_assoc, Nat.add_assoc, s, x, t, b, List.append_nil]

variable {K M G F R : Type} (layout : Layouts w K M G F R)
def parts := prepareParts (w := w) layout.target.representation.encoding.words layout.gamma.representation.encoding.words
  layout.xi.representation.encoding.words layout.table.representation.encoding.words
  layout.hashTokens.representation.encoding.words layout.signTokens.representation.encoding.words
def badParts := signatureParts (w := w) layout.target.representation.encoding.words layout.gamma.representation.encoding.words
  layout.xi.representation.encoding.words layout.table.representation.encoding.words
  layout.hashTokens.representation.encoding.words layout.signTokens.representation.encoding.words
theorem input_words : layout.input.representation.encoding.words =
    layout.target.representation.encoding.words + layout.gamma.representation.encoding.words +
      layout.xi.representation.encoding.words + layout.table.representation.encoding.words +
      layout.hashTokens.representation.encoding.words + layout.signTokens.representation.encoding.words := by
  change (_ + (_ + (_ + _))) + (_ + (_ + _)) = (_ + _) + _ + _ + _ + _ + _
  dsimp only [Layouts.message, Layouts.scalar]
  omega
theorem parts_valid : Valid layout.input.representation.encoding.words (parts layout) := by
  rw [input_words]
  exact prepareParts_valid _ _ _ _ _ _
theorem badParts_valid : Valid layout.input.representation.encoding.words (badParts layout) := by
  rw [input_words]
  exact signatureParts_valid _ _ _ _ _ _
theorem parts_words : words (parts layout) = layout.hashInput.encoding.words := prepareParts_words _ _ _ _ _ _
theorem badParts_words : words (badParts layout) = (WeightedSignatureTail.input layout.signing).encoding.words :=
  signatureParts_words _ _ _ _ _ _

def headerBytes (value : layout.input.Value) :=
  layout.target.representation.encoding.encode ⟨(value.val.1.1, value.val.1.2.1), value.property.1.1, value.property.1.2.1⟩
def gammaBytes (value : layout.input.Value) :=
  layout.gamma.representation.encoding.encode ⟨value.val.1.2.2.1, value.property.1.2.2.1⟩
def xiBytes (value : layout.input.Value) :=
  layout.xi.representation.encoding.encode ⟨value.val.1.2.2.2, value.property.1.2.2.2⟩
def tableBytes (value : layout.input.Value) :=
  layout.table.representation.encoding.encode ⟨value.val.2.1, value.property.2.1⟩
def hashBytes (value : layout.input.Value) :=
  layout.hashTokens.representation.encoding.encode ⟨value.val.2.2.1, value.property.2.2.1⟩
def signBytes (value : layout.input.Value) :=
  layout.signTokens.representation.encoding.encode ⟨value.val.2.2.2, value.property.2.2.2⟩
theorem input_bytes (value : layout.input.Value) :
    layout.input.representation.encoding.encode value =
      headerBytes layout value ++ gammaBytes layout value ++ xiBytes layout value ++
        tableBytes layout value ++ hashBytes layout value ++ signBytes layout value := by
  let message := layout.message.representation.encoding.encode ⟨value.val.1.1, value.property.1.1⟩
  let scalar := layout.scalar.representation.encoding.encode ⟨value.val.1.2.1, value.property.1.2.1⟩
  change (message ++ (scalar ++ (gammaBytes layout value ++ xiBytes layout value))) ++
      (tableBytes layout value ++ (hashBytes layout value ++ signBytes layout value)) =
    (message ++ scalar) ++ gammaBytes layout value ++ xiBytes layout value ++
      tableBytes layout value ++ hashBytes layout value ++ signBytes layout value
  simp only [List.append_assoc]
theorem parts_bytes (value : layout.input.Value) :
    bytes (layout.input.representation.encoding.encode value) (parts layout) =
      layout.hashInput.encoding.encode (layout.preparedValue value) := by
  rw [input_bytes]
  have routed := prepareParts_bytes (headerBytes layout value) (gammaBytes layout value) (xiBytes layout value)
    (tableBytes layout value) (hashBytes layout value) (signBytes layout value)
  change bytes _ (prepareParts _ _ _ _ _ _) =
    ((hashBytes layout value ++ gammaBytes layout value) ++ tableBytes layout value) ++
      (headerBytes layout value ++ (signBytes layout value ++ xiBytes layout value))
  simpa only [headerBytes, gammaBytes, xiBytes, tableBytes, hashBytes, signBytes, Encoding.encode_length] using routed
theorem badParts_bytes (value : layout.input.Value) :
    bytes (layout.input.representation.encoding.encode value) (badParts layout) =
      (WeightedSignatureTail.input layout.signing).encoding.encode (layout.signatureValue value) := by
  rw [input_bytes]
  have routed := signatureParts_bytes (headerBytes layout value) (gammaBytes layout value) (xiBytes layout value)
    (tableBytes layout value) (hashBytes layout value) (signBytes layout value)
  change bytes _ (signatureParts _ _ _ _ _ _) =
    ((signBytes layout value ++ xiBytes layout value) ++ tableBytes layout value) ++ headerBytes layout value
  simpa only [headerBytes, gammaBytes, xiBytes, tableBytes, hashBytes, signBytes, Encoding.encode_length] using routed

def prepare : Realizer .unit layout.input.representation layout.hashInput layout.preparedValue :=
  ByteRoute.realizer _ _ _ (parts layout) layout.signing.rows.accumulation.cache.wordFits
    (parts_valid layout) (parts_words layout) (parts_bytes layout)
def prepareBad : Realizer .unit layout.input.representation (WeightedSignatureTail.input layout.signing) layout.signatureValue :=
  ByteRoute.realizer _ _ _ (badParts layout) layout.signing.rows.accumulation.cache.wordFits
    (badParts_valid layout) (badParts_words layout) (badParts_bytes layout)

end Signatures.Runtime.CaliperBackend.WeightedExtractor
