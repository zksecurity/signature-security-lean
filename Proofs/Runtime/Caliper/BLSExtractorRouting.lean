import Proofs.Runtime.Caliper.BLSExtractorLayout
import Proofs.Runtime.Caliper.StructuralNames

/-! Initial extraction routing is a single executed assembly of bounded slices.
The source contains the target/beta, both explanations, cache, and both logs.
The bad branch discards the hash explanation/log only after admitting and
accounting for that complete source encoding. -/
namespace Signatures.Runtime.CaliperBackend.BLSExtractorFrame
open Caliper BoundedSource Assembly
variable {w : Nat}

def prepareOperands (header coefficients entries tokens : Nat) : List (Operand w) :=
  reads 0 (header + coefficients + coefficients + entries) tokens ++
  reads 0 header coefficients ++ reads 0 (header + coefficients + coefficients) entries ++
  reads 0 0 header ++ reads 0 (header + coefficients + coefficients + entries + tokens) tokens ++
  reads 0 (header + coefficients) coefficients
def signatureOperands (header coefficients entries tokens : Nat) : List (Operand w) :=
  reads 0 (header + coefficients + coefficients + entries + tokens) tokens ++
  reads 0 (header + coefficients) coefficients ++
  reads 0 (header + coefficients + coefficients) entries ++ reads 0 0 header

theorem prepareOperands_length (header coefficients entries tokens : Nat) :
    (prepareOperands (w := w) header coefficients entries tokens).length =
      ((tokens + coefficients) + entries) + (header + (tokens + coefficients)) := by
  simp only [prepareOperands, List.length_append, reads_length]
  omega
theorem signatureOperands_length (header coefficients entries tokens : Nat) :
    (signatureOperands (w := w) header coefficients entries tokens).length =
      ((tokens + coefficients) + entries) + header := by
  simp only [signatureOperands, List.length_append, reads_length]

theorem prepareOperands_names (header coefficients entries tokens : Nat) :
    SourcesBound (prepareOperands (w := w) header coefficients entries tokens) 1 := by
  simp only [prepareOperands, sourcesBound_append]
  exact ⟨⟨⟨⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩, sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩, sourcesBound_reads _ _ _ _ (by decide)⟩
theorem signatureOperands_names (header coefficients entries tokens : Nat) :
    SourcesBound (signatureOperands (w := w) header coefficients entries tokens) 1 := by
  simp only [signatureOperands, sourcesBound_append]
  exact ⟨⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩, sourcesBound_reads _ _ _ _ (by decide)⟩

theorem prepareOperands_fit (header coefficients entries tokens : Nat) :
    ∀ operand ∈ prepareOperands (w := w) header coefficients entries tokens, operand.NamesFit := by
  intro operand member
  simp only [prepareOperands, List.mem_append] at member
  rcases member with ((((member | member) | member) | member) | member) | member <;>
    exact reads_namesFit 0 _ _ (by positivity) operand member
theorem signatureOperands_fit (header coefficients entries tokens : Nat) :
    ∀ operand ∈ signatureOperands (w := w) header coefficients entries tokens, operand.NamesFit := by
  intro operand member
  simp only [signatureOperands, List.mem_append] at member
  rcases member with ((member | member) | member) | member <;>
    exact reads_namesFit 0 _ _ (by positivity) operand member

theorem prepareOperands_valid (header coefficients entries tokens : Nat) (before : State w)
    (size : (before.bufs 0).size = header + coefficients + coefficients + entries + tokens + tokens)
    (fits : (before.bufs 0).size < 2 ^ w) : Valid 1 before (prepareOperands header coefficients entries tokens) := by
  intro operand member
  simp only [prepareOperands, List.mem_append] at member
  rcases member with ((((member | member) | member) | member) | member) | member <;>
    exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member
theorem signatureOperands_valid (header coefficients entries tokens : Nat) (before : State w)
    (size : (before.bufs 0).size = header + coefficients + coefficients + entries + tokens + tokens)
    (fits : (before.bufs 0).size < 2 ^ w) : Valid 1 before (signatureOperands header coefficients entries tokens) := by
  intro operand member
  simp only [signatureOperands, List.mem_append] at member
  rcases member with ((member | member) | member) | member <;>
    exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member

theorem prepareOperands_values (header gamma xi entries hashes signatures : List (Word w))
    (coefficients : xi.length = gamma.length) (tokens : signatures.length = hashes.length) (before : State w)
    (contents : (before.bufs 0).toList = header ++ gamma ++ xi ++ entries ++ hashes ++ signatures) :
    values (prepareOperands header.length gamma.length entries.length hashes.length) before =
      ((hashes ++ gamma) ++ entries) ++ (header ++ (signatures ++ xi)) := by
  have h := ListFold.reads_block (header ++ gamma ++ xi ++ entries) hashes signatures before
    (by simpa only [List.append_assoc] using contents)
  have g := ListFold.reads_block header gamma (xi ++ entries ++ hashes ++ signatures) before
    (by simpa only [List.append_assoc] using contents)
  have e := ListFold.reads_block (header ++ gamma ++ xi) entries (hashes ++ signatures) before
    (by simpa only [List.append_assoc] using contents)
  have b := ListFold.reads_block [] header (gamma ++ xi ++ entries ++ hashes ++ signatures) before
    (by simpa only [List.nil_append, List.append_assoc] using contents)
  have s := ListFold.reads_block (header ++ gamma ++ xi ++ entries ++ hashes) signatures [] before
    (by simpa only [List.append_nil, List.append_assoc] using contents)
  have x := ListFold.reads_block (header ++ gamma) xi (entries ++ hashes ++ signatures) before
    (by simpa only [List.append_assoc] using contents)
  simp only [List.length_append, List.length_nil, coefficients, tokens, values] at h g e b s x
  simp only [prepareOperands, values, List.map_append, h, g, e, b, s, x, List.append_assoc]
theorem signatureOperands_values (header gamma xi entries hashes signatures : List (Word w))
    (coefficients : xi.length = gamma.length) (tokens : signatures.length = hashes.length) (before : State w)
    (contents : (before.bufs 0).toList = header ++ gamma ++ xi ++ entries ++ hashes ++ signatures) :
    values (signatureOperands header.length gamma.length entries.length hashes.length) before =
      ((signatures ++ xi) ++ entries) ++ header := by
  have s := ListFold.reads_block (header ++ gamma ++ xi ++ entries ++ hashes) signatures [] before
    (by simpa only [List.append_nil, List.append_assoc] using contents)
  have x := ListFold.reads_block (header ++ gamma) xi (entries ++ hashes ++ signatures) before
    (by simpa only [List.append_assoc] using contents)
  have e := ListFold.reads_block (header ++ gamma ++ xi) entries (hashes ++ signatures) before
    (by simpa only [List.append_assoc] using contents)
  have b := ListFold.reads_block [] header (gamma ++ xi ++ entries ++ hashes ++ signatures) before
    (by simpa only [List.nil_append, List.append_assoc] using contents)
  simp only [List.length_append, List.length_nil, coefficients, tokens, values] at s x e b
  simp only [signatureOperands, values, List.map_append, s, x, e, b]

variable {M G F R : Type} (layout : TokenEvaluation.Layouts w M G F R)
theorem input_bytes (value : (input layout).Value) :
    (input layout).representation.encoding.encode value =
      (target layout).representation.encoding.encode ⟨(value.val.1.1, value.val.1.2.1), value.property.1.1, value.property.1.2.1⟩ ++
      (coefficients layout).representation.encoding.encode ⟨value.val.1.2.2.1, value.property.1.2.2.1⟩ ++
      (coefficients layout).representation.encoding.encode ⟨value.val.1.2.2.2, value.property.1.2.2.2⟩ ++
      (table layout).representation.encoding.encode ⟨value.val.2.1, value.property.2.1⟩ ++
      (tokens layout).representation.encoding.encode ⟨value.val.2.2.1, value.property.2.2.1⟩ ++
      (tokens layout).representation.encoding.encode ⟨value.val.2.2.2, value.property.2.2.2⟩ := by
  let m := (message layout).representation.encoding.encode ⟨value.val.1.1, value.property.1.1⟩
  let b := (scalar layout).representation.encoding.encode ⟨value.val.1.2.1, value.property.1.2.1⟩
  let g := (coefficients layout).representation.encoding.encode ⟨value.val.1.2.2.1, value.property.1.2.2.1⟩
  let x := (coefficients layout).representation.encoding.encode ⟨value.val.1.2.2.2, value.property.1.2.2.2⟩
  let e := (table layout).representation.encoding.encode ⟨value.val.2.1, value.property.2.1⟩
  let h := (tokens layout).representation.encoding.encode ⟨value.val.2.2.1, value.property.2.2.1⟩
  let s := (tokens layout).representation.encoding.encode ⟨value.val.2.2.2, value.property.2.2.2⟩
  change (m ++ (b ++ (g ++ x))) ++ (e ++ (h ++ s)) = (m ++ b) ++ g ++ x ++ e ++ h ++ s
  simp only [List.append_assoc]

def prepare : Realizer .unit (input layout).representation (prepared layout).representation (prepareValue layout) :=
  Assembly.realizer .unit (by decide) _ _ _
    (prepareOperands (target layout).representation.encoding.words (coefficients layout).representation.encoding.words
      (table layout).representation.encoding.words (tokens layout).representation.encoding.words)
    layout.rows.accumulation.cache.wordFits (prepareOperands_length _ _ _ _) (prepareOperands_fit _ _ _ _)
    (by
      intro value state represented
      have size := represented_size _ represented
      change (state.bufs 0).size = (_ + (_ + (_ + _))) + (_ + (_ + _)) at size
      exact prepareOperands_valid _ _ _ _ state (by change _ = (_ + _) + _ + _ + _ + _ + _; omega)
        (by rw [Assembly.represented_size _ represented]; exact (input layout).representation.fits))
    (by
      intro value state represented
      have result := prepareOperands_values
        ((target layout).representation.encoding.encode ⟨(value.val.1.1, value.val.1.2.1), value.property.1.1, value.property.1.2.1⟩)
        ((coefficients layout).representation.encoding.encode ⟨value.val.1.2.2.1, value.property.1.2.2.1⟩)
        ((coefficients layout).representation.encoding.encode ⟨value.val.1.2.2.2, value.property.1.2.2.2⟩)
        ((table layout).representation.encoding.encode ⟨value.val.2.1, value.property.2.1⟩)
        ((tokens layout).representation.encoding.encode ⟨value.val.2.2.1, value.property.2.2.1⟩)
        ((tokens layout).representation.encoding.encode ⟨value.val.2.2.2, value.property.2.2.2⟩)
        (by simp only [Encoding.encode_length]) (by simp only [Encoding.encode_length]) state
        (represented.2.1.trans (input_bytes layout value))
      simp only [Encoding.encode_length] at result
      exact result)

def selectSignature : Realizer .unit (input layout).representation (signatureInput layout).representation (signatureValue layout) :=
  Assembly.realizer .unit (by decide) _ _ _
    (signatureOperands (target layout).representation.encoding.words (coefficients layout).representation.encoding.words
      (table layout).representation.encoding.words (tokens layout).representation.encoding.words)
    layout.rows.accumulation.cache.wordFits (signatureOperands_length _ _ _ _) (signatureOperands_fit _ _ _ _)
    (by
      intro value state represented
      have size := represented_size _ represented
      change (state.bufs 0).size = (_ + (_ + (_ + _))) + (_ + (_ + _)) at size
      exact signatureOperands_valid _ _ _ _ state (by change _ = (_ + _) + _ + _ + _ + _ + _; omega)
        (by rw [Assembly.represented_size _ represented]; exact (input layout).representation.fits))
    (by
      intro value state represented
      have result := signatureOperands_values
        ((target layout).representation.encoding.encode ⟨(value.val.1.1, value.val.1.2.1), value.property.1.1, value.property.1.2.1⟩)
        ((coefficients layout).representation.encoding.encode ⟨value.val.1.2.2.1, value.property.1.2.2.1⟩)
        ((coefficients layout).representation.encoding.encode ⟨value.val.1.2.2.2, value.property.1.2.2.2⟩)
        ((table layout).representation.encoding.encode ⟨value.val.2.1, value.property.2.1⟩)
        ((tokens layout).representation.encoding.encode ⟨value.val.2.2.1, value.property.2.2.1⟩)
        ((tokens layout).representation.encoding.encode ⟨value.val.2.2.2, value.property.2.2.2⟩)
        (by simp only [Encoding.encode_length]) (by simp only [Encoding.encode_length]) state
        (represented.2.1.trans (input_bytes layout value))
      simp only [Encoding.encode_length] at result
      exact result)

end Signatures.Runtime.CaliperBackend.BLSExtractorFrame
