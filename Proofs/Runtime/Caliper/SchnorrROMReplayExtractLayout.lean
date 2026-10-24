import Proofs.Runtime.Caliper.SchnorrROMReplayForkObservation
import Proofs.Runtime.Caliper.SumContextBounds
import Proofs.Runtime.Caliper.GuardedBranchBounds
import Proofs.Runtime.Caliper.EncodedConstant
import Proofs.Runtime.Caliper.EncodedEquality

/-! Frames for the executed fork extractor. The represented scalar choice is
`.inl` for the uniform fallback and `.inr` for an extracted quotient. Fallback
words, header projections and the final four-scalar frame are executed byte
routes; their byte equations are the only source of the routed values. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Extract
open Caliper BoundedSource SchnorrROMTape ByteRoute
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

abbrev Choice := config.handler.sampler.tape.unit.Value ⊕ config.handler.sampler.tape.scalar.Value
abbrev Forged := (ForgeryHash.forgery config).Value × config.handler.sampler.tape.scalar.Value
abbrev Quad (F G : Type) := (G × G) × ((F × F) × (F × F))

theorem scalar_words : config.handler.sampler.tape.scalar.representation.encoding.words = 1 := rfl
theorem unit_words : config.handler.sampler.tape.unit.representation.encoding.words = 0 := rfl

def choice : Representation w (Choice config) :=
  config.handler.sampler.tape.unit.representation.sum config.handler.sampler.tape.scalar.representation
    (width_pos config.sampler.wordFits) (by change 1 + max 0 1 < 2 ^ w; have := config.sampler.wordFits; omega)
theorem choice_words : (choice config).encoding.words = 2 := rfl

def fallbackValue : Choice config := .inl ⟨(), trivial⟩
def fallbackParts : List (Part w) := [.literal ((choice config).encoding.encode (fallbackValue config))]
theorem fallback_size : ByteRoute.words (fallbackParts config) = (choice config).encoding.words := by
  change ((choice config).encoding.encode (fallbackValue config)).length + 0 = _
  rw [Encoding.encode_length, Nat.add_zero]
/-- The fallback tag is written by stored literal code; the input is ignored. -/
def fallback {X : Type} (input : Representation w X) : Realizer .unit input (choice config) (fun _ => fallbackValue config) :=
  ByteRoute.realizer _ _ _ (fallbackParts config) config.sampler.wordFits trivial (fallback_size config)
    (fun _ => List.append_nil _)

/-! Header projections. -/

def header := ReplaySecond.header config
theorem header_le : (header config).encoding.words ≤ (ReplaySecond.first config).encoding.words := by
  have := ReplaySecond.first_parts config
  unfold ReplaySecond.prefixWords at this
  change (header config).encoding.words ≤ _
  unfold header
  omega
def headers := (header config).prod (header config)
  (ReplaySecond.combinedFits config (by have := header_le config; omega))
def headersValue (value : Terminal.Output config × Terminal.Output config) := (value.1.1, value.2.1)
def headersParts : List (Part w) :=
  [.slice 0 (header config).encoding.words,
   .slice (ReplaySecond.first config).encoding.words (header config).encoding.words]
theorem headers_valid : Valid (pair config).encoding.words (headersParts config) := by
  have := header_le config
  change (0 + _ ≤ _ + _) ∧ (_ + _ ≤ _ + _) ∧ True
  exact ⟨by omega, by omega, trivial⟩
theorem headers_size : ByteRoute.words (headersParts config) = (headers config).encoding.words := by
  change _ + (_ + 0) = _ + _
  omega

theorem first_split (value : Terminal.Output config) :
    (ReplaySecond.first config).encoding.encode value =
      (header config).encoding.encode value.1 ++ ((ReplaySecond.first config).encoding.encode value).drop (header config).encoding.words := by
  obtain ⟨rest, split⟩ : ∃ rest, (ReplaySecond.first config).encoding.encode value = (header config).encoding.encode value.1 ++ rest :=
    ⟨_, by rw [ReplaySecond.first_bytes]; unfold ReplaySecond.prefixBytes; rw [List.append_assoc]; rfl⟩
  rw [split, List.drop_left' (Encoding.encode_length _ _)]

theorem slice_of (before block after : List (Word w)) {offset count : Nat}
    (offsetEq : before.length = offset) (countEq : block.length = count) :
    ((before ++ block ++ after).drop offset).take count = block := by
  subst offsetEq countEq
  exact slice_block before block after

theorem headers_bytes (value : Terminal.Output config × Terminal.Output config) :
    bytes ((pair config).encoding.encode value) (headersParts config) = (headers config).encoding.encode (headersValue config value) := by
  have firstLength := (ReplaySecond.first config).encoding.encode_length value.1
  have one := slice_of [] ((header config).encoding.encode value.1.1)
    (((ReplaySecond.first config).encoding.encode value.1).drop (header config).encoding.words ++
      (ReplaySecond.first config).encoding.encode value.2) rfl (Encoding.encode_length _ _)
  have two := slice_of ((ReplaySecond.first config).encoding.encode value.1) ((header config).encoding.encode value.2.1)
    (((ReplaySecond.first config).encoding.encode value.2).drop (header config).encoding.words) firstLength (Encoding.encode_length _ _)
  rw [List.append_assoc, ← first_split config value.2] at two
  simp only [List.length_nil, List.nil_append] at one
  rw [← List.append_assoc, ← first_split config value.1] at one
  change List.take _ (List.drop 0 (_ ++ _)) ++ (List.take _ (List.drop _ (_ ++ _)) ++ []) = _ ++ _
  rw [one, two, List.append_nil]
  rfl
def headersRoute : Realizer .unit (pair config) (headers config) (headersValue config) :=
  ByteRoute.realizer _ _ _ (headersParts config) config.sampler.wordFits (headers_valid config)
    (headers_size config) (headers_bytes config)

/-! Distribution and second header dispatch frames. -/

theorem forged_le : (ForgeryHash.result config).encoding.words + 1 ≤ (header config).encoding.words := by
  change _ ≤ 1 + max 0 _
  omega
theorem frame_fits : 1 + max (Pairing.unitRepresentation w).encoding.words (ForgeryHash.result config).encoding.words +
    (header config).encoding.words < 2 ^ w :=
  ReplaySecond.combinedFits config (by have := header_le config; have := forged_le config; change 1 + max 0 _ + _ ≤ _; omega)
def distributeFirst := SumContext.distribute (Pairing.unitRepresentation w) (ForgeryHash.result config) (header config)
  config.sampler.wordFits (frame_fits config)
theorem swap_fits : (ForgeryHash.result config).encoding.words + (header config).encoding.words < 2 ^ w :=
  ReplaySecond.combinedFits config (by have := header_le config; have := forged_le config; omega)
def swapFrame := Pairing.swap .unit (by decide) (ForgeryHash.result config) (header config) config.sampler.wordFits (swap_fits config)
theorem second_fits : 1 + max (Pairing.unitRepresentation w).encoding.words (ForgeryHash.result config).encoding.words +
    (ForgeryHash.result config).encoding.words < 2 ^ w :=
  ReplaySecond.combinedFits config (by have := header_le config; have := forged_le config; change 1 + max 0 _ + _ ≤ _; omega)
def distributeSecond := SumContext.distribute (Pairing.unitRepresentation w) (ForgeryHash.result config) (ForgeryHash.result config)
  config.sampler.wordFits (second_fits config)
def forgedPair := (ForgeryHash.result config).prod (ForgeryHash.result config)
  (ReplaySecond.combinedFits config (by have := header_le config; have := forged_le config; omega))

/-! The arithmetic frame: both commitments, both responses and both challenges. -/

def scalars := config.handler.core.arithmetic.scalars
def points := config.handler.core.arithmetic.points
def pairs := (scalars config).prod (scalars config) (config.handler.core.arithmetic.fits_of_le (by
  change (_ + _) + (_ + _) ≤ _; omega))
def quad : Layout w (Quad F G) := (points config).prod (pairs config) (config.handler.core.arithmetic.fits_of_le (by
  change (_ + _) + ((_ + _) + (_ + _)) ≤ _; omega))
theorem quad_words : (quad config).representation.encoding.words =
    2 * config.point.representation.encoding.words + 4 := by
  change (config.point.representation.encoding.words + config.point.representation.encoding.words) + ((1 + 1) + (1 + 1)) = _
  omega

def quadOf (first second : Forged config) : Quad F G :=
  ((first.1.val.2.1, second.1.val.2.1), ((first.1.val.2.2, second.1.val.2.2), (first.2.val, second.2.val)))
theorem quadOf_valid (first second : Forged config) : (quad config).valid (quadOf config first second) :=
  ⟨⟨first.1.property.2.1, second.1.property.2.1⟩, ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩⟩
/-- The routed frame is taken from `(second, first)`, the order produced by
dispatching on the second header after the first one. -/
def gatherValue (value : Forged config × Forged config) : (quad config).Value :=
  ⟨quadOf config value.2 value.1, quadOf_valid config value.2 value.1⟩

section Gather
variable (messageWords pointWords : Nat)
def gatherParts : List (Part w) :=
  let forged := messageWords + pointWords + 2
  [.slice (forged + messageWords) pointWords, .slice messageWords pointWords,
   .slice (forged + messageWords + pointWords) 1, .slice (messageWords + pointWords) 1,
   .slice (forged + messageWords + pointWords + 1) 1, .slice (messageWords + pointWords + 1) 1]

theorem gather_lists (m₁ m₂ p₁ p₂ z₁ z₂ c₁ c₂ : List (Word w))
    (hm₁ : m₁.length = messageWords) (hm₂ : m₂.length = messageWords)
    (hp₁ : p₁.length = pointWords) (hp₂ : p₂.length = pointWords)
    (hz₁ : z₁.length = 1) (hz₂ : z₂.length = 1) (hc₁ : c₁.length = 1) (hc₂ : c₂.length = 1) :
    bytes ((m₂ ++ (p₂ ++ z₂) ++ c₂) ++ (m₁ ++ (p₁ ++ z₁) ++ c₁)) (gatherParts messageWords pointWords) =
      (p₁ ++ p₂) ++ ((z₁ ++ z₂) ++ (c₁ ++ c₂)) := by
  have one := slice_of (m₂ ++ (p₂ ++ z₂) ++ c₂ ++ m₁) p₁ (z₁ ++ c₁)
    (offset := messageWords + pointWords + 2 + messageWords) (by simp only [List.length_append]; omega) hp₁
  have two := slice_of m₂ p₂ (z₂ ++ c₂ ++ (m₁ ++ (p₁ ++ z₁) ++ c₁)) hm₂ hp₂
  have three := slice_of (m₂ ++ (p₂ ++ z₂) ++ c₂ ++ m₁ ++ p₁) z₁ c₁
    (offset := messageWords + pointWords + 2 + messageWords + pointWords) (by simp only [List.length_append]; omega) hz₁
  have four := slice_of (m₂ ++ p₂) z₂ (c₂ ++ (m₁ ++ (p₁ ++ z₁) ++ c₁))
    (offset := messageWords + pointWords) (by simp only [List.length_append]; omega) hz₂
  have five := slice_of (m₂ ++ (p₂ ++ z₂) ++ c₂ ++ m₁ ++ p₁ ++ z₁) c₁ []
    (offset := messageWords + pointWords + 2 + messageWords + pointWords + 1) (by simp only [List.length_append]; omega) hc₁
  have six := slice_of (m₂ ++ p₂ ++ z₂) c₂ (m₁ ++ (p₁ ++ z₁) ++ c₁)
    (offset := messageWords + pointWords + 1) (by simp only [List.length_append]; omega) hc₂
  simp only [List.append_assoc, List.append_nil] at one two three four five six
  simp only [gatherParts, bytes, List.append_assoc, List.append_nil]
  rw [one, two, three, four, five, six]
end Gather

theorem gather_valid : Valid (forgedPair config).encoding.words
    (gatherParts (w := w) config.message.representation.encoding.words config.point.representation.encoding.words) := by
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ True
  have : (forgedPair config).encoding.words =
      2 * (config.message.representation.encoding.words + config.point.representation.encoding.words + 2) := by
    change (config.message.representation.encoding.words + (config.point.representation.encoding.words + 1)) + 1 +
      ((config.message.representation.encoding.words + (config.point.representation.encoding.words + 1)) + 1) = _
    omega
  rw [this]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega
theorem gather_size : ByteRoute.words
    (gatherParts (w := w) config.message.representation.encoding.words config.point.representation.encoding.words) =
      (quad config).representation.encoding.words := by
  rw [quad_words]
  change _ + (_ + (1 + (1 + (1 + (1 + 0))))) = _
  omega
theorem gather_bytes (value : Forged config × Forged config) :
    bytes ((forgedPair config).encoding.encode value)
      (gatherParts (w := w) config.message.representation.encoding.words config.point.representation.encoding.words) =
      (quad config).representation.encoding.encode (gatherValue config value) := by
  rcases value with ⟨⟨⟨⟨m₂, p₂, z₂⟩, vm₂, vp₂, vz₂⟩, c₂⟩, ⟨⟨⟨m₁, p₁, z₁⟩, vm₁, vp₁, vz₁⟩, c₁⟩⟩
  exact gather_lists _ _ _ _ _ _ _ _ _ _ (Encoding.encode_length _ _) (Encoding.encode_length _ _)
    (Encoding.encode_length _ _) (Encoding.encode_length _ _) (Encoding.encode_length _ _)
    (Encoding.encode_length _ _) (Encoding.encode_length _ _) (Encoding.encode_length _ _)
def gather : Realizer .unit (forgedPair config) (quad config).representation (gatherValue config) :=
  ByteRoute.realizer _ _ _ _ config.sampler.wordFits (gather_valid config) (gather_size config) (gather_bytes config)

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Extract
