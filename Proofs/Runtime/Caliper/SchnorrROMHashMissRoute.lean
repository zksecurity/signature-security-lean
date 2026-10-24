import Proofs.Runtime.Caliper.SchnorrROMFinalHashBounds

/-! A managed-cache miss calls final hashing while retaining the requested key.
Both duplication and restoration of that key execute charged byte routes. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.HashMiss
open Caliper BoundedSource ByteRoute SchnorrROMTape
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

abbrev input := FinalHash.rawInput config
def prepared := (input config).representation.prod config.handler.core.key.representation
  (config.handler.fits_of_le (by
    have := FinalHash.key_le config; have := FinalHash.store_le config
    change (_ + _) + _ ≤ _; omega))
def finished := (FinalHash.output config).representation.prod config.handler.core.key.representation
  (config.handler.fits_of_le (by
    have := FinalHash.key_le config; have := FinalHash.store_le config
    have positive : 0 < config.handler.width := by change 0 < 1 + _ + _ + _ + _ + _; omega
    change (1 + _) + _ ≤ _; omega))
def output := config.handler.sampler.tape.scalar.representation.prod (input config).representation
  (config.handler.fits_of_le (by
    have := FinalHash.key_le config; have := FinalHash.store_le config
    have positive : 0 < config.handler.width := by change 0 < 1 + _ + _ + _ + _ + _; omega
    change 1 + (_ + _) ≤ _; omega))

def prepareValue (value : (input config).Value) : (input config).Value × config.handler.core.key.Value :=
  (value, ⟨value.val.1, value.property.1⟩)
def finishValue (value : (FinalHash.output config).Value × config.handler.core.key.Value) :
    config.handler.sampler.tape.scalar.Value × (input config).Value :=
  (⟨value.1.val.1, value.1.property.1⟩, ⟨(value.2.val, value.1.val.2), value.2.property, value.1.property.2⟩)

def prepareParts : List (Part w) :=
  [.slice 0 (input config).representation.encoding.words,
   .slice 0 config.handler.core.key.representation.encoding.words]
theorem prepare_valid : Valid (input config).representation.encoding.words (prepareParts config) := by
  change (0 + (_ + _) ≤ _ + _) ∧ (0 + _ ≤ _ + _) ∧ True
  exact ⟨by omega, by omega, trivial⟩
theorem prepare_size : words (prepareParts config) = (prepared config).encoding.words := by
  simp only [prepareParts, words, Nat.add_zero]
  rfl
theorem prepare_bytes (value : (input config).Value) :
    bytes ((input config).representation.encoding.encode value) (prepareParts config) =
      (prepared config).encoding.encode (prepareValue config value) := by
  let key := config.handler.core.key.representation.encoding.encode ⟨value.val.1, value.property.1⟩
  let saved := config.handler.store.representation.encoding.encode ⟨value.val.2, value.property.2⟩
  have hk : key.length = config.handler.core.key.representation.encoding.words := Encoding.encode_length _ _
  have hs : saved.length = config.handler.store.representation.encoding.words := Encoding.encode_length _ _
  have all := slice_block [] (key ++ saved) []
  have first := slice_block [] key saved
  simp only [List.length_nil, List.nil_append, List.append_nil, List.length_append, hk, hs] at all first
  change ((key ++ saved).drop 0).take (_ + _) ++ (((key ++ saved).drop 0).take _ ++ []) = (key ++ saved) ++ key
  rw [all, first, List.append_nil]

def prepare : Realizer .unit (input config).representation (prepared config) (prepareValue config) :=
  ByteRoute.realizer _ _ _ (prepareParts config) config.sampler.wordFits
    (prepare_valid config) (prepare_size config) (prepare_bytes config)

def finishParts : List (Part w) :=
  [.slice 0 1,
   .slice (1 + config.handler.store.representation.encoding.words) config.handler.core.key.representation.encoding.words,
   .slice 1 config.handler.store.representation.encoding.words]
theorem finish_valid : Valid (finished config).encoding.words (finishParts config) := by
  change (0 + 1 ≤ (1 + _) + _) ∧ ((1 + _) + _ ≤ (1 + _) + _) ∧ (1 + _ ≤ (1 + _) + _) ∧ True
  exact ⟨by omega, by omega, by omega, trivial⟩
theorem finish_size : words (finishParts config) = (output config).encoding.words := by
  simp only [finishParts, words, Nat.add_zero]
  rfl
theorem finish_bytes (value : (FinalHash.output config).Value × config.handler.core.key.Value) :
    bytes ((finished config).encoding.encode value) (finishParts config) =
      (output config).encoding.encode (finishValue config value) := by
  let scalar := config.handler.sampler.tape.scalar.representation.encoding.encode ⟨value.1.val.1, value.1.property.1⟩
  let saved := config.handler.store.representation.encoding.encode ⟨value.1.val.2, value.1.property.2⟩
  let key := config.handler.core.key.representation.encoding.encode value.2
  have hc : scalar.length = 1 := Encoding.encode_length _ _
  have hs : saved.length = config.handler.store.representation.encoding.words := Encoding.encode_length _ _
  have hk : key.length = config.handler.core.key.representation.encoding.words := Encoding.encode_length _ _
  have first := slice_block [] scalar (saved ++ key)
  have second := slice_block (scalar ++ saved) key []
  have third := slice_block scalar saved key
  simp only [List.length_nil, List.nil_append, List.append_nil, List.length_append, hc, hs, hk,
    List.append_assoc] at first second third
  change (((scalar ++ saved) ++ key).drop 0).take 1 ++
    ((((scalar ++ saved) ++ key).drop (1 + _)).take _ ++ ((((scalar ++ saved) ++ key).drop 1).take _ ++ [])) =
      scalar ++ (key ++ saved)
  simp only [List.append_assoc, List.append_nil]
  rw [first, second, third]

def finish : Realizer .unit (finished config) (output config) (finishValue config) :=
  ByteRoute.realizer _ _ _ (finishParts config) config.sampler.wordFits
    (finish_valid config) (finish_size config) (finish_bytes config)

theorem prepare_time (value) : (prepare config).time value ≤ 8 * (prepared config).encoding.words := ByteRoute.time _ _ _ _ _ _ _ _ _
theorem finish_time (value) : (finish config).time value ≤ 8 * (output config).encoding.words := ByteRoute.time _ _ _ _ _ _ _ _ _
theorem prepare_words : descriptionWords (prepare config).code ≤ 26 * (prepared config).encoding.words + 14 := ByteRoute.codeWords _ _ _ _ _ _ _ _
theorem finish_words : descriptionWords (finish config).code ≤ 26 * (output config).encoding.words + 14 := ByteRoute.codeWords _ _ _ _ _ _ _ _
theorem prepare_buffers : (prepare config).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
theorem finish_buffers : (finish config).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
theorem prepare_names (slots : Nat) : NamesAccounted (prepare config).code slots := ByteRoute.names _ _ _ _ _ _ _ _ _
theorem finish_names (slots : Nat) : NamesAccounted (finish config).code slots := ByteRoute.names _ _ _ _ _ _ _ _ _

end Signatures.Runtime.CaliperBackend.SchnorrROM.HashMiss
