import Proofs.Runtime.Caliper.SchnorrROMForgeryHashLayout

/-! Duplicate the forgery before the final hash and reconstruct the returned
forgery/challenge/store with literal word copies. The response is retained too. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ForgeryHash
open Caliper BoundedSource ByteRoute
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

def prepareParts : List (Part w) :=
  [.slice 0 config.handler.core.key.representation.encoding.words,
   .slice (forgery config).representation.encoding.words config.handler.store.representation.encoding.words,
   .slice 0 (forgery config).representation.encoding.words]
theorem prepare_valid : Valid (input config).encoding.words (prepareParts config) := by
  change Valid ((forgery config).representation.encoding.words + config.handler.store.representation.encoding.words) _
  simp only [prepareParts, Valid]
  have key : config.handler.core.key.representation.encoding.words ≤ (forgery config).representation.encoding.words := by
    change config.message.representation.encoding.words + config.point.representation.encoding.words ≤
      config.message.representation.encoding.words + (config.point.representation.encoding.words + 1)
    omega
  exact ⟨by omega, by omega, by omega, trivial⟩
theorem prepare_size : words (prepareParts config) = (rawPrepared config).encoding.words := by
  simp only [prepareParts, words]
  change _ + (_ + (_ + 0)) = (_ + _) + _
  omega
theorem prepare_bytes (value : Input config) : bytes ((input config).encoding.encode value) (prepareParts config) =
    (rawPrepared config).encoding.encode (rawPrepareValue config value) := by
  let keyBytes := config.handler.core.key.representation.encoding.encode
    ⟨key config value.1, value.1.property.1, value.1.property.2.1⟩
  let response := config.handler.sampler.tape.scalar.representation.encoding.encode ⟨value.1.val.2.2, value.1.property.2.2⟩
  let forge := (forgery config).representation.encoding.encode value.1
  let saved := config.handler.store.representation.encoding.encode value.2
  have keyLength : keyBytes.length = config.handler.core.key.representation.encoding.words := Encoding.encode_length _ _
  have forgeLength : forge.length = (forgery config).representation.encoding.words := Encoding.encode_length _ _
  have savedLength : saved.length = config.handler.store.representation.encoding.words := Encoding.encode_length _ _
  have split : forge = keyBytes ++ response := by
    change _ ++ (_ ++ _) = (_ ++ _) ++ _
    exact (List.append_assoc _ _ _).symm
  have one := slice_block [] keyBytes (response ++ saved)
  have two := slice_block forge saved []
  have three := slice_block [] forge saved
  simp only [List.length_nil, List.nil_append, List.append_nil, keyLength, forgeLength, savedLength] at one two three
  change bytes (forge ++ saved) (prepareParts config) = (keyBytes ++ saved) ++ forge
  simp only [prepareParts, bytes, List.append_nil]
  rw [two, three]
  rw [split, List.append_assoc, one]
  simp only [List.append_assoc]

def rawPrepare : Realizer .unit (input config) (rawPrepared config) (rawPrepareValue config) :=
  ByteRoute.realizer _ _ _ (prepareParts config) config.sampler.wordFits
    (prepare_valid config) (prepare_size config) (prepare_bytes config)

def finishParts : List (Part w) :=
  [.slice (FinalHash.output config).representation.encoding.words (forgery config).representation.encoding.words,
   .slice 0 (FinalHash.output config).representation.encoding.words]
theorem finish_valid : Valid (finished config).encoding.words (finishParts config) := by
  simp only [finishParts, Valid]
  change _ + _ ≤ _ + _ ∧ 0 + _ ≤ _ + _ ∧ True
  exact ⟨le_rfl, by omega, trivial⟩
theorem finish_size : words (finishParts config) = (output config).encoding.words := by
  simp only [finishParts, words]
  change _ + ((1 + _) + 0) = (_ + 1) + _
  omega
theorem finish_bytes (value : (FinalHash.output config).Value × (forgery config).Value) :
    bytes ((finished config).encoding.encode value) (finishParts config) = (output config).encoding.encode (finishValue config value) := by
  let hashed := (FinalHash.output config).representation.encoding.encode value.1
  let forge := (forgery config).representation.encoding.encode value.2
  have hashedLength : hashed.length = (FinalHash.output config).representation.encoding.words := Encoding.encode_length _ _
  have forgeLength : forge.length = (forgery config).representation.encoding.words := Encoding.encode_length _ _
  have one := slice_block hashed forge []
  have two := slice_block [] hashed forge
  simp only [List.length_nil, List.nil_append, List.append_nil, hashedLength, forgeLength] at one two
  change bytes (hashed ++ forge) (finishParts config) = (_ ++ _) ++ _
  simp only [finishParts, bytes, List.append_nil]
  rw [one, two, List.append_assoc]
  rfl
def finish : Realizer .unit (finished config) (output config) (finishValue config) :=
  ByteRoute.realizer _ _ _ (finishParts config) config.sampler.wordFits
    (finish_valid config) (finish_size config) (finish_bytes config)

variable [Zero F] [DecidableEq M] [DecidableEq G]
def prepare : Realizer .unit (admitted config) (prepared config) (prepareValue config) :=
  ((rawPrepare config).viewInput (admitted config) Subtype.val (fun _ => rfl)).viewOutput
    (prepared config) (prepareValue config) (fun _ => rfl)

end Signatures.Runtime.CaliperBackend.SchnorrROM.ForgeryHash
