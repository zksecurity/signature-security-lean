import Proofs.Runtime.Caliper.SchnorrAGMReadLayout

/-! Byte-level boundaries of the complete read frames. The metadata prefix
contains the basis, signing history and malformed flag; its final word is the
mutable bad flag. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Read
open Caliper BoundedSource
variable {w qH qS : Nat} {M F G : Type}
    (layout : Layouts w M F G qH qS)

def metadataPrefix (value : layout.metadata.Value) : List (Word w) :=
  layout.basis.representation.encoding.encode ⟨value.val.1, value.property.1⟩ ++
    layout.signed.representation.encoding.encode ⟨value.val.2.1, value.property.2.1⟩ ++
      [if value.val.2.2.1 then 1 else 0]

def prefixWords : Nat := layout.basis.representation.encoding.words + layout.signed.representation.encoding.words + 1

theorem prefix_length (value : layout.metadata.Value) :
    (metadataPrefix layout value).length = prefixWords layout := by
  simp only [metadataPrefix, List.length_append, Encoding.encode_length, List.length_cons, List.length_nil, prefixWords]

theorem metadata_words : layout.metadata.representation.encoding.words = prefixWords layout + 1 := by
  change _ + (_ + (1 + 1)) = _ + _ + 1 + 1
  omega

theorem metadata_bytes (value : layout.metadata.Value) :
    layout.metadata.representation.encoding.encode value = metadataPrefix layout value ++ [if value.val.2.2.2 then 1 else 0] := by
  change _ ++ (_ ++ ([if value.val.2.2.1 then 1 else 0] ++ [if value.val.2.2.2 then 1 else 0])) = _
  simp only [metadataPrefix, List.append_assoc]
  rfl

variable [Zero F] [DecidableEq M] [DecidableEq G]

theorem packed_bytes (zeroValid : layout.scalar.valid 0) (value : (input layout).Value) :
    (packed layout).encoding.encode (packValue layout zeroValid value) =
      layout.key.representation.encoding.encode (inputKey layout value) ++
        layout.scalar.representation.encoding.encode ⟨0, zeroValid⟩ ++ [0] ++
        (layout.affine.representation.encoding.encode (inputAffine layout value) ++
          layout.cache.lookup.table.representation.encoding.encode (inputTable layout value)) ++
        layout.affine.representation.encoding.encode (inputAffine layout value) ++
        [if value.val.2.2.2.2.2.2 then 1 else 0] ++
        layout.metadata.representation.encoding.encode (inputMetadata layout value) := by
  change ((_ ++ ((_ ++ ([0] ++ _)) ++ (_ ++ []))) ++ (_ ++ [if value.val.2.2.2.2.2.2 then 1 else 0])) ++ _ = _
  simp only [List.append_nil, List.append_assoc]
  rfl

def returnedChallenge (value : Returned layout) : layout.scalar.Value :=
  ⟨value.1.1.val.1.1, value.1.1.property.1.1⟩
def returnedEntry (value : Returned layout) : layout.entry.Value := ⟨value.1.1.val.1, value.1.1.property.1⟩
def returnedTable (value : Returned layout) : layout.cache.lookup.table.Value := ⟨value.1.1.val.2, value.1.1.property.2⟩
def returnedAffine (value : Returned layout) : layout.affine.Value := ⟨value.1.2.val.1, value.1.2.property.1⟩

omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem returned_bytes (value : Returned layout) : (returned layout).encoding.encode value =
    (layout.entry.representation.encoding.encode (returnedEntry layout value) ++
      layout.cache.lookup.table.representation.encoding.encode (returnedTable layout value)) ++
        (layout.affine.representation.encoding.encode (returnedAffine layout value) ++ [if value.1.2.val.2 then 1 else 0]) ++
          layout.metadata.representation.encoding.encode value.2 := rfl

omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem result_bytes (value : Returned layout) : (output layout).representation.encoding.encode (returnValue layout value) =
    layout.scalar.representation.encoding.encode (returnedChallenge layout value) ++
      layout.cache.lookup.table.representation.encoding.encode (returnedTable layout value) ++
        metadataPrefix layout value.2 ++ [if value.1.2.val.2 then 1 else 0] := by
  change _ ++ (_ ++ (_ ++ (_ ++ ([if value.2.val.2.2.1 then 1 else 0] ++ [if value.1.2.val.2 then 1 else 0])))) = _
  simp only [metadataPrefix, List.append_assoc]
  rfl

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Read
