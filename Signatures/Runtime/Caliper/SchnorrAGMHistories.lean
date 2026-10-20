import Signatures.Runtime.Caliper.SchnorrAGMHistoriesAppend
import Signatures.Runtime.Caliper.SchnorrAGMReachability

/-! Complete signing history update with the original source function as its
specification. Only the basis and signed-message list grow; cache arguments,
signature and both source flags are copied through the actual program. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Histories
open Caliper BoundedSource
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

def updatedSignedFlags : Implementation .unit layout.input layout.scheme.signedFlags
    (fun input => (input.2.2.2.2.2.1 ++ [input.2.2.2.1], input.2.2.2.2.2.2)) :=
  combine layout (appendSigned layout) (selectFlags layout)
    ((appendSigned_buffers layout).trans (by decide)) (by have := selection_buffers layout; omega)
    (by have := layout.field_sizes; omega) (by have := layout.field_sizes; omega)
theorem updatedSignedFlags_buffers : (updatedSignedFlags layout).program.code.memBound ≤ 5 :=
  combine_buffers layout _ _ _ _ _ _ (appendSigned_buffers layout) (selection_buffers layout).2.2.2.2.2.2

def updatedMetadata : Implementation .unit layout.input layout.scheme.metadata
    (fun input => (input.2.2.2.2.1 ++ [input.2.2.1], input.2.2.2.2.2.1 ++ [input.2.2.2.1], input.2.2.2.2.2.2)) :=
  combine layout (appendBasis layout) (updatedSignedFlags layout)
    ((appendBasis_buffers layout).trans (by decide)) ((updatedSignedFlags_buffers layout).trans (by decide))
    (by have := layout.field_sizes; omega) (by have := layout.field_sizes; omega)
theorem updatedMetadata_buffers : (updatedMetadata layout).program.code.memBound ≤ 6 :=
  combine_buffers layout _ _ _ _ _ _ (appendBasis_buffers layout) (updatedSignedFlags_buffers layout)

def updatedSaved : Implementation .unit layout.input layout.saved
    (fun input => (input.2.1, input.2.2.2.2.1 ++ [input.2.2.1], input.2.2.2.2.2.1 ++ [input.2.2.2.1], input.2.2.2.2.2.2)) :=
  combine layout (selectReply layout) (updatedMetadata layout)
    (by have := selection_buffers layout; omega) ((updatedMetadata_buffers layout).trans (by decide))
    (by have := layout.field_sizes; omega) (by have := layout.field_sizes; omega)
theorem updatedSaved_buffers : (updatedSaved layout).program.code.memBound ≤ 7 :=
  combine_buffers layout _ _ _ _ _ _ (selection_buffers layout).2.1 (updatedMetadata_buffers layout)

def implementation : Implementation .unit layout.input layout.output Signatures.Runtime.SchnorrAGM.Native.Signing.historiesValue :=
  combine layout (selectCache layout) (updatedSaved layout)
    (by have := selection_buffers layout; omega) ((updatedSaved_buffers layout).trans (by decide))
    (by have := layout.field_sizes; omega) (by have := layout.field_sizes; omega)
theorem buffers : (implementation layout).program.code.memBound ≤ 8 :=
  combine_buffers layout _ _ _ _ _ _ (selection_buffers layout).1 (updatedSaved_buffers layout)

theorem names (slots : Nat) : NamesAccounted (implementation layout).program.code slots := by
  have signedFlags : NamesAccounted (updatedSignedFlags layout).program.code slots :=
    combine_names layout _ _ _ _ _ _ slots (appendSigned_names layout slots) (selection_names layout slots).2.2.2.2.2.2
  have metadata : NamesAccounted (updatedMetadata layout).program.code slots :=
    combine_names layout _ _ _ _ _ _ slots (appendBasis_names layout slots) signedFlags
  have saved : NamesAccounted (updatedSaved layout).program.code slots :=
    combine_names layout _ _ _ _ _ _ slots (selection_names layout slots).2.1 metadata
  exact combine_names layout _ _ _ _ _ _ slots (selection_names layout slots).1 saved

theorem room_arithmetic [Zero F] [SMul F G] [Sub G] [Neg F] (input : Input M F G) :
    layout.room (Arithmetic.value input) ↔ input.2.2.2.2.2.1.length < qS + 2 ∧ input.2.2.2.2.2.2.1.length < qS := Iff.rfl

theorem reserved_room [Field F] [AddCommGroup G] [Module F G] {hashes signatures : Nat}
    {state : Signatures.Runtime.SchnorrAGM.State F G M} (room : layout.scheme.Reserved hashes (signatures + 1) state)
    (challenge response : F) (generator publicKey : G) (message : M) :
    layout.room (Arithmetic.value ((challenge, response), generator, publicKey, message, Signatures.Runtime.SchnorrAGM.Native.encodeState state)) := by
  rw [room_arithmetic]
  dsimp only [Signatures.Runtime.SchnorrAGM.Native.encodeState, Signatures.Runtime.SchnorrAGM.Native.encodeMetadata]
  simp only [List.length_map]
  exact ⟨by have := room.2.2.1; omega, by have := room.2.2.2; omega⟩

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Histories
