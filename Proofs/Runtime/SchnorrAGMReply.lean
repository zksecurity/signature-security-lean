import Proofs.Runtime.SchnorrAGMEncoding

/-! Tuple/list representations of Schnorr's one-group-family messages. These
maps state representation relations; actual reply constructors are compiled and
charged by the handlers that use them. -/

namespace Signatures.Runtime.SchnorrAGM.Native

open AlgebraicGroupModel.Interaction

abbrev groupReplyTy (dataTy : Ty CryptoAtom) : Ty CryptoAtom := .pair dataTy (.list point₁)
abbrev scalarGroupReplyTy : Ty CryptoAtom := groupReplyTy scalar

def encodeGroupReply {A G : Type} (reply : Message A (Schnorr.AGM.Group G)) : A × List G :=
  (reply.data, reply.groups ())

def decodeGroupReply {A G : Type} (reply : A × List G) : Message A (Schnorr.AGM.Group G) :=
  ⟨reply.1, fun _ => reply.2⟩

@[simp] theorem encode_decodeGroupReply {A G : Type} (reply : A × List G) :
    encodeGroupReply (decodeGroupReply reply) = reply := rfl

@[simp] theorem decode_encodeGroupReply {A G : Type} (reply : Message A (Schnorr.AGM.Group G)) :
    decodeGroupReply (encodeGroupReply reply) = reply := by
  rcases reply with ⟨d, groups⟩
  congr 1

@[simp] theorem encode_scalarReply {F G : Type} (c : F) :
    encodeGroupReply (Schnorr.AGM.scalarReply (G := G) c) = (c, []) := rfl

@[simp] theorem encode_signingReply {F G : Type} (R : G) (z : F) :
    encodeGroupReply (Schnorr.AGM.signingReply R z) = (z, [R]) := rfl

end Signatures.Runtime.SchnorrAGM.Native
