import Proofs.Runtime.Caliper.SchnorrAGMCallerSource

/-! Separate hash/sign reservations follow every supported handler reply.
The private store retains an explicit canonical source-state witness. These
proof-only allowances introduce no extra machine state or uncharged operations. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerHandler
open Caliper BoundedSource OracleComp OracleSpec CallerPackets
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS randomBound : Nat} {M F G : Type}
    (layout : Handler.Layouts w M F G qH qS randomBound)

def hashCharge : Request layout → Nat
  | .inr (.inl _) => 1
  | _ => 0
def signCharge : Request layout → Nat
  | .inr (.inr _) => 1
  | _ => 0
def Allowed (hashes signatures : Nat) (q : Request layout) : Prop :=
  hashCharge layout q ≤ hashes ∧ signCharge layout q ≤ signatures
def replyMatches (q : Request layout) (represented : Reply layout)
    (original : (Interface.sourceSpec F G M).Range (query layout q)) : Prop :=
  replyValue layout represented = (⟨query layout q, original⟩ : Interface.SourceIndex F G M) ∧
    canonicalReply layout represented

variable [Field F]
def Reserved (hashes signatures : Nat) (saved : layout.scheme.store.Value) : Prop :=
  ∃ state, saved.val.2 = encodeState state ∧ layout.scheme.Reserved hashes signatures state

omit [Field F] in
theorem query_valid (q : Request layout) : requestValid layout.scheme.message.valid (query layout q) := by
  rcases q with args | (args | args)
  · trivial
  · exact args.property.1
  · exact args.property.1
omit [Field F] in
theorem query_charges (q : Request layout) :
    _root_.Schnorr.AGM.Reduction.cacheCharge (query layout q) = hashCharge layout q + signCharge layout q ∧
      (if _root_.Schnorr.AGM.Reduction.signRequest (query layout q) then 1 else 0) = signCharge layout q := by
  rcases q with args | (args | args) <;> constructor <;> rfl

theorem Reserved.canonical {hashes signatures : Nat} {saved : layout.scheme.store.Value}
    (room : Reserved layout hashes signatures saved) : encodeState (decodeState saved.val.2) = saved.val.2 := by
  obtain ⟨state, encoded, _⟩ := room
  rw [encoded, decode_encodeState]
theorem Reserved.source {hashes signatures : Nat} {saved : layout.scheme.store.Value}
    (room : Reserved layout hashes signatures saved) : layout.scheme.Reserved hashes signatures (decodeState saved.val.2) := by
  obtain ⟨state, encoded, reserved⟩ := room
  simpa only [encoded, decode_encodeState] using reserved
theorem Reserved.mono {hashes signatures fewerHashes fewerSignatures : Nat} {saved : layout.scheme.store.Value}
    (room : Reserved layout hashes signatures saved) (hashBound : fewerHashes ≤ hashes) (signBound : fewerSignatures ≤ signatures) :
    Reserved layout fewerHashes fewerSignatures saved := by
  obtain ⟨state, encoded, reserved⟩ := room
  exact ⟨state, encoded, reserved.1, by have := reserved.2.1; omega,
    by have := reserved.2.2.1; omega, by have := reserved.2.2.2; omega⟩

variable [DecidableEq M] [DecidableEq G]
theorem ready_of_reserved (value : Packet layout) {hashes signatures : Nat}
    (room : Reserved layout hashes signatures value.2) (allowed : Allowed layout hashes signatures value.1) : ready layout value := by
  obtain ⟨state, encoded, reserved⟩ := room
  rcases value with ⟨args | (args | args), saved⟩
  · trivial
  · change layout.hash.admissible (Handler.hashArgument (args.val, saved.val))
    unfold Handler.hashArgument HashDispatch.Layouts.admissible
    split
    · intro _
      change saved.val.2.1.length ≤ qH + qS
      rw [encoded]
      change (state.cache.map _).length ≤ qH + qS
      rw [List.length_map]
      have := reserved.2.1
      omega
    · trivial
  · have positive : 1 ≤ signatures := allowed.2
    have reserved' : layout.scheme.Reserved hashes ((signatures - 1) + 1) state := by
      convert reserved using 1
      omega
    change layout.signing.admissible (Handler.signingArgument (args.val, saved.val))
    intro _
    change Signing.Sampling.ready layout.histories (saved.val.1.1, saved.val.1.2, args.val.1, saved.val.2)
    rw [encoded]
    exact Signing.Sampling.reserved_ready layout.histories reserved' _ _ _

variable [AddCommGroup G] [Module F G] [DecidableEq F] [SampleableType F]
theorem query_reserved (g pk : G) (state : Signatures.Runtime.SchnorrAGM.State F G M)
    (q : Request layout) {hashes signatures : Nat} (room : layout.scheme.Reserved hashes signatures state)
    (allowed : Allowed layout hashes signatures q)
    (answer : (Interface.sourceSpec F G M).Range (query layout q) × Signatures.Runtime.SchnorrAGM.State F G M)
    (reached : answer ∈ support ((Signatures.Runtime.SchnorrAGM.handler g pk (query layout q)).run state)) :
    layout.scheme.Reserved (hashes - hashCharge layout q) (signatures - signCharge layout q) answer.2 := by
  have growth := Signatures.Runtime.SchnorrAGM.handler_growth g pk state (query layout q) answer reached
  rw [(query_charges layout q).1, (query_charges layout q).2] at growth
  have messages := messages_handler layout.scheme.message.valid g pk state room.1 (query layout q) (query_valid layout q) answer reached
  exact ⟨messages, by have := room.2.1; have := allowed.1; have := allowed.2; omega,
    by have := room.2.2.1; have := allowed.2; omega,
    by have := room.2.2.2; have := allowed.2; omega⟩

variable (ops : Handler.Operations layout) (sampler : ProbComp layout.scheme.scalar.Value)
    (uniform : Subtype.val <$> sampler = ($ᵗ F : ProbComp F))
include uniform in
theorem reserved_after (value : Packet layout) {hashes signatures : Nat}
    (room : Reserved layout hashes signatures value.2) (allowed : Allowed layout hashes signatures value.1)
    (answer : Reply layout × layout.scheme.store.Value) (reached : answer ∈ support (source layout ops sampler value)) :
    Reserved layout (hashes - hashCharge layout value.1) (signatures - signCharge layout value.1) answer.2 := by
  obtain ⟨state, encoded, reserved⟩ := room
  have ready := ready_of_reserved layout value ⟨state, encoded, reserved⟩ allowed
  obtain ⟨original, supported, related⟩ := (synchronizes layout ops sampler uniform value ready state encoded).left_support reached
  have next := query_reserved layout value.2.val.1.1 value.2.val.1.2 state value.1 reserved allowed original supported
  exact ⟨original.2, congrArg Prod.snd related.2, next⟩

def stored (saved : layout.scheme.store.Value) : (G × G) × Signatures.Runtime.SchnorrAGM.State F G M :=
  (saved.val.1, decodeState saved.val.2)
noncomputable def original : QueryImpl (Interface.sourceSpec F G M)
    (StateT ((G × G) × Signatures.Runtime.SchnorrAGM.State F G M) ProbComp) :=
  fun q saved => (fun result => (result.1, saved.1, result.2)) <$>
    (Signatures.Runtime.SchnorrAGM.handler saved.1.1 saved.1.2 q).run saved.2

include uniform in
theorem synchronizes_stored (value : Packet layout) {hashes signatures : Nat}
    (room : Reserved layout hashes signatures value.2) (allowed : Allowed layout hashes signatures value.1) :
    Synchronizes (fun represented source => replyMatches layout value.1 represented.1 source.1 ∧
      stored layout represented.2 = source.2)
      (source layout ops sampler value) ((original (query layout value.1)).run (stored layout value.2)) := by
  have coupled := synchronizes layout ops sampler uniform value (ready_of_reserved layout value room allowed)
    (decodeState value.2.val.2) (Reserved.canonical layout room).symm
  have canonical := coupled.mono_left_support (stronger := fun represented source =>
      replyMatches layout value.1 represented.1 source.1 ∧
        represented.2.val = (value.2.val.1, encodeState source.2))
    (fun represented _ reached related =>
      ⟨⟨related.1, source_canonical layout ops sampler value represented reached⟩, related.2⟩)
  have mapped := canonical.map
    (result := fun represented source => replyMatches layout value.1 represented.1 source.1 ∧ stored layout represented.2 = source.2)
    id (fun result => (result.1, value.2.val.1, result.2)) (by
      intro represented source related
      refine ⟨related.1, ?_⟩
      change (represented.2.val.1, decodeState represented.2.val.2) = _
      rw [related.2]
      simp only [decode_encodeState])
  simpa only [id_map, original, StateT.run, stored] using mapped

end Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerHandler
