import Signatures.Runtime.SchnorrAGMCache
import Signatures.Runtime.Arithmetic

/-! Concrete tuple/list layouts for the Schnorr AGM store. The encoders express
the proof relation to the source state; native programs operate on these tuples
directly. Optional explanations use a Boolean tag and two scalar slots. -/

open Schnorr.AGM

namespace Signatures.Runtime.SchnorrAGM.Native

abbrev affineTy : Ty CryptoAtom := .pair scalar scalar
abbrev entryTy : Ty CryptoAtom := .pair scalar (.pair .bool affineTy)
abbrev cacheKeyTy : Ty CryptoAtom := .pair message point₁
abbrev cacheTy : Ty CryptoAtom := .list (.pair cacheKeyTy entryTy)
abbrev metaTy : Ty CryptoAtom := .pair (.list affineTy) (.pair (.list message) (.pair .bool .bool))
abbrev stateTy : Ty CryptoAtom := .pair cacheTy metaTy

abbrev EncodedEntry (F : Type) := F × Bool × F × F
abbrev Metadata (F M : Type) := List (F × F) × List M × Bool × Bool
abbrev EncodedState (F G M : Type) := List ((M × G) × EncodedEntry F) × Metadata F M

def encodeAffine {F : Type} (a : Affine F) : F × F := (a.constant, a.secret)
def decodeAffine {F : Type} (a : F × F) : Affine F := ⟨a.1, a.2⟩

@[simp] theorem decode_encodeAffine {F : Type} (a : Affine F) :
    decodeAffine (encodeAffine a) = a := by cases a; rfl

@[simp] theorem encode_decodeAffine {F : Type} (a : F × F) :
    encodeAffine (decodeAffine a) = a := rfl

def encodeEntry {F : Type} [Zero F] (e : Reduction.Entry F) : EncodedEntry F :=
  (e.challenge, match e.representation with
    | none => (false, 0, 0)
    | some a => (true, encodeAffine a))

def decodeEntry {F : Type} (e : EncodedEntry F) : Reduction.Entry F :=
  ⟨e.1, if e.2.1 then some (decodeAffine e.2.2) else none⟩

@[simp] theorem decode_encodeEntry {F : Type} [Zero F] (e : Reduction.Entry F) :
    decodeEntry (encodeEntry e) = e := by
  rcases e with ⟨c, a⟩
  cases a <;> simp [encodeEntry, decodeEntry]

def encodeMetadata {F G M : Type} [Field F] (s : State F G M) : Metadata F M :=
  (s.representations.map encodeAffine, s.signed, s.malformed, s.bad)

def encodeState {F G M : Type} [Field F] (s : State F G M) : EncodedState F G M :=
  (s.cache.map (Prod.map id encodeEntry), encodeMetadata s)

def decodeState {F G M : Type} [Field F] (s : EncodedState F G M) : State F G M :=
  { cache := s.1.map (Prod.map id decodeEntry)
    representations := s.2.1.map decodeAffine
    signed := s.2.2.1
    malformed := s.2.2.2.1
    bad := s.2.2.2.2 }

@[simp] theorem decode_encodeState {F G M : Type} [Field F] (s : State F G M) :
    decodeState (encodeState s) = s := by
  cases s
  simp [decodeState, encodeState, encodeMetadata, List.map_map, Function.comp_def, Prod.map]

theorem encodeState_injective {F G M : Type} [Field F] :
    Function.Injective (encodeState (F := F) (G := G) (M := M)) :=
  Function.LeftInverse.injective decode_encodeState

/-- Lookup commutes with the representation relation, including shadowed entries. -/
theorem cacheMap_encode {F G M : Type} [Zero F] [DecidableEq G] [DecidableEq M]
    (xs : List ((M × G) × Reduction.Entry F)) (k : M × G) :
    cacheMap (xs.map (Prod.map id encodeEntry)) k = (cacheMap xs k).map encodeEntry := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
      by_cases h : p.1 = k <;> simp [cacheMap, h, ih]

end Signatures.Runtime.SchnorrAGM.Native
