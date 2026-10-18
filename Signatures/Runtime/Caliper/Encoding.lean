import Signatures.Runtime.Caliper.Program

/-! Explicit word encodings and addresses for cryptographic routines.
Values live in ordinary Caliper buffers and remain available to word/bit
instructions. Decoding is a mathematical specification, never a free machine
instruction. Call operands must pass the bounds and decoding checks below.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper

/-- Canonical fixed-width encodings, independently chosen for each scalar/group
type. The width may depend on the security parameter at instantiation time. -/
structure Encoding (w : Nat) (Value : Type) where
  words : Nat
  encode : Value → List (Word w)
  decode : List (Word w) → Option Value
  encode_length : ∀ value, (encode value).length = words
  decode_encode : ∀ value, decode (encode value) = some value
  decode_length : ∀ bytes value, decode bytes = some value → bytes.length = words

/-- A statically named buffer with an offset held in an ordinary word register. -/
structure Address where
  buffer : BufId
  offset : Reg
  deriving DecidableEq, Repr

variable {w : Nat} {Value : Type}

def Address.start (address : Address) (state : State w) : Nat :=
  (state.regs address.offset).toNat

/-- All addressed words are initialized, within reserved capacity, and
addressable without wrapping the word index. -/
def Address.Valid (address : Address) (words : Nat) (state : State w) : Prop :=
  address.start state + words ≤ (state.bufs address.buffer).size ∧
    (state.bufs address.buffer).size ≤ state.caps address.buffer ∧
    state.caps address.buffer < 2 ^ w

def Address.contents (address : Address) (words : Nat) (state : State w) : List (Word w) :=
  ((state.bufs address.buffer).toList.drop (address.start state)).take words

/-- Describes a represented input/output; this predicate is not a primitive read. -/
def Encoding.At (encoding : Encoding w Value) (address : Address)
    (state : State w) (value : Value) : Prop :=
  address.Valid encoding.words state ∧
    encoding.decode (address.contents encoding.words state) = some value

theorem Encoding.encode_injective (encoding : Encoding w Value) :
    Function.Injective encoding.encode := by
  intro x y equal
  have := congrArg encoding.decode equal
  simpa only [encoding.decode_encode, Option.some.injEq] using this

/-- One register is an encoded Boolean result; no host-language predicate can
serve as an uncharged branch condition. -/
def BooleanAt (register : Reg) (state : State w) (value : Bool) : Prop :=
  state.regs register = if value then 1 else 0

end Signatures.Runtime.CaliperBackend
