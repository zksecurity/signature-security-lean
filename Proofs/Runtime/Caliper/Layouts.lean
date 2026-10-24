import Proofs.Runtime.Caliper.Realizer

/-! Bounded data layouts for the machine boundary. Each combinator gives a
decoder/encoder round trip and an exact stored-word count. Forming a represented
product, sum or list additionally requires its *combined* size to fit the chosen
address width; no unconditional closure instance hides that obligation.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper

variable {w : Nat} {A B : Type}

/-- Enforce the declared length before interpreting any value. -/
def Encoding.checked (words : Nat) (encode : A → List (Word w))
    (decode : List (Word w) → Option A)
    (length : ∀ value, (encode value).length = words)
    (roundtrip : ∀ value, decode (encode value) = some value) : Encoding w A where
  words := words
  encode := encode
  decode bytes := if bytes.length = words then decode bytes else none
  encode_length := length
  decode_encode value := by simp [length, roundtrip]
  decode_length bytes value h := by
    split at h
    · assumption
    · cases h

def Encoding.unit (w : Nat) : Encoding w Unit :=
  .checked 0 (fun _ => []) (fun _ => some ()) (fun _ => rfl) (fun _ => rfl)

/-- A bounded counter is one ordinary word, with out-of-range bit patterns
rejected by decoding. In particular, it is not an encoding of unbounded `Nat`. -/
def Encoding.fin (w bound : Nat) (fits : bound ≤ 2 ^ w) : Encoding w (Fin bound) :=
  .checked 1 (fun value => [BitVec.ofNat w value.val])
    (fun bytes => match bytes with
      | [word] => if h : word.toNat < bound then some ⟨word.toNat, h⟩ else none
      | _ => none)
    (fun _ => rfl) (by
      intro value
      have hv : value.val < 2 ^ w := value.isLt.trans_le fits
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, value.isLt])

def Encoding.prod (left : Encoding w A) (right : Encoding w B) : Encoding w (A × B) :=
  .checked (left.words + right.words)
    (fun value => left.encode value.1 ++ right.encode value.2)
    (fun bytes => do
      let x ← left.decode (bytes.take left.words)
      let y ← right.decode (bytes.drop left.words)
      pure (x, y))
    (by intro value; simp [left.encode_length, right.encode_length])
    (by
      intro value
      have hl := left.encode_length value.1
      rw [← hl]
      simp [left.decode_encode, right.decode_encode])

private def padded (encoding : Encoding w A) (width : Nat) (value : A) : List (Word w) :=
  encoding.encode value ++ List.replicate (width - encoding.words) 0

private theorem padded_length (encoding : Encoding w A) (width : Nat)
    (fits : encoding.words ≤ width) (value : A) : (padded encoding width value).length = width := by
  simp [padded, encoding.encode_length, Nat.add_sub_of_le fits]

private theorem padded_take (encoding : Encoding w A) (width : Nat) (value : A) :
    (padded encoding width value).take encoding.words = encoding.encode value := by
  rw [padded, ← encoding.encode_length value]
  simp

/-- Tagged unions reserve the larger payload size. Padding is charged, and the
tag is an inspectable word. Tags other than 0 and 1 are rejected. -/
def Encoding.sum (left : Encoding w A) (right : Encoding w B) (hw : 0 < w) : Encoding w (A ⊕ B) :=
  .checked (1 + max left.words right.words)
    (fun value => match value with
      | .inl x => 0 :: padded left (max left.words right.words) x
      | .inr y => 1 :: padded right (max left.words right.words) y)
    (fun bytes => match bytes with
      | [] => none
      | tag :: payload =>
          if tag = 0 then Sum.inl <$> left.decode (payload.take left.words)
          else if tag = 1 then Sum.inr <$> right.decode (payload.take right.words)
          else none)
    (by
      intro value
      cases value with
      | inl x => simp [padded_length left _ (le_max_left _ _) x, Nat.add_comm]
      | inr y => simp [padded_length right _ (le_max_right _ _) y, Nat.add_comm])
    (by
      intro value
      cases value <;> simp [hw.ne', padded_take, left.decode_encode, right.decode_encode])

/-- Bounded, variable-length mathematical lists. The capacity is part of the
representation, not a promise that an arbitrary list fits. -/
abbrev BoundedList (A : Type) (capacity : Nat) := {values : List A // values.length ≤ capacity}

def Encoding.pack (encoding : Encoding w A) : List A → List (Word w)
  | [] => []
  | value :: rest => encoding.encode value ++ encoding.pack rest

theorem Encoding.pack_length (encoding : Encoding w A) (values : List A) :
    (encoding.pack values).length = values.length * encoding.words := by
  induction values with
  | nil => simp [pack]
  | cons value rest ih => simp [pack, ih, encoding.encode_length, Nat.add_mul, Nat.add_comm]

def Encoding.unpack (encoding : Encoding w A) : Nat → List (Word w) → Option (List A)
  | 0, _ => some []
  | count + 1, bytes => do
      let value ← encoding.decode (bytes.take encoding.words)
      let rest ← encoding.unpack count (bytes.drop encoding.words)
      pure (value :: rest)

theorem Encoding.unpack_pack (encoding : Encoding w A) (values : List A) (suffix : List (Word w)) :
    encoding.unpack values.length (encoding.pack values ++ suffix) = some values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.length_cons, pack, unpack, List.append_assoc]
    rw [← encoding.encode_length value]
    simp [encoding.decode_encode, ih]

theorem Encoding.unpack_length (encoding : Encoding w A) (count : Nat)
    (bytes : List (Word w)) (values : List A)
    (decoded : encoding.unpack count bytes = some values) : values.length = count := by
  induction count generalizing bytes values with
  | zero => simp [unpack] at decoded; subst values; rfl
  | succ count ih =>
    cases hd : encoding.decode (bytes.take encoding.words) with
    | none => simp [unpack, hd] at decoded
    | some value =>
      cases hr : encoding.unpack count (bytes.drop encoding.words) with
      | none => simp [unpack, hd, hr] at decoded
      | some rest =>
        simp [unpack, hd, hr] at decoded
        subst values
        simp [ih _ _ hr]

def Encoding.boundedList (encoding : Encoding w A) (capacity : Nat)
    (fits : capacity < 2 ^ w) : Encoding w (BoundedList A capacity) :=
  .checked (1 + capacity * encoding.words)
    (fun values => BitVec.ofNat w values.val.length ::
      (encoding.pack values.val ++
        List.replicate ((capacity - values.val.length) * encoding.words) 0))
    (fun bytes => match bytes with
      | [] => none
      | length :: payload => do
          let values ← encoding.unpack length.toNat payload
          if h : values.length ≤ capacity then some ⟨values, h⟩ else none)
    (by
      intro values
      simp only [List.length_cons, List.length_append, List.length_replicate, encoding.pack_length]
      have := values.property
      rw [← Nat.add_mul, Nat.add_sub_of_le this, Nat.add_comm])
    (by
      intro values
      have hv : values.val.length < 2 ^ w := values.property.trans_lt fits
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, encoding.unpack_pack, values.property])

def Representation.prod (left : Representation w A) (right : Representation w B)
    (fits : left.encoding.words + right.encoding.words < 2 ^ w) : Representation w (A × B) :=
  ⟨left.encoding.prod right.encoding, fits⟩

def Representation.fin (w bound : Nat) (hw : 0 < w) (fits : bound ≤ 2 ^ w) :
    Representation w (Fin bound) :=
  ⟨Encoding.fin w bound fits, Nat.one_lt_two_pow hw.ne'⟩

def Representation.sum (left : Representation w A) (right : Representation w B)
    (hw : 0 < w) (fits : 1 + max left.encoding.words right.encoding.words < 2 ^ w) :
    Representation w (A ⊕ B) :=
  ⟨left.encoding.sum right.encoding hw, fits⟩

def Representation.boundedList (entry : Representation w A) (capacity : Nat)
    (count_fits : capacity < 2 ^ w)
    (storage_fits : 1 + capacity * entry.encoding.words < 2 ^ w) :
    Representation w (BoundedList A capacity) :=
  ⟨entry.encoding.boundedList capacity count_fits, storage_fits⟩

end Signatures.Runtime.CaliperBackend
