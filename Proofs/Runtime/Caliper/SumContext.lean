import Proofs.Runtime.Caliper.TagBounds
import Proofs.Runtime.Caliper.Pairing

/-! Executed distribution of a tagged value and saved context. Union padding
lies before the context on input and after it on output, so distribution is a
copying program, not an uncharged reassociation of the mathematical types. -/

namespace Signatures.Runtime.CaliperBackend.SumContext
open Caliper Assembly

variable {w : Nat} {A B S : Type}

def padded (value : Representation w A) (padding : Nat)
    (fits : value.encoding.words + padding < 2 ^ w) : Representation w A where
  encoding := Encoding.checked (value.encoding.words + padding)
    (fun x => value.encoding.encode x ++ List.replicate padding 0)
    (fun bytes => value.encoding.decode (bytes.take value.encoding.words))
    (fun x => by simp [value.encoding.encode_length])
    (fun x => by rw [← value.encoding.encode_length x]; simp [value.encoding.decode_encode])
  fits := fits

def unpad (value : Representation w A) (saved : Representation w S) (padding : Nat)
    (hw : 16 < 2 ^ w) (fits : value.encoding.words + padding + saved.encoding.words < 2 ^ w) :
    Realizer .unit ((padded value padding (by omega)).prod saved fits)
      (value.prod saved (by omega)) id :=
  Assembly.realizer .unit (by decide) _ _ id
    (reads 0 0 value.encoding.words ++ reads 0 (value.encoding.words + padding) saved.encoding.words) hw
    (by simp only [List.length_append, reads_length]; rfl)
    (by intro operand member; rcases List.mem_append.mp member with member | member
        · exact reads_namesFit 0 _ _ (by positivity) operand member
        · exact reads_namesFit 0 _ _ (by positivity) operand member)
    (by
      intro x before represented operand member
      have size := represented_size _ represented
      change (before.bufs 0).size = value.encoding.words + padding + saved.encoding.words at size
      rcases List.mem_append.mp member with member | member <;>
        exact reads_valid 1 0 _ _ before (by decide) (by omega) (by omega) operand member)
    (by
      intro x before represented
      have contents : (before.bufs 0).toList =
          value.encoding.encode x.1 ++ List.replicate padding 0 ++ saved.encoding.encode x.2 := represented.2.1
      have first := ListFold.reads_block [] (value.encoding.encode x.1)
        (List.replicate padding 0 ++ saved.encoding.encode x.2) before (by simpa [List.append_assoc] using contents)
      have second := ListFold.reads_block (value.encoding.encode x.1 ++ List.replicate padding 0)
        (saved.encoding.encode x.2) [] before (by simpa using contents)
      simp only [List.length_nil, List.length_append, List.length_replicate, value.encoding.encode_length, saved.encoding.encode_length] at first second
      change values (reads 0 0 value.encoding.words ++ reads 0 (value.encoding.words + padding) saved.encoding.words) before =
        value.encoding.encode x.1 ++ saved.encoding.encode x.2
      simp only [values, List.map_append] at first second ⊢
      rw [first, second])

def view : (A ⊕ B) × S ≃ (A × S) ⊕ (B × S) where
  toFun x := match x.1 with | .inl a => .inl (a, x.2) | .inr b => .inr (b, x.2)
  invFun x := match x with | .inl (a, s) => (.inl a, s) | .inr (b, s) => (.inr b, s)
  left_inv x := by rcases x with ⟨a | b, s⟩ <;> rfl
  right_inv x := by rcases x with ⟨a, s⟩ | ⟨b, s⟩ <;> rfl

variable (left : Representation w A) (right : Representation w B) (saved : Representation w S)
    (hw : 16 < 2 ^ w) (fits : 1 + max left.encoding.words right.encoding.words + saved.encoding.words < 2 ^ w)

def input : Representation w ((A ⊕ B) × S) :=
  (left.sum right (width_pos hw) (by omega)).prod saved fits

def output : Representation w ((A × S) ⊕ (B × S)) :=
  (left.prod saved (by omega)).sum (right.prod saved (by omega)) (width_pos hw) (by
    change 1 + max (left.encoding.words + saved.encoding.words) (right.encoding.words + saved.encoding.words) < 2 ^ w
    omega)

def leftFrame : Representation w (A × S) :=
  (padded left (max left.encoding.words right.encoding.words - left.encoding.words) (by omega)).prod saved (by
    change left.encoding.words + (max left.encoding.words right.encoding.words - left.encoding.words) + saved.encoding.words < 2 ^ w
    omega)
def rightFrame : Representation w (B × S) :=
  (padded right (max left.encoding.words right.encoding.words - right.encoding.words) (by omega)).prod saved (by
    change right.encoding.words + (max left.encoding.words right.encoding.words - right.encoding.words) + saved.encoding.words < 2 ^ w
    omega)

theorem frame_words : (leftFrame left right saved fits).encoding.words = max left.encoding.words right.encoding.words + saved.encoding.words ∧
    (rightFrame left right saved fits).encoding.words = max left.encoding.words right.encoding.words + saved.encoding.words := by
  change left.encoding.words + (max left.encoding.words right.encoding.words - left.encoding.words) + saved.encoding.words = _ ∧
    right.encoding.words + (max left.encoding.words right.encoding.words - right.encoding.words) + saved.encoding.words = _
  omega

theorem frameFits : 1 + max (leftFrame left right saved fits).encoding.words (rightFrame left right saved fits).encoding.words < 2 ^ w := by
  rw [(frame_words left right saved fits).1, (frame_words left right saved fits).2, max_self]
  omega

theorem sameBytes (x : (A ⊕ B) × S) :
    ((leftFrame left right saved fits).sum (rightFrame left right saved fits) (width_pos hw) (frameFits left right saved fits)).encoding.encode (view x) =
      (input left right saved hw fits).encoding.encode x := by
  rcases x with ⟨a | b, s⟩
  · change 0 :: (((leftFrame left right saved fits).encoding.encode (a, s)) ++
      List.replicate (max (leftFrame left right saved fits).encoding.words (rightFrame left right saved fits).encoding.words -
        (leftFrame left right saved fits).encoding.words) 0) = _
    rw [(frame_words left right saved fits).1, (frame_words left right saved fits).2, max_self, Nat.sub_self]
    simp only [List.replicate_zero, List.append_nil]
    rfl
  · change 1 :: (((rightFrame left right saved fits).encoding.encode (b, s)) ++
      List.replicate (max (leftFrame left right saved fits).encoding.words (rightFrame left right saved fits).encoding.words -
        (rightFrame left right saved fits).encoding.words) 0) = _
    rw [(frame_words left right saved fits).1, (frame_words left right saved fits).2, max_self, Nat.sub_self]
    simp only [List.replicate_zero, List.append_nil]
    rfl

def distribute : Realizer .unit (input left right saved hw fits) (output left right saved hw fits) view := by
  have body := (branchRealizer .unit (by decide) (leftFrame left right saved fits) (rightFrame left right saved fits) _
    ((unpad left saved (max left.encoding.words right.encoding.words - left.encoding.words) hw (by omega)).then
      (inlRealizer .unit (by decide) (left.prod saved (by omega)) (right.prod saved (by omega)) hw (output left right saved hw fits).fits))
    ((unpad right saved (max left.encoding.words right.encoding.words - right.encoding.words) hw (by omega)).then
      (inrRealizer .unit (by decide) (left.prod saved (by omega)) (right.prod saved (by omega)) hw (output left right saved hw fits).fits))
    hw (frameFits left right saved fits)).viewInput (input left right saved hw fits) view
      (fun x => (sameBytes left right saved hw fits x).symm)
  exact body.viewOutput (output left right saved hw fits) view (by
    intro x
    rcases x with ⟨a | b, s⟩ <;> rfl
  )

end Signatures.Runtime.CaliperBackend.SumContext
