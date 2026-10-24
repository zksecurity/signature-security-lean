import Proofs.Runtime.Caliper.Assembly

/-! Executable construction of bounded products and tagged unions. Literal tags,
padding and duplicated payloads all contribute instructions and stored code.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper Assembly

variable {w : Nat} {A B : Type}

def duplicateRealizer (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (input : Representation w A) (hw : 16 < 2 ^ w)
    (fits : input.encoding.words + input.encoding.words < 2 ^ w) :
    Realizer cost input (input.prod input fits) (fun value => (value, value)) :=
  Assembly.realizer cost allocation input (input.prod input fits) _
    (reads 0 0 input.encoding.words ++ reads 0 0 input.encoding.words) hw
    (by simp [reads_length, Representation.prod, Encoding.prod, Encoding.checked])
    (by
      intro operand member
      exact reads_namesFit 0 0 input.encoding.words (by positivity) operand (by simpa using member))
    (by
      intro value state represented operand member
      have valid := reads_valid 1 0 0 input.encoding.words state (by decide)
        (by simp [represented_size input represented])
        (by rw [represented_size input represented]; exact input.fits)
      exact valid operand (by simpa using member))
    (by
      intro value state represented
      have hv := reads_values 0 0 input.encoding.words state (by simp [represented_size input represented])
      have ht : (state.bufs 0).toList.take input.encoding.words = input.encoding.encode value := by
        rw [represented.2.1, ← input.encoding.encode_length value]; simp
      simpa [values, Representation.prod, Encoding.prod, Encoding.checked, ht] using congrArg (fun xs => xs ++ xs) hv)

namespace Construction

def taggedOperands (tag : Word w) (payload padding : Nat) : List (Operand w) :=
  .literal tag :: (reads 0 0 payload ++ List.replicate padding (.literal 0))

theorem prefix_length (tag : Word w) (payload padding : Nat) :
    (taggedOperands tag payload padding).length = 1 + payload + padding := by
  simp [taggedOperands, reads_length]; omega

theorem prefix_namesFit (tag : Word w) (payload padding : Nat) :
    ∀ operand ∈ taggedOperands tag payload padding, operand.NamesFit := by
  intro operand member
  simp only [taggedOperands, List.mem_cons, List.mem_append, List.mem_replicate] at member
  rcases member with rfl | member | ⟨_, rfl⟩
  · trivial
  · exact reads_namesFit 0 0 payload (by positivity) operand member
  · trivial

theorem prefix_valid (input : Representation w A) (tag : Word w) (padding : Nat)
    {value : A} {state : State w} (represented : input.Holds value state) :
    Valid 1 state (taggedOperands tag input.encoding.words padding) := by
  intro operand member
  simp only [taggedOperands, List.mem_cons, List.mem_append, List.mem_replicate] at member
  rcases member with rfl | member | ⟨_, rfl⟩
  · trivial
  · exact reads_valid 1 0 0 input.encoding.words state (by decide)
      (by simp [represented_size input represented])
      (by rw [represented_size input represented]; exact input.fits) operand member
  · trivial

theorem prefix_values (input : Representation w A) (tag : Word w) (padding : Nat)
    {value : A} {state : State w} (represented : input.Holds value state) :
    values (taggedOperands tag input.encoding.words padding) state =
      tag :: (input.encoding.encode value ++ List.replicate padding 0) := by
  have hv := reads_values 0 0 input.encoding.words state (by simp [represented_size input represented])
  have ht : (state.bufs 0).toList.take input.encoding.words = input.encoding.encode value := by
    rw [represented.2.1, ← input.encoding.encode_length value]; simp
  simp only [taggedOperands, values, List.map_cons, List.map_append, List.map_replicate, Operand.value]
  rw [show (reads 0 0 input.encoding.words).map (Operand.value state) =
    (state.bufs 0).toList.take input.encoding.words by simpa [values] using hv, ht]

end Construction

def inlRealizer (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (left : Representation w A) (right : Representation w B) (hw : 16 < 2 ^ w)
    (fits : 1 + max left.encoding.words right.encoding.words < 2 ^ w) :
    Realizer cost left (left.sum right (width_pos hw) fits) Sum.inl :=
  Assembly.realizer cost allocation left (left.sum right (width_pos hw) fits) _
    (Construction.taggedOperands 0 left.encoding.words (max left.encoding.words right.encoding.words - left.encoding.words)) hw
    (by
      rw [Construction.prefix_length]
      change 1 + left.encoding.words + (max left.encoding.words right.encoding.words - left.encoding.words) =
        1 + max left.encoding.words right.encoding.words
      omega)
    (Construction.prefix_namesFit _ _ _)
    (fun _ _ represented => Construction.prefix_valid _ _ _ represented)
    (fun _ _ represented => Construction.prefix_values _ _ _ represented)

def inrRealizer (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (left : Representation w A) (right : Representation w B) (hw : 16 < 2 ^ w)
    (fits : 1 + max left.encoding.words right.encoding.words < 2 ^ w) :
    Realizer cost right (left.sum right (width_pos hw) fits) Sum.inr :=
  Assembly.realizer cost allocation right (left.sum right (width_pos hw) fits) _
    (Construction.taggedOperands 1 right.encoding.words (max left.encoding.words right.encoding.words - right.encoding.words)) hw
    (by
      rw [Construction.prefix_length]
      change 1 + right.encoding.words + (max left.encoding.words right.encoding.words - right.encoding.words) =
        1 + max left.encoding.words right.encoding.words
      omega)
    (Construction.prefix_namesFit _ _ _)
    (fun _ _ represented => Construction.prefix_valid _ _ _ represented)
    (fun _ _ represented => Construction.prefix_values _ _ _ represented)

end Signatures.Runtime.CaliperBackend
