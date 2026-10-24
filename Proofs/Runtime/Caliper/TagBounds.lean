import Proofs.Runtime.Caliper.Construct
import Proofs.Runtime.Caliper.BufferBounds

/-! Resources for stored union tags, payload copying and padding. -/

namespace Signatures.Runtime.CaliperBackend
open Caliper Assembly

variable {w : Nat} {A B : Type} (left : Representation w A) (right : Representation w B)
    (hw : 16 < 2 ^ w) (fits : 1 + max left.encoding.words right.encoding.words < 2 ^ w)

theorem inl_time (value : A) : (inlRealizer .unit (by decide) left right hw fits).time value ≤
    8 * (1 + max left.encoding.words right.encoding.words) := by
  have bound := code_time_unit_le (Construction.taggedOperands (w := w) 0 left.encoding.words
    (max left.encoding.words right.encoding.words - left.encoding.words))
  rw [Construction.prefix_length] at bound
  change (code _).staticTime .unit ≤ _
  convert bound using 1; omega

theorem inr_time (value : B) : (inrRealizer .unit (by decide) left right hw fits).time value ≤
    8 * (1 + max left.encoding.words right.encoding.words) := by
  have bound := code_time_unit_le (Construction.taggedOperands (w := w) 1 right.encoding.words
    (max left.encoding.words right.encoding.words - right.encoding.words))
  rw [Construction.prefix_length] at bound
  change (code _).staticTime .unit ≤ _
  convert bound using 1; omega

theorem inl_words : descriptionWords (inlRealizer .unit (by decide) left right hw fits).code ≤
    26 * (1 + max left.encoding.words right.encoding.words) + 14 := by
  have bound := code_descriptionWords_le (Construction.taggedOperands (w := w) 0 left.encoding.words
    (max left.encoding.words right.encoding.words - left.encoding.words))
  rw [Construction.prefix_length] at bound
  change descriptionWords (code _) ≤ _
  convert bound using 1; omega

theorem inr_words : descriptionWords (inrRealizer .unit (by decide) left right hw fits).code ≤
    26 * (1 + max left.encoding.words right.encoding.words) + 14 := by
  have bound := code_descriptionWords_le (Construction.taggedOperands (w := w) 1 right.encoding.words
    (max left.encoding.words right.encoding.words - right.encoding.words))
  rw [Construction.prefix_length] at bound
  change descriptionWords (code _) ≤ _
  convert bound using 1; omega

theorem Construction.prefix_sources (tag : Word w) (payload padding : Nat) :
    SourcesBound (Construction.taggedOperands tag payload padding) 1 := by
  intro operand member
  simp only [Construction.taggedOperands, List.mem_cons, List.mem_append, List.mem_replicate] at member
  rcases member with rfl | member | ⟨_, rfl⟩
  · trivial
  · exact sourcesBound_reads 0 0 payload 1 (by decide) operand member
  · trivial

theorem inl_names : NamesBound (inlRealizer .unit (by decide) left right hw fits).code 3 := by
  have bound := code_names (Construction.taggedOperands (w := w) 0 left.encoding.words
    (max left.encoding.words right.encoding.words - left.encoding.words)) 1 (Construction.prefix_sources _ _ _)
  exact ⟨bound.1, bound.2.trans (by decide)⟩

theorem inr_names : NamesBound (inrRealizer .unit (by decide) left right hw fits).code 3 := by
  have bound := code_names (Construction.taggedOperands (w := w) 1 right.encoding.words
    (max left.encoding.words right.encoding.words - right.encoding.words)) 1 (Construction.prefix_sources _ _ _)
  exact ⟨bound.1, bound.2.trans (by decide)⟩

end Signatures.Runtime.CaliperBackend
