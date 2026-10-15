import Signatures.Runtime.SeedTapeScan
import Signatures.Runtime.SeedTapeReset

/-! Scanning and resetting retain only existing cells, apart from the explicitly
appended replacement. These facts transport any cell representation invariant. -/

namespace Signatures.Runtime.Schnorr.SeedTape

variable {F : Type}

theorem pop_sublist (tag : Nat) (fallback : TapeCell F) (cells : List (TapeCell F)) :
    (pop tag fallback cells).2.2.Sublist cells := by
  induction cells with
  | nil => exact List.Sublist.refl _
  | cons cell cells ih =>
      by_cases same : cell.1 = tag
      · simp [pop, same]
      · simpa [pop, same] using ih.cons_cons cell

theorem pop_answer_mem_or_default (tag : Nat) (fallback : TapeCell F)
    (cells : List (TapeCell F)) :
    (pop tag fallback cells).2.1 ∈ cells ∨ (pop tag fallback cells).2.1 = fallback := by
  induction cells with
  | nil => exact Or.inr rfl
  | cons cell cells ih =>
      by_cases same : cell.1 = tag
      · simp [pop, same]
      · simpa only [pop, same, ite_false, List.mem_cons] using ih.imp (Or.inr) id

theorem pop_answer_mem (tag : Nat) (fallback : TapeCell F) (cells : List (TapeCell F))
    (found : (pop tag fallback cells).1 = true) :
    (pop tag fallback cells).2.1 ∈ cells := by
  induction cells with
  | nil => simp [pop] at found
  | cons cell cells ih =>
      by_cases same : cell.1 = tag
      · simp [pop, same]
      · simp only [pop, same, ite_false] at found ⊢
        exact List.mem_cons_of_mem _ (ih found)

theorem trim_sublist (tag slot : Nat) (cells : List (TapeCell F)) :
    (trim tag slot cells).2.Sublist cells := by
  induction cells generalizing slot with
  | nil => exact List.Sublist.refl _
  | cons cell cells ih =>
      by_cases same : cell.1 = tag <;> cases slot <;>
        simp only [trim, same, ite_true, ite_false, Nat.succ_ne_zero, Nat.reduceSub] <;>
        first | exact (ih _).cons cell | exact (ih _).cons_cons cell

end Signatures.Runtime.Schnorr.SeedTape
