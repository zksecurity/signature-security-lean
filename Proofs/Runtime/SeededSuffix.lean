import Proofs.Runtime.SeededTrace

/-! Algebra of recorded prefixes and unused per-family suffixes. This separates
the seed entries kept by lazy replay from the independent entries appearing
only in the fully pregenerated probability proof. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.SeededTrace

variable {I : Type} {spec : OracleSpec I}

def append (recorded suffix : QuerySeed spec) : QuerySeed spec :=
  fun i => recorded i ++ suffix i

theorem append_empty (recorded : QuerySeed spec) : append recorded ∅ = recorded := by
  funext i
  simp [append]

variable [DecidableEq I]

theorem append_prepend (recorded suffix : QuerySeed spec) (i : I)
    (answers : List (spec.Range i)) :
    append recorded (suffix.prependValues answers) = append (recorded.addValues answers) suffix := by
  funext j
  by_cases h : j = i
  · subst j
    simp [append, List.append_assoc]
  · simp [append, QuerySeed.prependValues_of_ne _ _ h, QuerySeed.addValues_of_ne _ _ h]

theorem restore_eq_append (log : QueryLog spec) (suffix : QuerySeed spec) :
    restore log suffix = append (restore log ∅) suffix := by
  induction log with
  | nil => funext i; simp [restore, append]
  | cons entry log ih =>
      rcases entry with ⟨i, answer⟩
      simp only [restore, ih]
      funext j
      by_cases h : j = i
      · subst j
        simp [append]
      · simp [append, QuerySeed.prependValues_of_ne _ _ h]

/-- If the selected slot lies in the recorded prefix, resetting the full seed
keeps the recorded reset and only the other families' unused suffixes. -/
theorem reset_append (recorded suffix : QuerySeed spec) (i : I) (slot : Nat)
    (answer : spec.Range i) (within : slot ≤ (recorded i).length) :
    ((append recorded suffix).takeAtIndex i slot).addValue i answer =
      append ((recorded.takeAtIndex i slot).addValue i answer) (suffix.update i []) := by
  funext j
  by_cases h : j = i
  · subst j
    simp only [QuerySeed.addValue, QuerySeed.addValues_self, QuerySeed.takeAtIndex_apply_self,
      append, QuerySeed.update_self, List.append_nil]
    rw [List.take_append_of_le_length within]
  · simp [append, QuerySeed.addValue, QuerySeed.addValues_of_ne _ _ h,
      QuerySeed.takeAtIndex_apply_of_ne _ _ _ _ h, QuerySeed.update_of_ne _ _ _ _ h]

theorem erase_prepend_self (seed : QuerySeed spec) (i : I) (answers : List (spec.Range i)) :
    (seed.prependValues answers).update i [] = seed.update i [] := by
  simp only [QuerySeed.prependValues, QuerySeed.update_idem]

theorem erase_prepend_other (seed : QuerySeed spec) (i j : I) (different : j ≠ i)
    (answers : List (spec.Range j)) :
    (seed.prependValues answers).update i [] = (seed.update i []).prependValues answers := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [QuerySeed.prependValues_of_ne _ _ (Ne.symm different)]
  · by_cases hkj : k = j
    · subst k
      simp [QuerySeed.update_of_ne _ _ _ _ different]
    · simp [QuerySeed.update_of_ne _ _ _ _ hki, QuerySeed.prependValues_of_ne _ _ hkj]

end Signatures.Runtime.SeededTrace
