/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/
import Signatures.LinearFunctional.Spec.Handle
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# OOPS linear-functional weights

OOPS instantiates the shared linear-functional reduction with monomial weights `wⱼ(m) = mʲ`.
The Vandermonde argument supplies a coordinate where the forgery functional is nonzero.
-/

open AlgebraicGroupModel.LinFunctional Finset

namespace OOPS.Handle

variable {F T : Type} [Field F] [DecidableEq F] [DecidableEq T] {d : ℕ}

/-- Full multi-topic OOPS weight family.  A base coordinate contributes only to messages carrying
the same topic. -/
def oopsWMulti (d : ℕ) : (T × Fin (d + 1)) → (F × T) → F := fun b mt =>
  if b.1 = mt.2 then mt.1 ^ (b.2 : ℕ) else 0

/-- Distinct scalar messages queried on topic `t`, extracted after an adaptive transcript. -/
def targetMessages {Q : ℕ} (v : Fin Q → F × T) (t : T) : Finset F :=
  (Finset.univ.filter fun q => (v q).2 = t).image fun q => (v q).1

omit [Field F] in
/-- The indexed and list transcripts select the same distinct messages on a topic. -/
theorem targetMessages_eq_ofFn {Q : ℕ} (v : Fin Q → F × T) (t : T) :
    targetMessages v t = (((List.ofFn v).filter fun q => q.2 = t).map Prod.fst).toFinset := by
  ext m
  simp [targetMessages, Prod.ext_iff, and_comm]

/-- Multi-topic Vandermonde non-degeneracy.  The transcript may contain arbitrary signing queries
on other topics and repeated queries on the target topic.  The sole degree condition counts the
distinct scalar messages queried on the eventual forgery topic. -/
theorem forgery_coeff_ne_zero_multi {Q : ℕ} (v : Fin Q → F × T) (mstar : F × T)
    (xi : Fin Q → F) (hcard : (targetMessages v mstar.2).card ≤ d)
    (hfresh : ∀ q, mstar ≠ v q) :
    ∃ j : Fin (d + 1),
      Lcoeff (oopsWMulti (F := F) d) mstar v xi (mstar.2, j) ≠ 0 := by
  classical
  let signed := targetMessages v mstar.2
  let R : Polynomial F := ∏ m ∈ signed, (Polynomial.X - Polynomial.C m)
  have hRdeg : R.natDegree ≤ d := by
    calc
      R.natDegree ≤ ∑ m ∈ signed, (Polynomial.X - Polynomial.C m).natDegree := by
        dsimp [R]
        exact Polynomial.natDegree_prod_le _ _
      _ = signed.card := by simp
      _ ≤ d := hcard
  have hRstar : R.eval mstar.1 ≠ 0 := by
    dsimp [R]
    rw [Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun m hm => ?_
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_ne_zero.mpr fun heq => by
      have hmstar : mstar.1 ∈ targetMessages v mstar.2 := heq ▸ hm
      rw [targetMessages] at hmstar
      obtain ⟨q, hq, hqval⟩ := Finset.mem_image.mp hmstar
      have htopic : (v q).2 = mstar.2 := (Finset.mem_filter.mp hq).2
      apply hfresh q
      exact Prod.ext hqval.symm htopic.symm
  have hquery :
      ∑ q, xi q * (if mstar.2 = (v q).2 then R.eval (v q).1 else 0) = 0 := by
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases ht : mstar.2 = (v q).2
    · have hm : (v q).1 ∈ signed := by
        dsimp [signed, targetMessages]
        exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht.symm⟩, rfl⟩
      have hRq : R.eval (v q).1 = 0 := by
        dsimp [R]
        rw [Polynomial.eval_prod]
        exact Finset.prod_eq_zero hm (by simp)
      simp [ht, hRq]
    · simp [ht]
  by_contra hnonzero
  push Not at hnonzero
  have hev : ∀ x : F, R.eval x = ∑ j : Fin (d + 1), R.coeff j * x ^ (j : ℕ) := by
    intro x
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hRdeg),
      Finset.sum_range fun j => R.coeff j * x ^ j]
  have hswap :
      ∑ q, xi q *
          (if mstar.2 = (v q).2
            then ∑ j : Fin (d + 1), R.coeff j * (v q).1 ^ (j : ℕ) else 0)
        = ∑ j : Fin (d + 1), R.coeff j *
            (∑ q, xi q *
              (if mstar.2 = (v q).2 then (v q).1 ^ (j : ℕ) else 0)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => by
      by_cases ht : mstar.2 = (v q).2
      · simp only [if_pos ht, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      · simp [ht]
  have heval : R.eval mstar.1 =
      ∑ q, xi q * (if mstar.2 = (v q).2 then R.eval (v q).1 else 0) := by
    simp only [hev]
    rw [hswap]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj := hnonzero j
    simp only [Lcoeff, oopsWMulti, if_pos, sub_eq_zero] at hj
    rw [hj]
  exact hRstar (heval.trans hquery)

end OOPS.Handle
