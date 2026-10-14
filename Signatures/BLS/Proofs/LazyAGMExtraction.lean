import Signatures.BLS.Proofs.LazyAGMReduction
import Signatures.BLS.Proofs.Nondegeneracy

/-! Sparse BLS extraction agrees with the old full-domain formulas. The
finite domain occurs only in these proof-side comparison sums; evaluation of
`traceValue` follows actual reply occurrences, including duplicates. -/

open OracleComp OracleSpec Model.LazyAGM

namespace BLS.LazyAGM.Reduction

variable {F M R G₁ : Type}

theorem traceValue_eq_mapIdx [Zero F] [AddCommMonoid R] [SMul F R]
    (coeff : List F) (tr : List (M × G₁)) (table : M → R) :
    traceValue coeff tr table =
      (tr.mapIdx fun n p => tokenCoeff coeff n • table p.1).sum := by
  simp [traceValue, traceTerms, List.mapIdx_eq_ofFn, List.map_ofFn, Function.comp_def]

theorem traceValue_fst [Field F] (coeff : List F) (tr : List (M × G₁))
    (table : M → F × F) :
    (traceValue coeff tr table).1 = traceValue coeff tr (fun m => (table m).1) := by
  simp [traceValue_eq_mapIdx, List.mapIdx_eq_ofFn, List.sum_ofFn, Prod.fst_sum]

theorem traceValue_snd [Field F] (coeff : List F) (tr : List (M × G₁))
    (table : M → F × F) :
    (traceValue coeff tr table).2 = traceValue coeff tr (fun m => (table m).2) := by
  simp [traceValue_eq_mapIdx, List.mapIdx_eq_ofFn, List.sum_ofFn, Prod.snd_sum]

variable [Field F] [Fintype M] [DecidableEq M]

theorem baseCoeff_traceValue (coeff : List F) (tr : List (M × G₁)) (table : M → F) :
    (∑ i, baseCoeff coeff tr i * table i) = traceValue coeff tr table := by
  rw [traceValue_eq_mapIdx]
  simp only [baseCoeff, List.mapIdx_eq_ofFn, List.sum_ofFn, Finset.sum_mul, smul_eq_mul]
  rw [Finset.sum_comm]
  simp

theorem denominatorCoeff_traceValue (out : Output F M) (tr : Transcript M M G₁)
    (table : M → F) :
    (∑ i, denominatorCoeff BLS.Proofs.indicatorWeight out tr i * table i) =
      table out.mstar - traceValue out.ξ tr.2 table := by
  simp only [denominatorCoeff, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · simp [BLS.Proofs.indicatorWeight]
  · rw [traceValue_eq_mapIdx]
    simp only [List.mapIdx_eq_ofFn, List.sum_ofFn, Finset.sum_mul, smul_eq_mul]
    rw [Finset.sum_comm]
    simp [BLS.Proofs.indicatorWeight]

end BLS.LazyAGM.Reduction
