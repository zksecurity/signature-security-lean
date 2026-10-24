import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import ToMathlib.Probability.ProbabilityMassFunction.Lemmas
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Size

/-! Bounded rejection sampling from uniform binary words. Exhausting the retry
budget returns `none`; no modulo bias is hidden in a purported uniform sampler.
Individual fair-bit draws implement uniform words. The executable tape runner
has the same output distribution, with an explicit bound on consumed bits.
BitRejection implements the costed bit-oracle controller; its distributional
refinement is in BitRejectionDistribution. Reduction integration remains separate. -/

namespace Signatures.Runtime.RejectionSampling

open scoped ENNReal

def accept (n : Nat) {w : Nat} (x : Fin (2 ^ w)) : Option (Fin n) :=
  if h : x.val < n then some ⟨x.val, h⟩ else none

noncomputable def draw (n w : Nat) : PMF (Option (Fin n)) :=
  (PMF.uniformOfFintype (Fin (2 ^ w))).map (accept n)

noncomputable def sample (n w : Nat) : Nat → PMF (Option (Fin n))
  | 0 => PMF.pure none
  | k + 1 => (draw n w).bind fun
      | none => sample n w k
      | some x => PMF.pure (some x)

theorem accept_some_iff (n w : Nat) (y : Fin n) (x : Fin (2 ^ w)) :
    some y = accept n x ↔ y.val = x.val := by
  unfold accept
  split
  · simp only [Option.some.injEq, Fin.ext_iff]
  · simp only [reduceCtorEq, false_iff]
    intro h
    have := y.isLt
    omega

theorem draw_some (n w : Nat) (hfit : n ≤ 2 ^ w) (y : Fin n) :
    draw n w (some y) = (2 ^ w : ℝ≥0∞)⁻¹ := by
  unfold draw
  rw [PMF.map_apply]
  let x : Fin (2 ^ w) := ⟨y.val, y.isLt.trans_le hfit⟩
  rw [tsum_eq_single x]
  · simp [accept_some_iff, x, PMF.uniformOfFintype_apply]
  · intro b hb
    rw [ite_eq_right]
    intro h
    apply hb
    exact Fin.ext ((accept_some_iff n w y b).mp h).symm

theorem draw_none (n w : Nat) (hfit : n ≤ 2 ^ w) :
    draw n w none = 1 - n * (2 ^ w : ℝ≥0∞)⁻¹ := by
  have h := (draw n w).tsum_coe
  rw [tsum_fintype, Fintype.sum_option] at h
  simp only [draw_some n w hfit, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  exact ENNReal.eq_sub_of_add_eq (by finiteness) h

theorem sample_none (n w k : Nat) :
    sample n w k none = (draw n w none) ^ k := by
  induction k with
  | zero => simp [sample, PMF.pure_apply]
  | succ k ih =>
    simp [sample, PMF.bind_apply, tsum_fintype, Fintype.sum_option, PMF.pure_apply,
      ih, pow_succ']

/-- The exact failure probability, including zero retries and power-of-two moduli. -/
theorem failure (n w k : Nat) (hfit : n ≤ 2 ^ w) :
    sample n w k none = (1 - n * (2 ^ w : ℝ≥0∞)⁻¹) ^ k := by
  rw [sample_none, draw_none n w hfit]

theorem sample_some_succ (n w k : Nat) (y : Fin n) :
    sample n w (k + 1) (some y) =
      draw n w none * sample n w k (some y) + draw n w (some y) := by
  simp only [sample, PMF.bind_apply, tsum_fintype, Fintype.sum_option, PMF.pure_apply,
    Option.some.injEq, mul_ite, mul_one, mul_zero]
  simp

/-- Every accepted value has exactly the same mass, for every retry budget. -/
theorem sample_uniform (n w k : Nat) (hfit : n ≤ 2 ^ w) (x y : Fin n) :
    sample n w k (some x) = sample n w k (some y) := by
  induction k with
  | zero => simp [sample, PMF.pure_apply]
  | succ k ih => rw [sample_some_succ, sample_some_succ, ih,
      draw_some n w hfit, draw_some n w hfit]

/-- Success is an ideal uniform value scaled by the non-abort probability. -/
theorem sample_some (n w k : Nat) (hfit : n ≤ 2 ^ w) (x : Fin n) :
    sample n w k (some x) = (1 - (1 - n * (2 ^ w : ℝ≥0∞)⁻¹) ^ k) / n := by
  have hn : 0 < n := Nat.zero_lt_of_lt x.isLt
  apply (ENNReal.eq_div_iff (by positivity) (by simp)).mpr
  have h := (sample n w k).tsum_coe
  rw [tsum_fintype, Fintype.sum_option] at h
  simp only [sample_uniform n w k hfit (y := x), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have he := ENNReal.eq_sub_of_add_eq (sample n w k |>.apply_ne_top none) ((add_comm _ _).trans h)
  simpa only [failure n w k hfit] using he

/-- Independent uniform draws form the uniform distribution on pairs. -/
theorem uniform_pair {X Y : Type} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] :
    (PMF.uniformOfFintype X).bind (fun x =>
      (PMF.uniformOfFintype Y).map (fun y => (x, y))) =
      PMF.uniformOfFintype (X × Y) := by
  classical
  ext ⟨x, y⟩
  simp [PMF.bind_apply, PMF.map_apply, PMF.uniformOfFintype_apply,
    Prod.ext_iff, ite_and, mul_ite, tsum_fintype, ENNReal.mul_inv]

def joinBit (w : Nat) : Fin 2 × Fin (2 ^ w) ≃ Fin (2 ^ (w + 1)) :=
  finProdFinEquiv.trans (finCongr (by omega : 2 * 2 ^ w = 2 ^ (w + 1)))

/-- Draw exactly w independent fair bits, using their binary numeric encoding. -/
noncomputable def fairWord : (w : Nat) → PMF (Fin (2 ^ w))
  | 0 => PMF.pure 0
  | w + 1 => ((PMF.uniformOfFintype (Fin 2)).bind fun b =>
      (fairWord w).map (fun x => (b, x))).map (joinBit w)

theorem fairWord_uniform (w : Nat) : fairWord w = PMF.uniformOfFintype (Fin (2 ^ w)) := by
  induction w with
  | zero =>
    ext x
    have hx : x = 0 := Subsingleton.elim (α := Fin 1) _ _
    simp [fairWord, hx, PMF.pure_apply, PMF.uniformOfFintype_apply]
  | succ w ih =>
    simp only [fairWord, ih, uniform_pair]
    exact PMF.uniformOfFintype_map_of_bijective _ (joinBit w).bijective

noncomputable def fairSample (n w : Nat) : Nat → PMF (Option (Fin n))
  | 0 => PMF.pure none
  | k + 1 => ((fairWord w).map (accept n)).bind fun
      | none => fairSample n w k
      | some x => PMF.pure (some x)

theorem fairSample_eq (n w k : Nat) : fairSample n w k = sample n w k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [fairSample, sample, fairWord_uniform, draw, ih]

/-- Executable tape interpretation; the second component counts words consumed. -/
def runTape (n : Nat) {w : Nat} : List (Fin (2 ^ w)) → Option (Fin n) × Nat
  | [] => (none, 0)
  | x :: xs => match accept n x with
      | some y => (some y, 1)
      | none => let r := runTape n xs; (r.1, r.2 + 1)

theorem runTape_steps (n : Nat) {w : Nat} (xs : List (Fin (2 ^ w))) :
    (runTape n xs).2 ≤ xs.length := by
  induction xs with
  | nil => simp [runTape]
  | cons x xs ih =>
    simp only [runTape, List.length_cons]
    split <;> dsimp only <;> omega

theorem runTape_bits (n : Nat) {w : Nat} (xs : List (Fin (2 ^ w))) :
    w * (runTape n xs).2 ≤ w * xs.length :=
  Nat.mul_le_mul_left w (runTape_steps n xs)

noncomputable def fairTape (w : Nat) : Nat → PMF (List (Fin (2 ^ w)))
  | 0 => PMF.pure []
  | k + 1 => (fairWord w).bind fun x => (fairTape w k).map (x :: ·)

theorem fairTape_length (w k : Nat) (xs : List (Fin (2 ^ w)))
    (hxs : xs ∈ (fairTape w k).support) : xs.length = k := by
  induction k generalizing xs with
  | zero =>
    have hx : xs = [] := (PMF.mem_support_pure_iff _ _).mp hxs
    simp only [hx, List.length_nil]
  | succ k ih =>
    obtain ⟨x, _, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hxs
    obtain ⟨ys, hys, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    exact congrArg Nat.succ (ih ys hys)

/-- Every supported execution consumes at most w*k fair bits. -/
theorem fairTape_bit_budget (n w k : Nat) (xs : List (Fin (2 ^ w)))
    (hxs : xs ∈ (fairTape w k).support) : w * (runTape n xs).2 ≤ w * k := by
  simpa only [fairTape_length w k xs hxs] using runTape_bits n xs

/-- The executable, early-stopping tape interpreter has the proved sampler law. -/
theorem runTape_distribution (n w k : Nat) :
    (fairTape w k).map (fun xs => (runTape n xs).1) = fairSample n w k := by
  induction k with
  | zero => simp only [fairTape, PMF.pure_map, runTape, fairSample]
  | succ k ih =>
    simp only [fairTape, PMF.map_bind, PMF.map_comp, fairSample, PMF.bind_map]
    congr 1
    funext x
    dsimp only [Function.comp_def]
    cases h : accept n x with
    | none => simpa only [runTape, h] using ih
    | some y =>
      simp only [runTape, h]
      exact PMF.map_const _ _

theorem runTape_failure (n w k : Nat) (hfit : n ≤ 2 ^ w) :
    ((fairTape w k).map (fun xs => (runTape n xs).1)) none =
      (1 - n * (2 ^ w : ℝ≥0∞)⁻¹) ^ k := by
  rw [runTape_distribution, fairSample_eq, failure n w k hfit]

theorem failure_le_half (n w k : Nat) (hfit : n ≤ 2 ^ w) (hhalf : 2 ^ w ≤ 2 * n) :
    sample n w k none ≤ (1 / 2 : ℝ≥0∞) ^ k := by
  rw [failure n w k hfit]
  apply pow_le_pow_left'
  have hprob : (1 / 2 : ℝ≥0∞) ≤ n * (2 ^ w : ℝ≥0∞)⁻¹ := by
    rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le
      (Or.inl (by positivity)) (Or.inr (by simp))]
    rw [one_div, mul_comm, ← div_eq_mul_inv, ENNReal.div_le_iff (by norm_num) (by norm_num)]
    exact_mod_cast (show 2 ^ w ≤ n * 2 by simpa only [Nat.mul_comm] using hhalf)
  have := tsub_le_tsub_left hprob 1
  norm_num at this ⊢
  exact this

/-- Choosing the binary length of n gives failure at most 2^(-k). -/
theorem failure_size (n k : Nat) (hn : 0 < n) :
    sample n n.size k none ≤ (1 / 2 : ℝ≥0∞) ^ k := by
  apply failure_le_half _ _ _ (Nat.lt_size_self n).le
  have hs : 0 < n.size := Nat.size_pos.mpr hn
  have h := Nat.lt_size.mp (show n.size - 1 < n.size by omega)
  have he : n.size = (n.size - 1) + 1 := by omega
  calc
    2 ^ n.size = 2 * 2 ^ (n.size - 1) := by
      conv_lhs => rw [he, pow_succ]
      exact Nat.mul_comm _ _
    _ ≤ 2 * n := Nat.mul_le_mul_left 2 h

end Signatures.Runtime.RejectionSampling
