import Proofs.Runtime.BitRejectionDistribution

/-! Sample near the range's binary width, then extend to the machine's common
word width. Padding is constructed and copied with charged bit operations.
The rejection failure flag is unchanged. -/

namespace Signatures.Runtime.PaddedSampling

open HeapBits SharedHeap PrimeFieldCircuit OracleComp

def width (n w : Nat) : Nat := min n.size w

theorem width_le (n w : Nat) : width n w ≤ w := min_le_right _ _

theorem fits (n w : Nat) (h : n ≤ 2^w) : n ≤ 2^(width n w) := by
  unfold width
  rw [min_def]
  split
  · exact (Nat.lt_size_self n).le
  · exact h

theorem half (n w : Nat) (hn : 0 < n) : 2^(width n w) ≤ 2*n := by
  have h := Nat.lt_size.mp (show n.size-1 < n.size by have := Nat.size_pos.mpr hn; omega)
  have he : n.size = (n.size-1)+1 := by have := Nat.size_pos.mpr hn; omega
  have hs : 2^n.size ≤ 2*n := by rw [he, Nat.pow_succ]; omega
  exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (min_le_left n.size w)).trans hs

structure Code where
  sampler : BitRejection.Code
  padding : List Unit
  deriving Repr

def compile (n w k : Nat) : Code :=
  ⟨BitRejection.compile n (width n w) k, List.replicate (w-width n w) ()⟩

def run (code : Code) : OracleComp BitRejection.bitSpec (Run (List Bool × Bool)) := do
  let sample ← BitRejection.executeDefault code.sampler
  let zeros := BitRejection.zeroWord code.padding
  let word := HeapBits.append sample.value.1 zeros.value
  pure ⟨(word.value, sample.value.2), sample.steps+zeros.steps+word.steps+3⟩

def budget (n w k : Nat) : Nat := k*(10*width n w+6)+2*width n w+2*w+8

theorem exponent_zeroes (xs : List Bool) (k : Nat) :
    exponent (xs ++ List.replicate k false) = exponent xs := by
  induction xs with
  | nil =>
    simp only [List.nil_append, exponent]
    induction k <;> simp_all [List.replicate_succ, exponent]
  | cons b xs ih => simp [exponent, ih]

theorem pad_bits (v w x : Nat) (hv : v ≤ w) (hx : x < 2^v) :
    natBits v x ++ natBits (w-v) 0 = natBits w x := by
  apply BitRejection.exponent_injective
  · simp only [List.length_append, natBits, List.length_ofFn]
    omega
  · have hz : natBits (w-v) 0 = List.replicate (w-v) false := by simp [natBits]
    rw [hz, exponent_zeroes, HeapLoop.exponent_natBits _ _ hx,
      HeapLoop.exponent_natBits _ _ (hx.trans_le (Nat.pow_le_pow_right (by decide) hv))]

/-- Every output is a canonical machine-width word, even on sampler failure. -/
theorem run_support (n w k : Nat) (hn : 0 < n) (out : Run (List Bool × Bool))
    (hout : out ∈ support (run (compile n w k))) :
    out.value.1 = natBits w (exponent out.value.1) ∧ exponent out.value.1 < n ∧
    out.value.1.length = w ∧ out.steps ≤ budget n w k := by
  simp only [run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
  obtain ⟨sample, hs, rfl⟩ := hout
  have h := BitRejection.executeDefault_support n (width n w) k hn sample hs
  have hz := BitRejection.zeroWord_spec (List.replicate (w-width n w) ())
  simp only [List.length_replicate] at hz
  have hw := width_le n w
  have hbits : sample.value.1 = natBits (width n w) (exponent sample.value.1) := by
    apply BitRejection.exponent_injective
    · simp [natBits, h.1]
    · rw [HeapLoop.exponent_natBits _ _ (by simpa [h.1] using BitRejection.exponent_lt sample.value.1)]
  have hx : exponent sample.value.1 < 2^(width n w) := by
    simpa [h.1] using BitRejection.exponent_lt sample.value.1
  have hp := pad_bits (width n w) w (exponent sample.value.1) hw hx
  have hv : (HeapBits.append sample.value.1 (BitRejection.zeroWord (compile n w k).padding).value).value =
      natBits w (exponent sample.value.1) := by
    rw [append_value]
    exact (congrArg₂ (fun a b : List Bool => a ++ b) hbits hz.1).trans hp
  simp only [hv, HeapLoop.exponent_natBits _ _ (hx.trans_le (Nat.pow_le_pow_right (by decide) hw))]
  refine ⟨trivial, h.2.1, by simp [natBits], ?_⟩
  simp only [compile, hz.2, append_steps, h.1, budget]
  omega

theorem run_queries (n w k : Nat) :
    IsQueryBoundP (run (compile n w k)) (fun _ => True) (k*width n w) := by
  have h : IsQueryBoundP (run (compile n w k)) (fun _ => True) (k*width n w+0) := by
    exact isQueryBoundP_bind (BitRejection.executeDefault_queries n (width n w) k)
      (fun _ _ => isQueryBoundP_pure _ _ _)
  simpa only [Nat.add_zero] using h

open scoped ENNReal

/-- Padding changes only the encoding width, not the sampled value or flag. -/
theorem distribution (n w k : Nat) (hfit : n ≤ 2^w) :
    (simulateQ (fun _ : Unit => PMF.uniformOfFintype Bool) (run (compile n w k))).map Run.value =
      (RejectionSampling.sample n (width n w) k).map
        (fun x => ((x.map (fun y => natBits w y.val)).getD (natBits w 0), x.isNone)) := by
  let fair : QueryImpl BitRejection.bitSpec PMF := fun _ => PMF.uniformOfFintype Bool
  have hz := (BitRejection.zeroWord_spec (List.replicate (w-width n w) ())).1
  simp only [List.length_replicate] at hz
  calc
    _ = ((simulateQ fair (BitRejection.executeDefault (BitRejection.compile n (width n w) k))).map
        Run.value).map (fun p => (p.1 ++ natBits (w-width n w) 0, p.2)) := by
      simp only [run, compile, simulateQ_bind, simulateQ_pure, PMF.monad_bind_eq_bind,
        PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map, PMF.map_comp,
        Function.comp_def, append_value, hz]
      rfl
    _ = _ := by
      rw [BitRejection.executeDefault_distribution, PMF.map_comp]
      congr 1
      funext x
      cases x with
      | none =>
        change (natBits (width n w) 0 ++ natBits (w-width n w) 0, true) = (natBits w 0, true)
        rw [pad_bits _ _ _ (width_le n w) (by positivity)]
      | some x =>
        change (natBits (width n w) x.val ++ natBits (w-width n w) 0, false) = (natBits w x.val, false)
        rw [pad_bits _ _ _ (width_le n w) (x.isLt.trans_le (fits n w hfit))]

theorem bad_eq (n w k : Nat) (hfit : n ≤ 2^w) :
    ((simulateQ (fun _ : Unit => PMF.uniformOfFintype Bool) (run (compile n w k))).map
      (fun out => out.value.2)) true = (1-n*(2^(width n w) : ℝ≥0∞)⁻¹)^k := by
  have hm := PMF.map_comp (Run.value : Run (List Bool × Bool) → List Bool × Bool)
    (simulateQ (fun _ : Unit => PMF.uniformOfFintype Bool) (run (compile n w k))) Prod.snd
  simp only [Function.comp_def] at hm
  rw [← hm, distribution n w k hfit, PMF.map_comp, PMF.map_apply]
  simp only [Function.comp_def, Bool.true_eq, Option.isNone_iff_eq_none]
  simpa using RejectionSampling.failure n (width n w) k (fits n w hfit)

theorem bad_le (n w k : Nat) (hn : 0 < n) (hfit : n ≤ 2^w) :
    ((simulateQ (fun _ : Unit => PMF.uniformOfFintype Bool) (run (compile n w k))).map
      (fun out => out.value.2)) true ≤ (1/2 : ℝ≥0∞)^k := by
  rw [bad_eq n w k hfit, ← RejectionSampling.failure n (width n w) k (fits n w hfit)]
  exact RejectionSampling.failure_le_half n (width n w) k (fits n w hfit) (half n w hn)

end Signatures.Runtime.PaddedSampling
