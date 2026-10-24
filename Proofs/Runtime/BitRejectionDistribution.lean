import Proofs.Runtime.BitRejection

/-! Distributional correctness for the costed bit-list rejection controller.
The same `run` definition is interpreted with independent uniform Boolean
draws. Its output is the encoded existing sampler, not merely a sampler with
the same support. -/

namespace Signatures.Runtime.BitRejection

open HeapBits SharedHeap PrimeFieldCircuit RejectionSampling
open scoped ENNReal

private def joinLow (w : Nat) : Bool × Fin (2^w) ≃ Fin (2^(w+1)) :=
  ((Equiv.prodComm Bool (Fin (2^w))).trans
    ((Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans finProdFinEquiv)).trans
      (finCongr (Nat.pow_succ 2 w).symm)

private theorem joinLow_value (w : Nat) (b : Bool) (x : Fin (2^w)) :
    (joinLow w (b, x)).val = x.val+x.val+b.toNat := by
  cases b <;> simp [joinLow, finProdFinEquiv, finTwoEquiv] <;> omega

private theorem natBits_joinLow (w : Nat) (b : Bool) (x : Fin (2^w)) :
    natBits (w+1) (joinLow w (b, x)).val = b :: natBits w x.val := by
  apply exponent_injective
  · simp [natBits]
  · rw [HeapLoop.exponent_natBits _ _ (joinLow w (b, x)).isLt]
    simp only [exponent, HeapLoop.exponent_natBits _ _ x.isLt, joinLow_value]

/-- The online word builder implements a uniform word and charges every bit. -/
theorem drawWord_distribution (w : Nat) :
    drawWord (PMF.uniformOfFintype Bool) (List.replicate w ()) =
      (PMF.uniformOfFintype (Fin (2^w))).map (fun x => ⟨natBits w x.val, 4*w+1⟩) := by
  induction w with
  | zero =>
    have h : (fun x : Fin (2^0) => (⟨natBits 0 x.val, 4*0+1⟩ : Run (List Bool))) =
        Function.const _ ⟨[], 1⟩ := rfl
    rw [h, PMF.map_const]
    rfl
  | succ w ih =>
    simp only [List.replicate_succ, drawWord, ih]
    change (PMF.uniformOfFintype Bool).bind (fun b =>
      ((PMF.uniformOfFintype (Fin (2^w))).map _).bind _) = _
    simp only [PMF.bind_map, PMF.monad_pure_eq_pure, Function.comp_def]
    change (PMF.uniformOfFintype Bool).bind (fun b =>
      (PMF.uniformOfFintype (Fin (2^w))).map
        (fun x => (⟨b :: natBits w x.val, 4*w+1+4⟩ : Run (List Bool)))) = _
    have hp := congrArg (fun p : PMF (Bool × Fin (2^w)) =>
      p.map (fun bx => (⟨bx.1 :: natBits w bx.2.val, 4*w+1+4⟩ : Run (List Bool))))
      (uniform_pair (X := Bool) (Y := Fin (2^w)))
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at hp
    rw [hp]
    have hj := PMF.uniformOfFintype_map_of_bijective (joinLow w) (joinLow w).bijective
    rw [← hj, PMF.map_comp]
    congr 1
    funext bx
    rcases bx with ⟨b, x⟩
    simp only [Function.comp_def, natBits_joinLow]
    congr 1

/-- Encoded-output equality includes aborts and early stopping. Static retry
fuel does not force consumption of the unused suffix after success. -/
theorem run_distribution (n w k : Nat) :
    (run (PMF.uniformOfFintype Bool) (List.replicate w ()) (compile n w k).limit
      (List.replicate k ())).map Run.value =
    (sample n w k).map (Option.map (fun x => natBits w x.val)) := by
  induction k with
  | zero => simp [run, sample, PMF.pure_map]
  | succ k ih =>
    simp only [List.replicate_succ, run, drawWord_distribution]
    change (((PMF.uniformOfFintype (Fin (2^w))).map _).bind _).map Run.value = _
    simp only [PMF.bind_map, PMF.map_bind, Function.comp_def]
    simp only [sample, draw, PMF.bind_map, PMF.map_bind, Function.comp_def]
    congr 1
    funext x
    have ha := (accepts_compile n w (k+1) (natBits w x.val) (by simp [natBits])).1
    rw [HeapLoop.exponent_natBits _ _ x.isLt] at ha
    simp only [ha]
    by_cases hx : x.val < n
    · simp [hx, accept, copy_value, PMF.pure_map]
    · simp only [accept, hx, decide_false, Bool.false_eq_true, ite_false, dite_false,
        PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map]
      change (run (PMF.uniformOfFintype Bool) (List.replicate w ()) (compile n w k).limit
        (List.replicate k ())).map Run.value = _
      exact ih

/-- The law is for the actual oracle program, with each bit query independently
uniform, not for a disconnected probabilistic specification. -/
theorem execute_distribution (n w k : Nat) :
    (simulateQ (fun _ : Unit => PMF.uniformOfFintype Bool) (execute (compile n w k))).map Run.value =
      (sample n w k).map (Option.map (fun x => natBits w x.val)) := by
  simp only [execute, simulateQ_run, simulateQ_spec_query]
  exact run_distribution n w k

theorem execute_failure (n w k : Nat) (hfit : n ≤ 2^w) :
    ((simulateQ (fun _ : Unit => PMF.uniformOfFintype Bool) (execute (compile n w k))).map Run.value) none =
      (1 - n*(2^w : ℝ≥0∞)⁻¹)^k := by
  rw [execute_distribution, PMF.map_apply]
  simp only [Option.map_eq_none_iff, eq_comm (a := none)]
  simpa using failure n w k hfit

theorem execute_failure_size (n k : Nat) (hn : 0 < n) :
    ((simulateQ (fun _ : Unit => PMF.uniformOfFintype Bool)
      (execute (compile n n.size k))).map Run.value) none ≤ (1/2 : ℝ≥0∞)^k := by
  rw [execute_failure n n.size k (Nat.lt_size_self n).le]
  rw [← failure n n.size k (Nat.lt_size_self n).le]
  exact failure_size n k hn

theorem execute_some (n w k : Nat) (hfit : n ≤ 2^w) (x : Fin n) :
    ((simulateQ (fun _ : Unit => PMF.uniformOfFintype Bool) (execute (compile n w k))).map Run.value)
      (some (natBits w x.val)) = (1-(1-n*(2^w : ℝ≥0∞)⁻¹)^k)/n := by
  have hi : Function.Injective (fun y : Fin n => natBits w y.val) := by
    intro y z hyz
    have h := congrArg exponent hyz
    rw [HeapLoop.exponent_natBits _ _ (y.isLt.trans_le hfit),
      HeapLoop.exponent_natBits _ _ (z.isLt.trans_le hfit)] at h
    exact Fin.ext h
  have ho := Option.map_injective hi
  rw [execute_distribution]
  change (sample n w k).map (Option.map (fun y : Fin n => natBits w y.val))
    (Option.map (fun y : Fin n => natBits w y.val) (some x)) = _
  rw [PMF.map_apply]
  simp only [ho.eq_iff, eq_comm (a := some x), tsum_ite_eq]
  exact sample_some n w k hfit x

/-- The fallback flag records exactly the sampler's abort event. Successful
values are unchanged; the bad mass is not silently folded into uniform zero. -/
theorem executeDefault_distribution (n w k : Nat) :
    (simulateQ (fun _ : Unit => PMF.uniformOfFintype Bool) (executeDefault (compile n w k))).map Run.value =
      (sample n w k).map (fun x => ((x.map (fun y => natBits w y.val)).getD (natBits w 0), x.isNone)) := by
  let fair : QueryImpl bitSpec PMF := fun _ => PMF.uniformOfFintype Bool
  calc
    _ = (simulateQ fair (execute (compile n w k))).map
        (fun r => (r.value.getD (natBits w 0), r.value.isNone)) := by
      simp only [executeDefault, simulateQ_bind, PMF.monad_bind_eq_bind, PMF.map_bind]
      change (simulateQ fair (execute (compile n w k))).bind _ =
        (simulateQ fair (execute (compile n w k))).bind _
      congr 1
      funext r
      cases hx : r.value <;> simp only [simulateQ_pure, PMF.monad_pure_eq_pure, PMF.pure_map,
        compile, (zeroWord_spec (List.replicate w ())).1, List.length_replicate,
        Option.getD_none, Option.isNone_none, Option.getD_some, Option.isNone_some,
        Function.comp_def, hx]
    _ = ((simulateQ fair (execute (compile n w k))).map Run.value).map
        (fun x => (x.getD (natBits w 0), x.isNone)) := by rw [PMF.map_comp]; rfl
    _ = _ := by
      rw [execute_distribution, PMF.map_comp]
      congr 1
      funext x
      cases x <;> rfl

theorem executeDefault_bad (n w k : Nat) (hfit : n ≤ 2^w) :
    ((simulateQ (fun _ : Unit => PMF.uniformOfFintype Bool) (executeDefault (compile n w k))).map
      (fun out => out.value.2)) true = (1-n*(2^w : ℝ≥0∞)⁻¹)^k := by
  have hm := PMF.map_comp (Run.value : Run (List Bool × Bool) → List Bool × Bool)
    (simulateQ (fun _ : Unit => PMF.uniformOfFintype Bool) (executeDefault (compile n w k))) Prod.snd
  simp only [Function.comp_def] at hm
  rw [← hm]
  rw [executeDefault_distribution, PMF.map_comp, PMF.map_apply]
  simp only [Function.comp_def, Bool.true_eq, Option.isNone_iff_eq_none]
  simpa using failure n w k hfit

end Signatures.Runtime.BitRejection
