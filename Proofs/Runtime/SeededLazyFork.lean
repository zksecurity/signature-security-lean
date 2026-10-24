import Proofs.Runtime.SeededDeferredContinuation
import VCVio.CryptoFoundations.SeededFork

/-! Full distributional equality between a pregenerated seeded fork and a
fork retaining only encountered answers. The selector must point to an answer
actually consumed in the first run, so its collision guard is log-determined.
The finite family list appears only in the pregenerated reference experiment. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.SeededLazyFork

variable {I A : Type} {spec : OracleSpec I} [DecidableEq I]

theorem restore_entry (log : QueryLog spec) (suffix : QuerySeed spec) (target : I)
    (slot : Nat) (within : slot < (SeededTrace.restore log ∅ target).length) :
    (SeededTrace.restore log suffix target)[slot]? =
      (SeededTrace.restore log ∅ target)[slot]? := by
  rw [SeededTrace.restore_eq_append log suffix]
  exact List.getElem?_append_left within

variable [∀ i, SampleableType (spec.Range i)] [∀ i, DecidableEq (spec.Range i)]
  [unifSpec ⊂ₒ spec]

/-- The actual fork controller after the first result: sample a replacement,
reject an unchanged answer, and accept only a replay selecting the same slot. -/
def afterFirst (main : OracleComp spec A) (target : I) {q : Nat}
    (select : A → Option (Fin q)) (first : A) (seed : QuerySeed spec) :
    OracleComp spec (Option (A × A)) := do
  match select first with
  | none => pure none
  | some slot =>
      let answer ← liftComp ($ᵗ spec.Range target) spec
      if (seed target)[slot.val]? = some answer then pure none
      else
        let second ← (simulateQ seededOracle main).run'
          ((seed.takeAtIndex target slot.val).addValue target answer)
        if select second = some slot then pure (some (first, second)) else pure none

/-- Record one live execution; restart with its recorded answers, replacing
the selected target answer and discarding later answers of that family only. -/
def recordedFork (main : OracleComp spec A) (target : I) {q : Nat}
    (select : A → Option (Fin q)) : OracleComp spec (Option (A × A)) := do
  let first ← main.withQueryLog
  afterFirst main target select first.1 (SeededTrace.restore first.2 ∅)

variable [IsUniformSpec spec]
  [∀ i, MeasurableSpace (spec.Range i)] [∀ i, DiscreteMeasurableSpace (spec.Range i)]
  [unifSpec ˡ⊂ₒ spec] [MeasurableSpace A]

omit [unifSpec ˡ⊂ₒ spec] [∀ i, DecidableEq (spec.Range i)] in
private theorem discard_seed {B : Type} [MeasurableSpace B]
    (budget : I → Nat) (families : List I) (result : B) :
    𝒟[do
      let _ ← liftComp (generateSeed spec budget families) spec
      pure result] = 𝒟[(pure result : OracleComp spec B)] := by
  apply SeededDeferred.measure_of_compat
  apply congrArg SPMF.toMeasure
  apply evalSPMF_ext
  intro output
  rw [probOutput_bind_const]
  simp

/-- Unused entries disappear even with replacement sampling, the old-answer
comparison, and the replay's acceptance test all present in the controller. -/
theorem afterFirst_suffix (main : OracleComp spec A) (target : I) {q : Nat}
    (select : A → Option (Fin q)) (first : A) (log : QueryLog spec)
    (within : ∀ slot, select first = some slot →
      slot.val < (SeededTrace.restore log ∅ target).length)
    (budget : I → Nat) (families : List I) :
    𝒟[do
      let suffix ← liftComp (generateSeed spec budget families) spec
      afterFirst main target select first (SeededTrace.restore log suffix)] =
    𝒟[afterFirst main target select first (SeededTrace.restore log ∅)] := by
  cases selected : select first with
  | none =>
      simp only [afterFirst, selected]
      exact discard_seed budget families none
  | some slot =>
      simp only [afterFirst, selected]
      rw [OracleComp.evalDist_bind_bind_swap]
      apply OracleComp.evalDist_bind_congr_of_support
      intro answer _
      have oldEntry (suffix : QuerySeed spec) :=
        restore_entry log suffix target slot.val (within slot selected)
      simp only [oldEntry]
      split
      · exact discard_seed budget families none
      · have h := SeededTrace.generate_reset_run
          ((fun second => if select second = some slot then some (first, second) else none) <$> main)
          budget families log target slot.val answer (Nat.le_of_lt (within slot selected))
        simp only [simulateQ_map, StateT.run'_map'] at h
        simpa only [map_eq_bind_pure_comp, Function.comp_def, apply_ite] using h

/-- Exact joint output law of the complete fork, not just a marginal success
bound. No finite universe of oracle families is required by the lazy side. -/
theorem seededFork_eq_recordedFork (main : OracleComp spec A) (budget : I → Nat)
    (bound : IsPerIndexQueryBound main budget) (families : List I)
    (unique : families.Nodup) (cover : SeedListCovers budget families) (target : I)
    (select : A → Option (Fin (budget target + 1)))
    (within : ∀ result ∈ support main.withQueryLog, ∀ slot, select result.1 = some slot →
      slot.val < (SeededTrace.restore result.2 ∅ target).length) :
    𝒟[seededFork main budget families target select] =
      𝒟[recordedFork main target select] := by
  unfold seededFork
  trans 𝒟[do
    let seed ← liftComp (generateSeed spec budget families) spec
    let first ← (simulateQ seededOracle main).run' seed
    afterFirst main target select first seed]
  · congr 1
    apply bind_congr
    intro seed
    apply bind_congr
    intro first
    cases selected : select first with
    | none => simp [afterFirst, selected]
    | some slot =>
        simp only [afterFirst, selected]
        apply bind_congr
        intro answer
        simp
  · trans 𝒟[do
      let seed ← liftComp (generateSeed spec budget families) spec
      let result ← (simulateQ seededOracle main.withQueryLog).run seed
      afterFirst main target select result.1.1 seed]
    · congr 1
      apply bind_congr
      intro seed
      rw [← SeededDeferred.logged_run_erase main seed, bind_map_left]
    · refine SeededDeferred.defer_continuation main budget bound families unique cover
        (fun result seed => afterFirst main target select result.1 seed)
        (fun result => afterFirst main target select result.1 (SeededTrace.restore result.2 ∅)) ?_
      intro result supported remaining
      exact afterFirst_suffix main target select result.1 result.2
        (within result supported) remaining families

end Signatures.Runtime.SeededLazyFork
