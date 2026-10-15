import Signatures.Schnorr.Proofs.FixedTapeROM
import Signatures.Schnorr.Proofs.LazyFork
import Signatures.Schnorr.Proofs.LazySampling

/-! The named lazy Schnorr reduction inherits the original fixed-private-tape
EUF-CMA bound, with the signing-simulation loss and fork denominator unchanged.
This is a probability theorem; native implementation costs are separate. -/

open OracleComp OracleSpec DiffieHellman MeasureTheory

namespace Schnorr.LazyROM

variable {F G M : Type} [Field F] [SampleableType F] [Fintype F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G] [DecidableEq M]

section Correspondence

variable [MeasurableSpace F] [DiscreteMeasurableSpace F]

local instance securityInhabited : Inhabited F := ⟨0⟩

noncomputable local instance securityUniformChallenges : IsUniformSpec (Unit →ₒ F) :=
  IsUniformSpec.ofFintypeInhabited _

noncomputable local instance securityNativeMeasure : IsUniformMeasureSpec (FixedTape.Spec F) :=
  OracleSpec.instIsUniformMeasureSpecOfIsUniformSpec

/-- Correspondence includes extraction and the final interpretation of all
randomness. The reference cover is deduplicated only in the proof experiment. -/
theorem dlogReduction_eq_fixed (g pk : G) (adv : ROM.Adversary (F := F) (M := M) g)
    (privateFamilies : List Nat) (qR qH : Nat)
    (bound : IsPerIndexQueryBound (main g pk adv)
      (FixedTape.finiteBounds privateFamilies qR (qH + 1))) :
    𝒟[dlogReduction g adv qH g pk] =
      𝒟[FixedTape.dlogReduction g adv privateFamilies.dedup qR qH g pk] := by
  let : MeasurableSpace (FiatShamir.Fork.Trace G F F M) := ⊤
  change 𝒟[simulateQ sample (fork (main g pk adv) qH (FiatShamir.Fork.forkPoint G F F M qH) >>=
      FiatShamir.nmaForkExtractBranch (M := M) (Schnorr.sigma F G g))] =
    𝒟[simulateQ sample (FixedTape.completeFork (main g pk adv) privateFamilies.dedup qR qH
      (FiatShamir.Fork.forkPoint G F F M qH) >>=
      FiatShamir.nmaForkExtractBranch (M := M) (Schnorr.sigma F G g))]
  rw [sample_measure, sample_measure]
  have reachable : PathCfReachable (main g pk adv) (FiatShamir.nmaForkBudget qH) (.inr ())
      (FiatShamir.Fork.forkPoint G F F M qH) :=
    CfReachable.toPathCfReachable
      (FiatShamir.Fork.runTrace_forkPoint_CfReachable
        (σ := Schnorr.sigma F G g) (hr := dlogGenerable F g) (M := M)
        (FiatShamir.cmaToNmaAdv (Schnorr.sigma F G g) (dlogGenerable F g) M
          (Schnorr.simTranscript F G g) adv) qH pk)
  have hfork := fork_eq_complete (main g pk adv) privateFamilies qR qH
    (FiatShamir.Fork.forkPoint G F F M qH) bound reachable
  -- Traces contain function-valued caches and arbitrary messages. Singleton
  -- equality suffices for these atomic oracle laws; no countability premise
  -- or discreteness assumption on the product sigma-algebra is needed.
  apply Signatures.Runtime.SeededDeferred.measure_of_compat
  apply congrArg SPMF.toMeasure
  rw [liftM_bind, liftM_bind]
  congr 1
  apply evalSPMF_ext
  intro result
  have h := congrArg (fun measure : Measure (Option
    (FiatShamir.Fork.Trace G F F M × FiatShamir.Fork.Trace G F F M)) => measure {result}) hfork
  simpa only [evalDist_apply_singleton] using h

/-- Pointwise equality of the extracted scalars also preserves the complete
key-averaged DLog experiment, including its equality test. -/
theorem dlogExperiment_eq_fixed (g : G) (adv : ROM.Adversary (F := F) (M := M) g)
    (privateFamilies : List Nat) (qR qH : Nat)
    (bound : ∀ pk, IsPerIndexQueryBound (main g pk adv)
      (FixedTape.finiteBounds privateFamilies qR (qH + 1))) :
    𝒟[dlogExperiment g (dlogReduction g adv qH)] =
      𝒟[dlogExperiment g (FixedTape.dlogReduction g adv privateFamilies.dedup qR qH)] := by
  unfold dlogExperiment
  apply evalDist_bind_congr
  intro secret
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete,
    dlogReduction_eq_fixed g (secret • g) adv privateFamilies qR qH (bound (secret • g))]

end Correspondence

/-- The source game's full EUF-CMA probability is bounded by the success of the
named lazy DLog reduction. No eager seed allocation occurs in that reduction.
The seed-cover premise bounds the source query tree on every reply path; it is
not an assumption about the reduction's runtime or extraction success. -/
theorem security (g : G) (generates : Function.Bijective (fun x : F => x • g))
    (adv : ROM.Adversary (F := F) (M := M) g) (privateFamilies : List Nat) (qR qS qH : Nat)
    (queries : ∀ pk, FiatShamir.signHashQueryBound (M := M) (oa := adv.main pk) qS qH)
    (bound : ∀ pk, IsPerIndexQueryBound (main g pk adv)
      (FixedTape.finiteBounds privateFamilies qR (qH + 1))) :
    let eps := 𝒟[ROM.game g adv] {true} -
      (qS : ENNReal) * (qS + qH) * (Fintype.card F : ENNReal)⁻¹
    eps * (eps / (qH + 1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      𝒟[dlogExperiment g (dlogReduction g adv qH)] {true} := by
  let : MeasurableSpace F := ⊤
  rw [dlogExperiment_eq_fixed g adv privateFamilies qR qH bound]
  apply FixedTape.security g generates adv privateFamilies.dedup qR qS qH queries
  intro pk
  rw [finiteBounds_dedup]
  exact bound pk

end Schnorr.LazyROM
