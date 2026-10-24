import Proofs.Schnorr.LazyFiatShamirReduction
import Proofs.Schnorr.LazyROM

/-! The lazy controller inherits the complete-private-tape Fiat--Shamir bound
for any signing simulator satisfying the original HVZK and commitment laws.
The finite reference cover is derived in the proof and never constructed by
the reduction. Native runtime and encoded-memory bounds are separate. -/

open OracleComp OracleSpec MeasureTheory

namespace FiatShamir.LazyTape

variable {Stmt Wit Commit PrvState Chal Resp M : Type} {rel : Stmt → Wit → Bool}
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)
  [DecidableEq M] [DecidableEq Commit] [DecidableEq Chal]
  [SampleableType Wit] [SampleableType Chal]

omit [DecidableEq Chal] [SampleableType Wit] in
/-- Only hash queries and the final verifier lookup consume challenge slots. -/
theorem main_hashBound (simulator : Stmt → ProbComp (Commit × Chal × Resp))
    (adv : SignatureAlg.UnforgeableAdversary (inROM σ hr M)) (qS qH : Nat)
    (queries : ∀ pk, signHashQueryBound (M := M) (oa := adv.main pk) qS qH) (pk : Stmt) :
    IsQueryBoundP (main σ hr M simulator adv pk) (· = Sum.inr ()) (qH + 1) := by
  have before := Stateful.nmaAdvFromCma_nmaHashQueryBound σ hr M adv simulator qS qH queries pk
  have finalQuery : nmaHashQueryBound (M := M)
      (oa := (cmaToNmaAdv σ hr M simulator adv).main pk) (qH + 1) := by
    apply isQueryBoundP_bind before
    intro result _
    simp
  unfold main Fork.runTrace
  refine isQueryBoundP_bind (n := qH + 1) (m := 0) ?_ ?_
  swap
  · rintro ⟨⟨forgery, advCache⟩, roCache, log⟩ _
    simp
  apply finalQuery.simulateQ_run_of_step
  · intro i hi state
    rcases i with n | mc
    · simp at hi
    · rcases state with ⟨cache, log⟩
      simp only [QueryImpl.add_apply_inr]
      cases hcache : cache mc with
      | none =>
          rw [Fork.roImpl_run_none (M := M) (Commit := Commit) (Chal := Chal) mc cache log hcache]
          simp [Fork.wrappedChallengeQuery]
      | some answer =>
          rw [Fork.roImpl_run_some (M := M) (Commit := Commit) (Chal := Chal) mc cache log answer hcache]
          simp
  · intro i hi state
    rcases i with n | mc
    · simp [QueryImpl.add_apply_inl, Fork.unifForward_run, Fork.wrappedUniformQuery]
    · simp at hi

omit [DecidableEq Chal] [SampleableType Wit] in
/-- Finite reply branching and public-statement space give a proof-only cover.
Its cardinality is not an efficiency assumption or a runtime allowance. -/
theorem exists_seed_bound [Fintype Chal] [Finite Stmt]
    (simulator : Stmt → ProbComp (Commit × Chal × Resp))
    (adv : SignatureAlg.UnforgeableAdversary (inROM σ hr M)) (qS qH : Nat)
    (queries : ∀ pk, signHashQueryBound (M := M) (oa := adv.main pk) qS qH) :
    ∃ (privateFamilies : List Nat) (qR : Nat), ∀ pk,
      IsPerIndexQueryBound (main σ hr M simulator adv pk)
        (Schnorr.FixedTape.finiteBounds privateFamilies qR (qH + 1)) := by
  classical
  let : ∀ i, Finite ((Schnorr.FixedTape.Spec Chal).Range i) := fun i => by
    cases i <;> infer_instance
  obtain ⟨families, qR, bounded⟩ :=
    Signatures.Runtime.FiniteQueryCover.exists_bound_family (fun pk => main σ hr M simulator adv pk)
  refine ⟨families.toLeft.toList, qR, fun pk => ?_⟩
  apply (Signatures.Runtime.FiniteQueryCover.replace_bound (main σ hr M simulator adv pk) _ (.inr ())
    (qH + 1) (bounded pk) (main_hashBound σ hr M simulator adv qS qH queries pk)).mono
  intro i
  rcases i with n | ⟨⟩ <;> simp [Schnorr.FixedTape.finiteBounds]

variable [Fintype Chal] [Inhabited Chal]

section Correspondence

variable [MeasurableSpace Chal] [DiscreteMeasurableSpace Chal]
  [MeasurableSpace Wit]

noncomputable local instance : IsUniformSpec (Unit →ₒ Chal) :=
  IsUniformSpec.ofFintypeInhabited _

noncomputable local instance : IsUniformMeasureSpec (Schnorr.FixedTape.Spec Chal) :=
  OracleSpec.instIsUniformMeasureSpecOfIsUniformSpec

/-- Equality covers the whole extracted witness law, including failure fallback. -/
theorem reduction_eq_fixed (simulator : Stmt → ProbComp (Commit × Chal × Resp))
    (adv : SignatureAlg.UnforgeableAdversary (inROM σ hr M)) (pk : Stmt)
    (privateFamilies : List Nat) (qR qH : Nat)
    (bound : IsPerIndexQueryBound (main σ hr M simulator adv pk)
      (Schnorr.FixedTape.finiteBounds privateFamilies qR (qH + 1))) :
    𝒟[reduction σ hr M simulator adv qH pk] =
      𝒟[FixedTape.cmaReduction σ hr M simulator adv privateFamilies.dedup qR qH pk] := by
  let : MeasurableSpace (Fork.Trace Commit Chal Resp M) := ⊤
  change 𝒟[simulateQ Schnorr.LazyROM.sample
    (Schnorr.LazyROM.fork (main σ hr M simulator adv pk) qH
      (Fork.forkPoint Commit Chal Resp M qH) >>= nmaForkExtractBranch (M := M) σ)] =
    𝒟[simulateQ Schnorr.LazyROM.sample
      (Schnorr.FixedTape.completeFork (main σ hr M simulator adv pk) privateFamilies.dedup qR qH
        (Fork.forkPoint Commit Chal Resp M qH) >>= nmaForkExtractBranch (M := M) σ)]
  rw [Schnorr.LazyROM.sample_measure, Schnorr.LazyROM.sample_measure]
  have reachable : PathCfReachable (main σ hr M simulator adv pk) (nmaForkBudget qH) (.inr ())
      (Fork.forkPoint Commit Chal Resp M qH) :=
    CfReachable.toPathCfReachable (Fork.runTrace_forkPoint_CfReachable
      (σ := σ) (hr := hr) (M := M) (cmaToNmaAdv σ hr M simulator adv) qH pk)
  have hfork := Schnorr.LazyROM.fork_eq_complete (main σ hr M simulator adv pk)
    privateFamilies qR qH (Fork.forkPoint Commit Chal Resp M qH) bound reachable
  apply Signatures.Runtime.SeededDeferred.measure_of_compat
  apply congrArg SPMF.toMeasure
  rw [liftM_bind, liftM_bind]
  congr 1
  apply evalSPMF_ext
  intro result
  have h := congrArg (fun measure : Measure (Option
    (Fork.Trace Commit Chal Resp M × Fork.Trace Commit Chal Resp M)) => measure {result}) hfork
  simpa only [evalDist_apply_singleton] using h

end Correspondence

/-- The full key-averaged success probability agrees with the reference fork. -/
theorem experiment_eq_fixed (simulator : Stmt → ProbComp (Commit × Chal × Resp))
    (adv : SignatureAlg.UnforgeableAdversary (inROM σ hr M))
    (privateFamilies : List Nat) (qR qH : Nat)
    (bound : ∀ pk, IsPerIndexQueryBound (main σ hr M simulator adv pk)
      (Schnorr.FixedTape.finiteBounds privateFamilies qR (qH + 1))) :
    𝒟[hardRelationExperiment hr (reduction σ hr M simulator adv qH)] =
      𝒟[hardRelationExperiment hr
        (FixedTape.cmaReduction σ hr M simulator adv privateFamilies.dedup qR qH)] := by
  let : MeasurableSpace Chal := ⊤
  let : MeasurableSpace Wit := ⊤
  unfold hardRelationExperiment
  apply evalDist_bind_congr
  intro pkw
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete,
    reduction_eq_fixed σ hr M simulator adv pkw.1 privateFamilies qR qH (bound pkw.1)]

/-- Original Fiat--Shamir security for the lazy replay algorithm.
Only source query allowances enter; reference seed coverage is derived internally. -/
theorem security [Finite Stmt] [SampleableType Stmt]
    (hss : σ.SpeciallySound)
    (simulator : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ : ℝ) (hζ : 0 ≤ ζ) (hhvzk : σ.HVZK simulator ζ)
    (β : ENNReal) (hpred : σ.simCommitPredictability simulator β)
    (adv : SignatureAlg.UnforgeableAdversary (inROM σ hr M)) (qS qH : Nat)
    (queries : ∀ pk, signHashQueryBound (M := M) (oa := adv.main pk) qS qH) :
    let eps := SignatureAlg.unforgeableAdvantage (runtime M) adv -
      (ENNReal.ofReal ((qS : ℝ) * ζ) + (qS : ENNReal) * (qS + qH) * β)
    eps * (eps / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
      𝒟[hardRelationExperiment hr (reduction σ hr M simulator adv qH)] {true} := by
  obtain ⟨families, qR, bounded⟩ := exists_seed_bound σ hr M simulator adv qS qH queries
  rw [experiment_eq_fixed σ hr M simulator adv families qR qH bounded]
  have h := FixedTape.euf_cma_bound σ hr M hss simulator ζ hζ hhvzk β hpred adv
    families.dedup qR qS qH queries (fun pk => by
      rw [Schnorr.LazyROM.finiteBounds_dedup]
      exact bounded pk)
  simpa only [evalDist_apply_singleton] using h

end FiatShamir.LazyTape
