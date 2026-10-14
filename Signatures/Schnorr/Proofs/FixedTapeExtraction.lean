import Signatures.Schnorr.Proofs.FixedTape
import Signatures.Runtime.SeededReplay
import VCVio.CryptoFoundations.FiatShamir.Sigma.Reductions

/-! Fixed-private-tape extraction for Fiat--Shamir, specialized to Schnorr by
the security endpoint. Seed capacity includes the final verification query;
the candidate labels still have cardinality `qH + 1`. -/

open OracleComp OracleSpec

namespace Schnorr.FixedTape

/-- An explicit list avoids enumerating every range below the largest sampler.
For compiled sources this list comes from their sampling instructions. -/
def finiteBounds (privateFamilies : List Nat) (qR qH : Nat) : Nat ⊕ Unit → Nat
  | .inl n => if n ∈ privateFamilies then qR else 0
  | .inr () => qH

def seedFamilies (privateFamilies : List Nat) : List (Nat ⊕ Unit) :=
  privateFamilies.map Sum.inl ++ [Sum.inr ()]

theorem seedFamilies_cover (privateFamilies : List Nat) (qR qH : Nat) (i : Nat ⊕ Unit)
    (hi : finiteBounds privateFamilies qR qH i ≠ 0) : i ∈ seedFamilies privateFamilies := by
  cases i with
  | inl n =>
      have hn : n ∈ privateFamilies := by
        by_contra hn
        exact hi (by simp [finiteBounds, hn])
      simp [seedFamilies, hn]
  | inr u => cases u; simp [seedFamilies]

attribute [local implicit_reducible] finiteBounds FiatShamir.nmaForkBudget

variable {F A : Type} [SampleableType F] [DecidableEq F]

/-- Seed all private draws and all `qH + 1` fresh challenge positions, including
the final verifier query. The selector has exactly `qH + 1` possible labels. -/
def completeFork (main : OracleComp (Spec F) A) (privateFamilies : List Nat) (qR qH : Nat)
    (cf : A → Option (Fin (qH + 1))) : OracleComp (Spec F) (Option (A × A)) :=
  seededFork main (finiteBounds privateFamilies qR (qH + 1)) (seedFamilies privateFamilies) (.inr ())
    (Option.map Fin.castSucc ∘ cf)

theorem complete_seed_covers (privateFamilies : List Nat) (qR qH : Nat)
    (seed : QuerySeed (Spec F))
    (hs : seed ∈ support (generateSeed (Spec F) (finiteBounds privateFamilies qR (qH + 1))
      (seedFamilies privateFamilies))) :
    ∀ i, finiteBounds privateFamilies qR (qH + 1) i ≤ (seed i).length :=
  fun i => le_length_of_mem_support_generateSeed_of_covers (Spec F)
    (finiteBounds privateFamilies qR (qH + 1)) (seedFamilies privateFamilies) seed i hs
    (fun j hj => seedFamilies_cover privateFamilies qR (qH + 1) j (Nat.ne_of_gt hj))

/-- No private randomness is sampled live in either run. The only unseeded
queries in the second run are hash challenges after the selected position. -/
theorem complete_replay_live_bound (main : OracleComp (Spec F) A)
    (privateFamilies : List Nat) (qR qH : Nat)
    (hmain : IsPerIndexQueryBound main (finiteBounds privateFamilies qR (qH + 1)))
    (seed : QuerySeed (Spec F))
    (hs : seed ∈ support (generateSeed (Spec F) (finiteBounds privateFamilies qR (qH + 1))
      (seedFamilies privateFamilies))) (slot : Fin (qH + 1)) (c : F) :
    IsPerIndexQueryBound ((simulateQ seededOracle main).run' seed) 0 ∧
    IsPerIndexQueryBound ((simulateQ seededOracle main).run'
      ((seed.takeAtIndex (.inr ()) slot.val).addValue (.inr ()) c))
      (Function.update 0 (.inr ()) (qH + 1 - (slot.val + 1))) := by
  have hc := complete_seed_covers privateFamilies qR qH seed hs
  exact ⟨seededOracle.isPerIndexQueryBound_run'_zero hmain hc,
    seededOracle.isPerIndexQueryBound_run'_takeAtIndex_addValue
      (i := Sum.inr ()) hmain hc slot.castSucc c⟩

noncomputable local instance [Fintype F] [Inhabited F] : IsUniformSpec (Unit →ₒ F) :=
  IsUniformSpec.ofFintypeInhabited _

theorem completeFork_success_bound [Fintype F] [Inhabited F]
    (main : OracleComp (Spec F) A) (privateFamilies : List Nat) (qR qH : Nat)
    (cf : A → Option (Fin (qH + 1))) :
    let acc : ENNReal := ∑ s, Pr[= some s | cf <$> main]
    acc * (acc / (qH + 1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      Pr[fun r => r.isSome | completeFork main privateFamilies qR qH cf] := by
  have hcard : Fintype.card ((Spec F).Range (.inr ())) = Fintype.card F :=
    Fintype.card_congr (Equiv.refl F)
  simpa only [completeFork, hcard, Nat.cast_add, Nat.cast_one] using
    Signatures.Runtime.SeededReplay.seededFork_success_bound_labels main
      (finiteBounds privateFamilies qR (qH + 1)) (seedFamilies privateFamilies) (.inr ()) cf
      Fin.castSucc (Fin.castSucc_injective _)

/-- A complete seeded fork satisfies the same shared-prefix and distinct-answer
invariants as the established contextual extractor. -/
theorem completeFork_support_context
    (main : OracleComp (Spec F) A) (privateFamilies : List Nat) (qR qH : Nat)
    (cf : A → Option (Fin (qH + 1)))
    (hmain : IsPerIndexQueryBound main (finiteBounds privateFamilies qR (qH + 1)))
    (hreach : PathCfReachable main (FiatShamir.nmaForkBudget qH) (.inr ()) cf)
    {x₁ x₂ : A}
    (h : some (x₁, x₂) ∈ support (completeFork main privateFamilies qR qH cf)) :
    some (x₁, x₂) ∈ support (contextFork main (FiatShamir.nmaForkBudget qH) (.inr ()) cf) := by
  have hreach' : PathCfReachable main (finiteBounds privateFamilies qR (qH + 1)) (.inr ())
      (Option.map Fin.castSucc ∘ cf) := by
    intro path s hs
    simp only [Function.comp_def] at hs
    simp only [Option.map_eq_some_iff] at hs
    obtain ⟨slot, hs, rfl⟩ := hs
    exact hreach path slot hs
  have hctx := Signatures.Runtime.SeededReplay.seededFork_support_context main
    (finiteBounds privateFamilies qR (qH + 1)) (seedFamilies privateFamilies) (.inr ())
    (Option.map Fin.castSucc ∘ cf) hmain
    (fun i hi => seedFamilies_cover privateFamilies qR (qH + 1) i (Nat.ne_of_gt hi)) hreach' h
  exact Signatures.Runtime.SeededReplay.contextFork_support_castLE main
    (FiatShamir.nmaForkBudget qH) (finiteBounds privateFamilies qR (qH + 1)) (.inr ())
    (Nat.le_succ _) cf hctx

end Schnorr.FixedTape

namespace FiatShamir.FixedTape

variable {Stmt Wit Commit PrvState Chal Resp M : Type} {rel : Stmt → Wit → Bool}
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel) (M : Type)
variable [DecidableEq M] [DecidableEq Commit] [DecidableEq Chal]
  [SampleableType Wit] [SampleableType Chal]

/-- Named extractor using a single complete private tape for both runs. -/
def nmaForkExtract (adv : SignatureAlg.ManagedRoNmaAdversary (inROM σ hr M))
    (privateFamilies : List Nat) (qR qH : Nat) (pk : Stmt) :
    OracleComp (Schnorr.FixedTape.Spec Chal) Wit :=
  Schnorr.FixedTape.completeFork (Fork.runTrace σ hr M adv pk) privateFamilies qR qH
    (Fork.forkPoint Commit Chal Resp M qH) >>= nmaForkExtractBranch (M := M) σ

/-- Interpret private draws and fresh hash challenges as uniform sampling. -/
def nmaReduction (adv : SignatureAlg.ManagedRoNmaAdversary (inROM σ hr M))
    (privateFamilies : List Nat) (qR qH : Nat) : Stmt → ProbComp Wit := fun pk =>
  simulateQ (QueryImpl.ofLift unifSpec ProbComp + uniformSampleImpl (spec := Unit →ₒ Chal))
    (nmaForkExtract σ hr M adv privateFamilies qR qH pk)

private def TraceInvariant (qH : Nat) (pk : Stmt)
    (x : Fork.Trace Commit Chal Resp M)
    (log : QueryLog (unifSpec + (Unit →ₒ Chal))) : Prop :=
  ∀ s : Fin (qH + 1), Fork.forkPoint Commit Chal Resp M qH x = some s →
    ∃ c : Chal, QueryLog.getQueryValue? log (.inr ()) s.val = some c ∧
      x.roCache x.target = some c ∧ σ.verify pk x.target.2 c x.forgery.2.2 = true

omit [DecidableEq Chal] [SampleableType Wit] in
private theorem traceInvariant_of_support
    (adv : SignatureAlg.ManagedRoNmaAdversary (inROM σ hr M)) (qH : Nat) (pk : Stmt)
    {x : Fork.Trace Commit Chal Resp M} {log : QueryLog (unifSpec + (Unit →ₒ Chal))}
    (h : (x, log) ∈ support (replayFirstRun (Fork.runTrace σ hr M adv pk))) :
    TraceInvariant σ M qH pk x log := by
  intro s hs
  have htarget := Fork.forkPoint_getElem?_eq_some_target (M := M) (Commit := Commit)
    (Resp := Resp) (Chal := Chal) hs
  have hverified := Fork.verified_of_forkPoint_eq_some (M := M) (Commit := Commit)
    (Resp := Resp) (Chal := Chal) hs
  obtain ⟨hslt, htgt_eq⟩ := List.getElem?_eq_some_iff.1 htarget
  obtain ⟨c, hcache, hlog⟩ := Fork.runTrace_cache_outer_lockstep σ hr M adv pk h s.val hslt
  rw [htgt_eq] at hcache
  obtain ⟨c', hcache', hverify⟩ :=
    Fork.exists_cached_verify_of_runTrace_verified σ hr M adv pk h hverified
  refine ⟨c, hlog, hcache, ?_⟩
  rwa [Option.some.inj (hcache'.symm.trans hcache)] at hverify

variable [Fintype Chal] [Inhabited Chal]

noncomputable local instance : IsUniformSpec (Unit →ₒ Chal) :=
  IsUniformSpec.ofFintypeInhabited _

/-- Every supported successful fork invokes special soundness on two accepting
transcripts with the same commitment and different cached challenges. -/
theorem branch_success_of_context
    (adv : SignatureAlg.ManagedRoNmaAdversary (inROM σ hr M)) (qH : Nat)
    (hss : σ.SpeciallySound) (pk : Stmt) {x₁ x₂ : Fork.Trace Commit Chal Resp M}
    (h : some (x₁, x₂) ∈ support (contextFork (Fork.runTrace σ hr M adv pk)
      (nmaForkBudget qH) (.inr ()) (Fork.forkPoint Commit Chal Resp M qH))) :
    Pr[fun w => rel pk w = true | nmaForkExtractBranch (M := M) σ (some (x₁, x₂))] = 1 := by
  classical
  obtain ⟨log₁, log₂, s, hcf₁, hcf₂, hP₁, hP₂, hneq⟩ :=
    contextFork_propertyTransfer (Fork.runTrace σ hr M adv pk) (nmaForkBudget qH)
      (.inr ()) (Fork.forkPoint Commit Chal Resp M qH) (TraceInvariant σ M qH pk)
      (fun h => traceInvariant_of_support σ hr M adv qH pk h) h
  obtain ⟨c₁, hlog₁, hcache₁, hverify₁⟩ := hP₁ s hcf₁
  obtain ⟨c₂, hlog₂, hcache₂, hverify₂⟩ := hP₂ s hcf₂
  simp only [Fork.Trace.target] at hcache₁ hcache₂ hverify₁ hverify₂
  have hne : c₁ ≠ c₂ := fun heq => hneq (by rw [hlog₁, hlog₂, heq])
  have hc : x₁.forgery.2.1 = x₂.forgery.2.1 :=
    congrArg Prod.snd (Fork.runTrace_target_eq_of_mem_contextFork σ hr M adv qH pk
      x₁ x₂ s h hcf₁ hcf₂)
  simp only [nmaForkExtractBranch, hcache₁, hcache₂, dite_eq_left hc, dite_eq_left hne,
    probEvent_liftComp]
  exact probEvent_eq_one_iff.2 ⟨probFailure_eq_zero' inferInstance, fun w hw =>
    SigmaProtocol.extract_sound_of_speciallySoundAt σ (hss pk) hne hverify₁
      (hc.symm ▸ hverify₂) hw⟩

omit [DecidableEq Chal] in
private theorem probEvent_sample_challenges {A : Type}
    (main : OracleComp (unifSpec + (Unit →ₒ Chal)) A) (p : A → Prop) :
    Pr[p | simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      uniformSampleImpl (spec := Unit →ₒ Chal)) main] = Pr[p | main] := by
  classical
  induction main using OracleComp.inductionOn with
  | pure x => simp only [simulateQ_pure, probEvent_pure]
  | query_bind t cont ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
        OracleQuery.input_query, probEvent_bind_eq_tsum, ih]
      refine tsum_congr fun u => ?_
      congr 1
      cases t with
      | inl n =>
          simp only [QueryImpl.add_apply_inl, QueryImpl.ofLift_eq_id', QueryImpl.id'_apply,
            probOutput_query, ← Nat.card_eq_fintype_card]
          rfl
      | inr t =>
          simp only [QueryImpl.add_apply_inr, uniformSampleImpl]
          exact probOutput_uniformSample_eq_query (spec := unifSpec + (Unit →ₒ Chal))
            (.inr t) u

/-- Fixed-private-tape extraction with the standard `qH + 1` denominator.
The premise bounds the source query tree on every possible reply path; it does
not assume the extractor's success or the finished reduction's runtime. -/
theorem pointwise_extraction_bound
    (adv : SignatureAlg.ManagedRoNmaAdversary (inROM σ hr M))
    (privateFamilies : List Nat) (qR qH : Nat) (hss : σ.SpeciallySound) (pk : Stmt)
    (hmain : IsPerIndexQueryBound (Fork.runTrace σ hr M adv pk)
      (Schnorr.FixedTape.finiteBounds privateFamilies qR (qH + 1))) :
    let acc : ENNReal := ∑ s, Pr[= some s |
      Fork.forkPoint Commit Chal Resp M qH <$> Fork.runTrace σ hr M adv pk]
    acc * (acc / (qH + 1 : ENNReal) - (Fintype.card Chal : ENNReal)⁻¹) ≤
      Pr[fun w => rel pk w = true | nmaReduction σ hr M adv privateFamilies qR qH pk] := by
  classical
  refine (Schnorr.FixedTape.completeFork_success_bound (Fork.runTrace σ hr M adv pk)
    privateFamilies qR qH (Fork.forkPoint Commit Chal Resp M qH)).trans ?_
  rw [nmaReduction, probEvent_sample_challenges, nmaForkExtract,
    probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun r => ?_
  cases r with
  | none => simp
  | some pair =>
      simp only [Option.isSome, ite_true]
      by_cases hsupp : some pair ∈ support (Schnorr.FixedTape.completeFork
          (Fork.runTrace σ hr M adv pk) privateFamilies qR qH (Fork.forkPoint Commit Chal Resp M qH))
      · have hctx := Schnorr.FixedTape.completeFork_support_context
          (Fork.runTrace σ hr M adv pk) privateFamilies qR qH
          (Fork.forkPoint Commit Chal Resp M qH) hmain
          (CfReachable.toPathCfReachable
            (Fork.runTrace_forkPoint_CfReachable (σ := σ) (hr := hr) (M := M)
              adv qH pk)) hsupp
        rw [branch_success_of_context σ hr M adv qH hss pk hctx, mul_one]
      · rw [probOutput_eq_zero_of_not_mem_support hsupp, zero_mul]

private theorem sum_forkPoint_eq_acceptance
    (adv : SignatureAlg.ManagedRoNmaAdversary (inROM σ hr M)) (qH : Nat) (pk : Stmt) :
    (∑ s, Pr[= some s | Fork.forkPoint Commit Chal Resp M qH <$>
      Fork.runTrace σ hr M adv pk]) =
    Pr[fun x => (Fork.forkPoint Commit Chal Resp M qH x).isSome |
      Fork.runTrace σ hr M adv pk] := by
  simpa only [probEvent_isSome_eq_tsum_probOutput_some, tsum_fintype, Function.comp_def] using
    probEvent_map (Fork.runTrace σ hr M adv pk)
      (Fork.forkPoint Commit Chal Resp M qH) (fun r => r.isSome)

/-- Average the fixed-tape extraction bound over generated public statements.
The same private tape is fixed within each fork, while key generation retains
its original distribution. -/
theorem nma_to_hard_relation_bound
    (adv : SignatureAlg.ManagedRoNmaAdversary (inROM σ hr M))
    (privateFamilies : List Nat) (qR qH : Nat) (hss : σ.SpeciallySound)
    (hmain : ∀ pk, IsPerIndexQueryBound (Fork.runTrace σ hr M adv pk)
      (Schnorr.FixedTape.finiteBounds privateFamilies qR (qH + 1))) :
    Fork.advantage σ hr M adv qH *
      (Fork.advantage σ hr M adv qH / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
    Pr[= true | hardRelationExperiment hr (nmaReduction σ hr M adv privateFamilies qR qH)] := by
  classical
  let acc : Stmt → ENNReal := fun pk =>
    Pr[fun x => (Fork.forkPoint Commit Chal Resp M qH x).isSome | Fork.runTrace σ hr M adv pk]
  have hAdv : Fork.advantage σ hr M adv qH =
      ∑' pkw : Stmt × Wit, Pr[= pkw | hr.gen] * acc pkw.1 := by
    simp only [Fork.advantage, Fork.experiment, ← probEvent_eq_eq_probOutput,
      probEvent_sample_challenges, probEvent_bind_eq_tsum, bind_pure_comp,
      probEvent_map, Function.comp_def, probEvent_liftComp, acc]
  have hReduction :
      Pr[= true | hardRelationExperiment hr (nmaReduction σ hr M adv privateFamilies qR qH)] =
      ∑' pkw : Stmt × Wit, Pr[= pkw | hr.gen] *
        Pr[fun w => rel pkw.1 w = true | nmaReduction σ hr M adv privateFamilies qR qH pkw.1] := by
    simp only [hardRelationExperiment, ← probEvent_eq_eq_probOutput, bind_pure_comp,
      probEvent_bind_eq_tsum, probEvent_map, Function.comp_def]
  have hPointwise : ∀ pk, acc pk * (acc pk / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
      Pr[fun w => rel pk w = true | nmaReduction σ hr M adv privateFamilies qR qH pk] := by
    intro pk
    simpa only [sum_forkPoint_eq_acceptance, challengeSpaceInv, acc] using
      pointwise_extraction_bound σ hr M adv privateFamilies qR qH hss pk (hmain pk)
  rw [hAdv, hReduction]
  simpa only [DiscreteEvalDistCompatible.lintegral_evalDist _ (g := fun a => a) measurable_id,
    ← OracleComp.EvalDist.expectedValue_def, OracleComp.EvalDist.expectedValue_map] using
    OracleComp.EvalDist.marginalized_jensen_forking_bound_map (mx := hr.gen)
      (acc := fun pkw => acc pkw.1)
      (B := fun pkw => Pr[fun w => rel pkw.1 w = true |
        nmaReduction σ hr M adv privateFamilies qR qH pkw.1])
      (q := (qH : ENNReal) + 1) (hinv := challengeSpaceInv Chal)
      (fun _ => probEvent_le_one) (fun pkw => hPointwise pkw.1)

/-- The CMA reduction uses the existing signing simulator and the new complete
private-tape extractor. -/
def cmaReduction (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (adv : SignatureAlg.UnforgeableAdversary (inROM σ hr M))
    (privateFamilies : List Nat) (qR qH : Nat) : Stmt → ProbComp Wit :=
  nmaReduction σ hr M (cmaToNmaAdv σ hr M simTranscript adv) privateFamilies qR qH

/-- The complete CMA bound for the named fixed-private-tape reduction. -/
theorem euf_cma_bound [Finite Stmt] [SampleableType Stmt]
    (hss : σ.SpeciallySound)
    (simTranscript : Stmt → ProbComp (Commit × Chal × Resp))
    (ζ : ℝ) (hζ : 0 ≤ ζ) (hhvzk : σ.HVZK simTranscript ζ)
    (β : ENNReal) (hpred : σ.simCommitPredictability simTranscript β)
    (adv : SignatureAlg.UnforgeableAdversary (inROM σ hr M))
    (privateFamilies : List Nat) (qR qS qH : Nat)
    (hQ : ∀ pk, signHashQueryBound (M := M) (oa := adv.main pk) qS qH)
    (hmain : ∀ pk, IsPerIndexQueryBound
      (Fork.runTrace σ hr M (cmaToNmaAdv σ hr M simTranscript adv) pk)
      (Schnorr.FixedTape.finiteBounds privateFamilies qR (qH + 1))) :
    let eps := SignatureAlg.unforgeableAdvantage (runtime M) adv -
      (ENNReal.ofReal ((qS : ℝ) * ζ) + (qS : ENNReal) * (qS + qH) * β)
    eps * (eps / (qH + 1 : ENNReal) - challengeSpaceInv Chal) ≤
      Pr[= true | hardRelationExperiment hr
        (cmaReduction σ hr M simTranscript adv privateFamilies qR qH)] := by
  have hAdv := cma_to_nma_advantage_bound σ hr M simTranscript ζ hζ hhvzk β hpred adv qS qH hQ
  refine le_trans ?_ (nma_to_hard_relation_bound σ hr M
    (cmaToNmaAdv σ hr M simTranscript adv) privateFamilies qR qH hss hmain)
  gcongr <;> exact tsub_le_iff_right.mpr (by simpa [add_assoc] using hAdv)

end FiatShamir.FixedTape
