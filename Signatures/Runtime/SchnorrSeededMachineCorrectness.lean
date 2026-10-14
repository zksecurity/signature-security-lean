import Signatures.Runtime.SchnorrSeededMachineRefinement
import Signatures.Runtime.SchnorrSeededMachineBudget
import Signatures.Runtime.SchnorrReduction
import Signatures.Runtime.SchnorrSeededSecurity

/-! The executable controller implements the named source-derived reduction
used by the fixed-private-tape Schnorr security theorem. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.SeedTape

variable {F : Type} [Field F] [SampleableType F] [DecidableEq F]

omit [Field F] [DecidableEq F] in
theorem support_samples {A : Type} (main : OracleComp (replaySpec F) A) :
    support (simulateQ samples main) = support main := by
  induction main using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, support_bind, ih]
      rcases i with (n | ⟨⟩) | ⟨⟩ <;> simp [samples]

omit [Field F] in
theorem seededFork_map {A B : Type} (main : OracleComp (replaySpec F) A) (f : A → B)
    (capacity : Family → Nat) (families : List Family)
    (cf : B → Option (Fin (capacity (.inr ()) + 1))) :
    seededFork (f <$> main) capacity families (.inr ()) cf =
      Option.map (Prod.map f f) <$> seededFork main capacity families (.inr ()) (cf ∘ f) := by
  unfold seededFork
  simp only [simulateQ_map, StateT.run'_map', bind_map_left, map_bind, Function.comp_def]
  congr 1
  funext seed
  congr 1
  funext first
  cases cf (f first) with
  | none => simp
  | some index =>
      dsimp only
      simp only [map_bind]
      congr 1
      funext fresh
      split
      · simp
      · simp only [map_bind]
        congr 1
        funext second
        split <;> simp

omit [Field F] in
theorem seededFork_outputs {A : Type} (main : OracleComp (replaySpec F) A)
    (capacity : Family → Nat) (families : List Family)
    (cf : A → Option (Fin (capacity (.inr ()) + 1))) (first second : A)
    (h : some (first, second) ∈ support (seededFork main capacity families (.inr ()) cf)) :
    first ∈ support main ∧ second ∈ support main := by
  unfold seededFork at h
  simp only [mem_support_bind_iff] at h
  obtain ⟨seed, _, a, ha, h⟩ := h
  cases hcf : cf a with
  | none => simp only [hcf, support_pure, Set.mem_singleton_iff, reduceCtorEq] at h
  | some index =>
      simp only [hcf, mem_support_bind_iff] at h
      obtain ⟨fresh, _, h⟩ := h
      split at h
      · simp at h
      · simp only [mem_support_bind_iff] at h
        obtain ⟨b, hb, h⟩ := h
        split at h
        · simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨support_simulateQ_run'_subset seededOracle main seed ha,
            support_simulateQ_run'_subset seededOracle main _ hb⟩
        · simp at h

variable {G₁ G₂ K M : Type}
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁] [SampleableType G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

/-- Erasure equals the same named reduction whose success is already bounded
by `Seeded.security`; the equality is derived from the controller's code. -/
theorem sourceForkCode_reduction [Fintype F] (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {dataTy} (qH randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery)
    (localTime : Nat) (queries : Fin 3 → Nat)
    (pk g : G₁) (data : dataTy.Value (cryptoBase F G₁ G₂ K M)) :
    Run.value <$> (sourceForkCode qH randomBound source localTime queries).run
      cost sampling (pk, g, data, ()) =
      Seeded.reduction cost randomBound source (pk, data, ()) g pk localTime queries qH := by
  rw [sourceForkCode_seeded]
  unfold Seeded.reduction Seeded.fork Seeded.main
  rw [simulateQ_bind, ← samples_expand, seededFork_map]
  have hselect : (Option.map (Fin.castLE (Nat.succ_le_succ (Seeded.target_le source localTime queries qH))) ∘
      FiatShamir.Fork.forkPoint G₁ F F M qH) ∘ cacheTrace (G₂ := G₂) (K := K) =
      Option.map (Fin.castLE (Nat.succ_le_succ (Seeded.target_le source localTime queries qH))) ∘
        selectPass cost qH := by
    funext p
    simp only [Function.comp_def, selectPass_trace]
  rw [hselect, simulateQ_map, bind_map_left]
  have hsample : (Seeded.sampleChallenges : QueryImpl (expandedSpec F) ProbComp) = sampleExpanded := by
    funext i
    cases i with
    | inl n => rfl
    | inr u => cases u; rfl
  rw [hsample]
  apply bind_congr_of_forall_mem_support
  intro result hr
  cases result with
  | none =>
      simp only [Option.map_none, extractFork, FiatShamir.nmaForkExtractBranch]
      rw [← liftRandom_eq_liftComp, sampleExpanded_liftRandom]
  | some pair =>
      rw [support_samples] at hr
      obtain ⟨hfirst, hsecond⟩ := seededFork_outputs _ _ _ _ pair.1 pair.2 hr
      have hf := macroPass_valid cost randomBound source (pk, data, ()) g pk [] [] pair.1
        (by simpa only [support_expandPrivate] using hfirst)
      have hs := macroPass_valid cost randomBound source (pk, data, ()) g pk [] [] pair.2
        (by simpa only [support_expandPrivate] using hsecond)
      have he := congrArg (simulateQ (sampleExpanded (F := F)))
        (extractFork_trace g pair.1 pair.2 hf.2 hs.2)
      rw [sampleExpanded_liftRandom] at he
      exact he

/-- The fixed-tape reduction belongs to the same closed-machine runtime class
as other certified DLog solvers. The source certificate supplies its only budget premise. -/
theorem source_within [Fintype F] {cost : PrimitiveCosts} (sampling : Machine.SamplingCosts)
    {randomBound localTime : Nat} {queries : Fin 3 → Nat} (g : G₁)
    {adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g}
    (cert : SourceCertificate (G₂ := G₂) (K := K) cost randomBound localTime queries adv.main)
    (qH : Nat) :
    dlogWithin (G₂ := G₂) (K := K) (M := M) cost sampling g
      (packagePrice cost sampling qH randomBound cert.code localTime queries g cert.data)
      (Seeded.dlogReduction cost randomBound localTime queries g adv cert qH) := by
  refine ⟨forkPackage qH randomBound cert.code localTime queries g cert.data, ?_, ?_⟩
  · rintro ⟨pk, _⟩
    rw [Machine.Package.run_eq]
    simpa only [Functor.map_map, forkPackage, Env.append, Seeded.dlogReduction, Seeded.sourceReduction] using
      sourceForkCode_reduction cost sampling qH randomBound cert.code localTime queries pk g cert.data
  · rintro ⟨pk, _⟩ out hout
    exact forkPackage_bound cost sampling qH randomBound cert.code pk g cert.data
      localTime queries (cert.budget pk) out hout

/-- Source-certified fixed-tape Schnorr security against a concrete arithmetic
budget. The hardness premise ranges over all closed-machine solvers within it. -/
theorem security [Fintype F] (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound localTime : Nat) (queries : Fin 3 → Nat)
    (g : G₁) (hgen : Function.Bijective (fun x : F => x • g))
    (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g)
    (cert : SourceCertificate (G₂ := G₂) (K := K) cost randomBound localTime queries adv.main)
    (qS qH : Nat)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound (M := M) (oa := adv.main pk) qS qH)
    (epsilon : ENNReal)
    (hardness : ∀ solver : DiffieHellman.DLogAdversary F G₁,
      dlogWithin (G₂ := G₂) (K := K) (M := M) cost sampling g
        (packagePrice cost sampling qH randomBound cert.code localTime queries g cert.data) solver →
      𝒟[DiffieHellman.dlogExperiment g solver] {true} ≤ epsilon) :
    let eps := 𝒟[_root_.Schnorr.ROM.game g adv] {true} -
      (qS : ENNReal) * (qS + qH) * (Fintype.card F : ENNReal)⁻¹
    eps * (eps / (qH + 1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤ epsilon := by
  exact (Seeded.security cost randomBound localTime queries g hgen adv cert qS qH hQ).trans
    (hardness _ (source_within sampling g cert qH))

end Signatures.Runtime.Schnorr.SeedTape
