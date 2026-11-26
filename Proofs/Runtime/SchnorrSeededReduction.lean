import Proofs.Runtime.SchnorrSeededFork

/-! Extraction for the source-derived fixed-tape fork. Scalar sampling is
expanded after constructing the typed fork, preserving its private tape. -/

open OracleComp OracleSpec DiffieHellman

namespace Signatures.Runtime.Schnorr.Seeded

section Sampling

variable {F A : Type} [SampleableType F] [Fintype F] [Inhabited F]

noncomputable local instance : OracleSpec.UniformAnswerMeasure (Unit →ₒ F) :=
  UniformAnswerMeasure.ofFiniteNonempty _

/-- A uniform query returns a fixed answer with probability `1 / |Range|`. -/
private theorem prEvent_liftM_query_eq_singleton {ι : Type} {spec : OracleSpec ι}
    [UniformAnswerMeasure spec] (t : spec.Domain) [Fintype (spec.Range t)] (u : spec.Range t) :
    Pr{let x ← (liftM (OracleSpec.query t) : OracleComp spec (spec.Range t))}[x = u] =
      (Fintype.card (spec.Range t) : ENNReal)⁻¹ := by
  classical
  rw [prEvent_liftM_query_eq_card_div t (· = u)]
  have hcard : (Finset.univ.filter (· = u)).card = 1 :=
    Finset.card_eq_one.mpr ⟨u, by ext; simp⟩
  rw [hcard, Nat.cast_one, one_div]

private theorem probOutput_liftRandom (main : ProbComp A) (out : A) :
    Pr{let x ← liftRandom (F := F) main}[x = out] = Pr{let x ← main}[x = out] := by
  classical
  induction main using OracleComp.inductionOn with
  | pure x => simp [liftRandom]
  | query_bind n next ih =>
      simp only [liftRandom] at ih ⊢
      simp only [simulateQ_bind, simulateQ_spec_query, OracleComp.prEvent_bind_eq_tsum, ih]
      apply tsum_congr
      intro u
      congr 1

theorem probEvent_expandPrivate (main : OracleComp (replaySpec F) A) (p : A → Prop) :
    Pr{let x ← simulateQ (Replay.expandPrivate privateImpl) main}[p x] = Pr{let x ← main}[p x] := by
  classical
  induction main using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OracleComp.prEvent_bind_eq_tsum, ih]
      apply tsum_congr
      intro u
      congr 1
      cases i with
      | inl i =>
          cases i with
          | inl n =>
              simp only [Replay.expandPrivate, privateImpl]
              exact (prEvent_liftM_query_eq_singleton (spec := expandedSpec F) (.inl n) u).trans
                (prEvent_liftM_query_eq_singleton (spec := replaySpec F) (.inl (.inl n)) u).symm
          | inr t =>
              cases t
              rw [Replay.expandPrivate, privateImpl, probOutput_liftRandom]
              exact (SampleableType.prEvent_uniformSample_eq_singleton (α := F) u).trans
                (prEvent_liftM_query_eq_singleton (spec := replaySpec F) (.inl (.inr ())) u).symm
      | inr t =>
          cases t
          simp only [Replay.expandPrivate]
          exact (prEvent_liftM_query_eq_singleton (spec := expandedSpec F) (.inr ()) u).trans
            (prEvent_liftM_query_eq_singleton (spec := replaySpec F) (.inr ()) u).symm

def sampleChallenges : QueryImpl (expandedSpec F) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp + uniformSampleImpl (spec := Unit →ₒ F)

theorem probEvent_sampleChallenges (main : OracleComp (expandedSpec F) A) (p : A → Prop) :
    Pr{let x ← simulateQ sampleChallenges main}[p x] = Pr{let x ← main}[p x] := by
  classical
  induction main using OracleComp.inductionOn with
  | pure x => simp
  | query_bind i next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OracleComp.prEvent_bind_eq_tsum, ih]
      apply tsum_congr
      intro u
      congr 1
      cases i with
      | inl n =>
          simp only [sampleChallenges, QueryImpl.add_apply_inl, QueryImpl.ofLift_eq_id',
            QueryImpl.id'_apply]
          exact (prEvent_liftM_query_eq_singleton (spec := unifSpec) n u).trans
            (prEvent_liftM_query_eq_singleton (spec := expandedSpec F) (.inl n) u).symm
      | inr t =>
          simp only [sampleChallenges, QueryImpl.add_apply_inr, uniformSampleImpl_apply]
          exact (SampleableType.prEvent_uniformSample_eq_singleton u).trans
            (prEvent_liftM_query_eq_singleton (spec := expandedSpec F) (.inr t) u).symm

end Sampling

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [Fintype F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁] [SampleableType G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

local instance : Inhabited F := ⟨0⟩
noncomputable local instance : OracleSpec.UniformAnswerMeasure (Unit →ₒ F) :=
  UniformAnswerMeasure.ofFiniteNonempty _

/-- A named witness finder from the actual source program. -/
def reduction (cost : PrimitiveCosts) {Γ} (randomBound : Nat)
    (code : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (g pk : G₁)
    (localTime : Nat) (queries : Fin 3 → Nat) (qH : Nat) : ProbComp F :=
  simulateQ sampleChallenges (do
    let pair ← simulateQ (Replay.expandPrivate privateImpl)
      (fork cost randomBound code env g pk localTime queries qH)
    FiatShamir.nmaForkExtractBranch (M := M) (_root_.Schnorr.sigma F G₁ g) pair)

theorem source_fork_support_native (cost : PrimitiveCosts) (randomBound localTime : Nat)
    (queries : Fin 3 → Nat) (g : G₁) (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g)
    (cert : SourceCertificate (G₂ := G₂) (K := K) cost randomBound localTime queries adv.main)
    (pk : G₁) (qH : Nat) {x₁ x₂ : FiatShamir.Fork.Trace G₁ F F M}
    (h : some (x₁, x₂) ∈ support (fork cost randomBound cert.code (pk, cert.data, ())
      g pk localTime queries qH)) :
    some (x₁, x₂) ∈ support (contextFork
      (FiatShamir.Fork.runTrace (_root_.Schnorr.sigma F G₁ g) (dlogGenerable F g) M
        (FiatShamir.cmaToNmaAdv (_root_.Schnorr.sigma F G₁ g) (dlogGenerable F g) M
          (_root_.Schnorr.simTranscript F G₁ g) adv) pk)
      (FiatShamir.nmaForkBudget qH) (.inr ()) (FiatShamir.Fork.forkPoint G₁ F F M qH)) := by
  have hctx := fork_support_context cost randomBound cert.code (pk, cert.data, ())
    g pk localTime queries qH (cert.budget pk) h
  have he := cert.trace cost randomBound localTime queries g adv pk
  rw [← simulateQ_map] at he
  rw [← he]
  change some (x₁, x₂) ∈ support (contextFork
    (simulateQ (Replay.expandPrivate privateImpl)
      (main cost randomBound cert.code (pk, cert.data, ()) g pk))
    (fun _ => qH) (Sum.inr ()) (FiatShamir.Fork.forkPoint G₁ F F M qH))
  rw [← expand_contextFork, support_expandPrivate]
  exact hctx

/-- Every accepted source fork yields a discrete-log witness under the
established special-soundness theorem. -/
theorem pointwise_extraction_bound (cost : PrimitiveCosts) (randomBound localTime : Nat)
    (queries : Fin 3 → Nat) (g : G₁) (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g)
    (cert : SourceCertificate (G₂ := G₂) (K := K) cost randomBound localTime queries adv.main)
    (pk : G₁) (qH : Nat) :
    let acc : ENNReal := ∑ s, Pr{let x ← (FiatShamir.Fork.forkPoint G₁ F F M qH <$>
      main cost randomBound cert.code (pk, cert.data, ()) g pk)}[x = some s]
    acc * (acc / (qH + 1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      Pr{let w ← reduction cost randomBound cert.code (pk, cert.data, ()) g pk localTime queries qH}[decide (w • g = pk) = true] := by
  classical
  refine (fork_success_bound cost randomBound cert.code (pk, cert.data, ())
    g pk localTime queries qH).trans ?_
  rw [reduction, probEvent_sampleChallenges, OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun pair => ?_
  have hexp : Pr{let x ← (simulateQ (Replay.expandPrivate privateImpl)
      (fork cost randomBound cert.code (pk, cert.data, ()) g pk localTime queries qH))}[x = pair] =
      Pr{let x ← fork cost randomBound cert.code (pk, cert.data, ()) g pk localTime queries qH}[x = pair] := by
    exact probEvent_expandPrivate
      (fork cost randomBound cert.code (pk, cert.data, ()) g pk localTime queries qH) (· = pair)
  rw [hexp]
  cases pair with
  | none => simp
  | some pair =>
      simp only [Option.isSome, ite_true]
      by_cases hsupp : some pair ∈ support (fork cost randomBound cert.code (pk, cert.data, ())
          g pk localTime queries qH)
      · have hctx := source_fork_support_native cost randomBound localTime queries g adv cert pk qH hsupp
        have hbranch := FiatShamir.FixedTape.branch_success_of_context
          (_root_.Schnorr.sigma F G₁ g) (dlogGenerable F g) M
          (FiatShamir.cmaToNmaAdv (_root_.Schnorr.sigma F G₁ g) (dlogGenerable F g) M
            (_root_.Schnorr.simTranscript F G₁ g) adv) qH
          (_root_.Schnorr.sigma_speciallySound F G₁ g) pk hctx
        rw [hbranch, mul_one]
      · rw [(prEvent_eq_zero_of_not_mem_support _) hsupp, zero_mul]

end Signatures.Runtime.Schnorr.Seeded
