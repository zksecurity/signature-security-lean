import Proofs.Runtime.SchnorrSeededReduction
import Proofs.Schnorr.FixedTapeROM

/-! Native EUF-CMA probability bound for the fixed-tape source reduction. Seed
coverage is derived from the source certificate; no bound on the finished
reduction is a premise. Machine-time certification is a separate obligation. -/

open OracleComp OracleSpec DiffieHellman

namespace Signatures.Runtime.Schnorr.Seeded

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [Fintype F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁] [SampleableType G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

local instance : Inhabited F := ⟨0⟩
noncomputable local instance : IsUniformSpec (Unit →ₒ F) :=
  IsUniformSpec.ofFintypeInhabited _

def sourceReduction (cost : PrimitiveCosts) (randomBound localTime : Nat)
    (queries : Fin 3 → Nat) (g : G₁) (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g)
    (cert : SourceCertificate (G₂ := G₂) (K := K) cost randomBound localTime queries adv.main)
    (qH : Nat) : G₁ → ProbComp F := fun pk =>
  reduction cost randomBound cert.code (pk, cert.data, ()) g pk localTime queries qH

def dlogReduction (cost : PrimitiveCosts) (randomBound localTime : Nat)
    (queries : Fin 3 → Nat) (g : G₁) (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g)
    (cert : SourceCertificate (G₂ := G₂) (K := K) cost randomBound localTime queries adv.main)
    (qH : Nat) : DLogAdversary F G₁ := fun _ pk =>
  sourceReduction cost randomBound localTime queries g adv cert qH pk

private theorem source_acceptance_eq (cost : PrimitiveCosts) (randomBound localTime : Nat)
    (queries : Fin 3 → Nat) (g : G₁) (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g)
    (cert : SourceCertificate (G₂ := G₂) (K := K) cost randomBound localTime queries adv.main)
    (pk : G₁) (qH : Nat) :
    (∑ s, Pr[= some s | FiatShamir.Fork.forkPoint G₁ F F M qH <$>
      main cost randomBound cert.code (pk, cert.data, ()) g pk]) =
    Pr[fun x => (FiatShamir.Fork.forkPoint G₁ F F M qH x).isSome |
      _root_.Schnorr.FixedTape.main g pk adv] := by
  have he := cert.trace cost randomBound localTime queries g adv pk
  rw [← simulateQ_map] at he
  unfold _root_.Schnorr.FixedTape.main
  rw [← he, probEvent_expandPrivate]
  simpa only [probEvent_isSome_eq_tsum_probOutput_some, tsum_fintype, Function.comp_def] using
    (probEvent_map (main cost randomBound cert.code (pk, cert.data, ()) g pk)
      (FiatShamir.Fork.forkPoint G₁ F F M qH) (fun r => r.isSome))

theorem hardRelation_bound (cost : PrimitiveCosts) (randomBound localTime : Nat)
    (queries : Fin 3 → Nat) (g : G₁) (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g)
    (cert : SourceCertificate (G₂ := G₂) (K := K) cost randomBound localTime queries adv.main)
    (qH : Nat) :
    let a := FiatShamir.Fork.advantage (_root_.Schnorr.sigma F G₁ g) (dlogGenerable F g) M
      (FiatShamir.cmaToNmaAdv (_root_.Schnorr.sigma F G₁ g) (dlogGenerable F g) M
        (_root_.Schnorr.simTranscript F G₁ g) adv) qH
    a * (a / (qH + 1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      Pr[= true | hardRelationExperiment (dlogGenerable F g)
        (sourceReduction cost randomBound localTime queries g adv cert qH)] := by
  classical
  dsimp only
  let acc : G₁ → ENNReal := fun pk =>
    Pr[fun x => (FiatShamir.Fork.forkPoint G₁ F F M qH x).isSome |
      _root_.Schnorr.FixedTape.main g pk adv]
  have hsample (mx : OracleComp (expandedSpec F) Bool) (p : Bool → Prop) :
      Pr[p | simulateQ (QueryImpl.ofLift unifSpec ProbComp +
        uniformSampleImpl (spec := Unit →ₒ F)) mx] = Pr[p | mx] :=
    probEvent_sampleChallenges mx p
  have hAdv : FiatShamir.Fork.advantage (_root_.Schnorr.sigma F G₁ g) (dlogGenerable F g) M
      (FiatShamir.cmaToNmaAdv (_root_.Schnorr.sigma F G₁ g) (dlogGenerable F g) M
        (_root_.Schnorr.simTranscript F G₁ g) adv) qH =
      ∑' pkw : G₁ × F, Pr[= pkw | (dlogGenerable F g).gen] * acc pkw.1 := by
    simp only [FiatShamir.Fork.advantage, FiatShamir.Fork.experiment,
      ← probEvent_eq_eq_probOutput, hsample,
      probEvent_bind_eq_tsum, bind_pure_comp, probEvent_map, Function.comp_def,
      probEvent_liftComp, acc]
  have hReduction : Pr[= true | hardRelationExperiment (dlogGenerable F g)
        (sourceReduction cost randomBound localTime queries g adv cert qH)] =
      ∑' pkw : G₁ × F, Pr[= pkw | (dlogGenerable F g).gen] *
        Pr[fun w => decide (w • g = pkw.1) = true |
          sourceReduction cost randomBound localTime queries g adv cert qH pkw.1] := by
    simp only [hardRelationExperiment, ← probEvent_eq_eq_probOutput, bind_pure_comp,
      probEvent_bind_eq_tsum, probEvent_map, Function.comp_def]
  have hPointwise : ∀ pk, acc pk * (acc pk / (qH + 1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      Pr[fun w => decide (w • g = pk) = true |
        sourceReduction cost randomBound localTime queries g adv cert qH pk] := by
    intro pk
    simpa only [source_acceptance_eq, acc, sourceReduction] using
      pointwise_extraction_bound cost randomBound localTime queries g adv cert pk qH
  rw [hAdv, hReduction]
  simpa only [DiscreteEvalDistCompatible.lintegral_evalDist _ (g := fun a => a) measurable_id,
    ← OracleComp.EvalDist.expectedValue_def, OracleComp.EvalDist.expectedValue_map] using
    OracleComp.EvalDist.marginalized_jensen_forking_bound_map (mx := (dlogGenerable F g).gen)
      (acc := fun pkw => acc pkw.1)
      (B := fun pkw => Pr[fun w => decide (w • g = pkw.1) = true |
        sourceReduction cost randomBound localTime queries g adv cert qH pkw.1])
      (q := (qH : ENNReal) + 1) (hinv := (Fintype.card F : ENNReal)⁻¹)
      (fun _ => probEvent_le_one) (fun pkw => hPointwise pkw.1)

/-- The complete source-certified probability endpoint. Both runs share every
private draw; only the selected hash answer and its hash suffix are resampled. -/
theorem security (cost : PrimitiveCosts) (randomBound localTime : Nat)
    (queries : Fin 3 → Nat) (g : G₁) (hgen : Function.Bijective (fun x : F => x • g))
    (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g)
    (cert : SourceCertificate (G₂ := G₂) (K := K) cost randomBound localTime queries adv.main)
    (qS qH : Nat)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound (M := M) (oa := adv.main pk) qS qH) :
    let eps := 𝒟[_root_.Schnorr.ROM.game g adv] {true} -
      (qS : ENNReal) * (qS + qH) * (Fintype.card F : ENNReal)⁻¹
    eps * (eps / (qH + 1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      𝒟[dlogExperiment g (dlogReduction cost randomBound localTime queries g adv cert qH)] {true} := by
  haveI : Finite G₁ := Finite.of_surjective (fun x : F => x • g) hgen.2
  have hAdv := FiatShamir.cma_to_nma_advantage_bound
    (_root_.Schnorr.sigma F G₁ g) (dlogGenerable F g) M (_root_.Schnorr.simTranscript F G₁ g)
    0 le_rfl ((ChallengeVerifyProtocol.perfectHVZK_iff_hvzk_zero _ _).mp
      (_root_.Schnorr.sigma_hvzk F G₁ g)) ((Fintype.card F : ENNReal)⁻¹)
    (_root_.Schnorr.sigma_simCommitPredictability F G₁ g hgen) adv qS qH hQ
  simp only [mul_zero, ENNReal.ofReal_zero, add_zero] at hAdv
  have hbound := hardRelation_bound cost randomBound localTime queries g adv cert qH
  have heq : Pr[= true | hardRelationExperiment (dlogGenerable F g)
      (sourceReduction cost randomBound localTime queries g adv cert qH)] =
      Pr[= true | dlogExperiment g (dlogReduction cost randomBound localTime queries g adv cert qH)] := by
    simp only [hardRelationExperiment, dlogGenerable, dlogExperiment,
      dlogReduction, bind_pure_comp, bind_map_left]
    apply probOutput_bind_congr' _ true
    intro x
    simp [hgen.1.eq_iff]
  rw [heq] at hbound
  rw [_root_.Schnorr.ROM.game_eq_advantage]
  simp only [evalDist_apply_singleton]
  refine le_trans ?_ hbound
  gcongr <;> exact tsub_le_iff_right.mpr (by
    simpa only [_root_.Schnorr.signature, FiatShamir.inROM] using hAdv)

end Signatures.Runtime.Schnorr.Seeded
