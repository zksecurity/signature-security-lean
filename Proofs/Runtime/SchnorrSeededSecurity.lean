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
noncomputable local instance : OracleSpec.UniformAnswerMeasure (Unit →ₒ F) :=
  UniformAnswerMeasure.ofFiniteNonempty _

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
    (∑ s, Pr{let x ← (FiatShamir.Fork.forkPoint G₁ F F M qH <$>
      main cost randomBound cert.code (pk, cert.data, ()) g pk)}[x = some s]) =
    Pr{let x ← _root_.Schnorr.FixedTape.main g pk adv}[(FiatShamir.Fork.forkPoint G₁ F F M qH x).isSome] := by
  have he := cert.trace cost randomBound localTime queries g adv pk
  rw [← simulateQ_map] at he
  unfold _root_.Schnorr.FixedTape.main
  rw [← he, probEvent_expandPrivate]
  simp only [prEvent_isSome_eq_sum, prEvent_map]

theorem hardRelation_bound (cost : PrimitiveCosts) (randomBound localTime : Nat)
    (queries : Fin 3 → Nat) (g : G₁) (adv : _root_.Schnorr.ROM.Adversary (F := F) (M := M) g)
    (cert : SourceCertificate (G₂ := G₂) (K := K) cost randomBound localTime queries adv.main)
    (qH : Nat) :
    let a := FiatShamir.Fork.advantage (_root_.Schnorr.sigma F G₁ g) (dlogGenerable F g) M
      (FiatShamir.cmaToNmaAdv (_root_.Schnorr.sigma F G₁ g) (dlogGenerable F g) M
        (_root_.Schnorr.simTranscript F G₁ g) adv) qH
    a * (a / (qH + 1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      Pr{let x ← (hardRelationExperiment (dlogGenerable F g)
        (sourceReduction cost randomBound localTime queries g adv cert qH))}[x = true] := by
  classical
  dsimp only
  let : MeasurableSpace (G₁ × F) := ⊤
  let acc : G₁ → ENNReal := fun pk =>
    Pr{let x ← _root_.Schnorr.FixedTape.main g pk adv}[(FiatShamir.Fork.forkPoint G₁ F F M qH x).isSome]
  let B : G₁ × F → ENNReal := fun pkw =>
    Pr{let w ← sourceReduction cost randomBound localTime queries g adv cert qH pkw.1}[decide (w • g = pkw.1) = true]
  have hAdv : FiatShamir.Fork.advantage (_root_.Schnorr.sigma F G₁ g) (dlogGenerable F g) M
      (FiatShamir.cmaToNmaAdv (_root_.Schnorr.sigma F G₁ g) (dlogGenerable F g) M
        (_root_.Schnorr.simTranscript F G₁ g) adv) qH =
      ∫⁻ pkw, acc pkw.1 ∂𝒟[(dlogGenerable F g).gen] := by
    rw [FiatShamir.Fork.advantage, FiatShamir.Fork.experiment,
      (FiatShamir.Fork.simulateQ_uniformImpl_evalDistEq _).prEvent_eq,
      prEvent_bind_eq_lintegral_of_discrete, OracleComp.evalDist_liftComp_uniform]
    refine MeasureTheory.lintegral_congr fun pkw => ?_
    rcases pkw with ⟨pk, w⟩
    simp only [acc, prEvent_norm]
  have hReduction : Pr{let x ← (hardRelationExperiment (dlogGenerable F g)
        (sourceReduction cost randomBound localTime queries g adv cert qH))}[x = true] =
      ∫⁻ pkw, B pkw ∂𝒟[(dlogGenerable F g).gen] := by
    rw [hardRelationExperiment, prEvent_bind_eq_lintegral_of_discrete]
    refine MeasureTheory.lintegral_congr fun pkw => ?_
    rcases pkw with ⟨pk, w⟩
    simp only [B, prEvent_norm]
  have hPointwise : ∀ pk, acc pk * (acc pk / (qH + 1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      Pr{let w ← sourceReduction cost randomBound localTime queries g adv cert qH pk}[decide (w • g = pk) = true] := by
    intro pk
    simpa only [source_acceptance_eq, acc, sourceReduction] using
      pointwise_extraction_bound cost randomBound localTime queries g adv cert pk qH
  rw [hAdv, hReduction]
  exact OracleComp.EvalDist.marginalized_jensen_forking_bound_of_discrete (dlogGenerable F g).gen
    (fun pkw => acc pkw.1) B _ _ (fun _ => prEvent_le_one _) (fun pkw => hPointwise pkw.1)

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
    0 ((ChallengeVerifyProtocol.perfectHVZK_iff_hvzk_zero _ _).mp
      (_root_.Schnorr.sigma_hvzk F G₁ g)) ((Fintype.card F : ENNReal)⁻¹)
    (_root_.Schnorr.sigma_simCommitPredictability F G₁ g hgen) adv qS qH hQ
  simp only [mul_zero, ENNReal.ofReal_zero, add_zero] at hAdv
  have hbound := hardRelation_bound cost randomBound localTime queries g adv cert qH
  have heq : Pr{let x ← (hardRelationExperiment (dlogGenerable F g)
      (sourceReduction cost randomBound localTime queries g adv cert qH))}[x = true] =
      Pr{let x ← dlogExperiment g (dlogReduction cost randomBound localTime queries g adv cert qH)}[x = true] := by
    rw [show Pr{let x ← (hardRelationExperiment (dlogGenerable F g)
        (sourceReduction cost randomBound localTime queries g adv cert qH))}[x = true] =
      Pr{let y ← (do
        let x ← $ᵗ F
        let w ← sourceReduction cost randomBound localTime queries g adv cert qH (x • g)
        pure (decide (w • g = x • g)))}[y = true] by
      simp [hardRelationExperiment, dlogGenerable]]
    simp [dlogExperiment, dlogReduction, prEvent_norm, hgen.1.eq_iff]
  rw [heq] at hbound
  rw [_root_.Schnorr.ROM.game_eq_advantage]
  simp only [← prEvent_eq_evalDist_singleton]
  refine le_trans ?_ hbound
  gcongr <;> exact tsub_le_iff_right.mpr (by
    simpa only [_root_.Schnorr.signature, FiatShamir.inROM] using hAdv)

end Signatures.Runtime.Schnorr.Seeded
