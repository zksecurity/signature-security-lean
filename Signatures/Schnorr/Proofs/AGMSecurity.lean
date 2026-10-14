import Signatures.Schnorr.Proofs.AGMSigningSimulation
import Signatures.Schnorr.Proofs.AGMSourceGame
import VCVio.OracleComp.Constructions.SampleableType.MeasureCompatibility

/-! Adaptive, single-pass Schnorr security in the algebraic group model.
The theorem concerns the original source game, including malformed requests,
shared lazy hashes, signing history, and final verification. -/

open OracleComp OracleSpec AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Schnorr.AGM

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F] [Fintype F]

/-- Honest instrumentation preserves the entire Boolean output distribution. -/
theorem honestGame_dist (g : G) (A : Adversary F G M) :
    𝒟[Reduction.honestGame g A] = 𝒟[game g A] := by
  exact evalDist_eq_of_evalSPMF_eq _ _ (Reduction.honestGame_eq g A)

/-- The actual single-pass solver loses at most the signing-collision term and
one inverse-field-size term per adversarial hash or final verification query.
Both request caps hold on every adaptive reply path and for every public key. -/
theorem security (g : G) (hg : Function.Injective (fun x : F => x • g))
    (A : Adversary F G M) (qS qH : Nat)
    (hS : ∀ pk, IsQueryBoundP (A.main (initial g pk))
      (fun q => Reduction.signRequest q = true) qS)
    (hH : ∀ pk, IsQueryBoundP (A.main (initial g pk))
      (fun q => Reduction.hashRequest q = true) qH) :
    𝒟[game g A] {true} ≤
      𝒟[DiffieHellman.dlogExperiment g (Reduction.dlogReduction g A)] {true} +
        (qH + 1 : ENNReal) * (Fintype.card F : ENNReal)⁻¹ +
        (qS : ENNReal) * (qS + qH) * (Fintype.card F : ENNReal)⁻¹ := by
  rw [← honestGame_dist]
  exact Reduction.honest_security g hg A qS qH hS hH

end Schnorr.AGM
