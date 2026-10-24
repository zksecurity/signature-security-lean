import Proofs.Schnorr.ROM
import Proofs.Runtime.SchnorrReduction
import Proofs.Model.Hardness

/-! Arithmetic-source Schnorr EUF-CMA security in the programmable ROM, with a
complete replay-machine certificate. No AGM restriction or constant-cost
continuation snapshot is assumed. General-caller ROM replay is separate work. -/

open OracleComp DiffieHellman
open Signatures.Runtime Signatures.Runtime.Schnorr
open scoped ENNReal

namespace Schnorr.Statement

variable {F G M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G] [DecidableEq M]

/-- The corrected EUF-CMA success feeds the Pointcheval-Stern fork bound. The machine
budget pays for both passes, retained randomness, cache/tape scans, and extraction.
Arithmetic and sampling prices are contracts, not proved bit-operation costs. -/
theorem schnorr_eufcma_of_dlog_machine_hardness
    -- The scalar action on the fixed generator parametrizes the group bijectively.
    (g : G) (hgen : Function.Bijective (fun x : F => x • g))
    {adv : Schnorr.ROM.Adversary (F := F) (M := M) g}
    -- Signing and hash-call bounds hold on every adaptive reply path at every key.
    (qS qH : Nat)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound (M := M) (oa := adv.main pk) qS qH)
    {cost : PrimitiveCosts} (sampling : Machine.SamplingCosts)
    -- The independent source budget counts random, hash, and signing calls (0, 1, 2).
    {randomBound localTime : Nat} {queries : Fin 3 → Nat}
    -- Only the original adversary supplies executable code and all-path resource evidence.
    (cert : SourceCertificate (G₂ := G) (K := M) cost randomBound localTime queries adv.main)
    (epsilon : ENNReal)
    -- Hardness ranges over all closed machine implementations within the derived budget.
    (hhard : Model.HardWithin
      (fun solver : DLogAdversary F G => 𝒟[dlogExperiment g solver] {true})
      (dlogWithin (G₂ := G) (K := M) (M := M) cost sampling g)
      (cert.targetBudget sampling qH) epsilon) :
    -- Signing simulation can lose qS*(qS+qH)/|F|; subtraction truncates at zero.
    let eps := 𝒟[Schnorr.ROM.game g adv] {true} -
      (qS : ENNReal) * (qS + qH) * (Nat.card F : ENNReal)⁻¹
    -- The extra hash slot is the final verification query; a repeated challenge costs 1/|F|.
    eps * (eps / (qH + 1 : ENNReal) - (Nat.card F : ENNReal)⁻¹) ≤ epsilon := by
  let : Fintype F := Fintype.ofFinite F
  simpa only [Nat.card_eq_fintype_card] using (Schnorr.ROM.Proofs.security g hgen adv qS qH hQ).trans
    (hhard _ (cert.within sampling g qH))

end Schnorr.Statement
