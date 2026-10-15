import Signatures.Runtime.SchnorrAGMGrowth
import Signatures.Schnorr.Proofs.AGMSecurity

/-! Preserve the original Schnorr AGM probability bound with the finite-store
solver. This is a semantic/probability endpoint; a complete native resource
certificate is still required before using a time-bounded DLog assumption. -/

open OracleComp OracleSpec AlgebraicGroupModel.Interaction Schnorr.AGM
open scoped ENNReal

namespace Signatures.Runtime.SchnorrAGM

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]

/-- Algebraicity and cache validity survive every finite-store adaptive path. -/
theorem simulate_valid (g pk : G)
    (program : OracleComp (explainedSpec F (Group G) (Request M) (Reply F M))
      (Explained F (M × F) (Group G)))
    (s : State F G M) (hs : (erase s).Valid g pk)
    (halg : IsAlgebraic (representedBasis g pk s.representations) program)
    (out : Explained F (M × F) (Group G)) (t : State F G M)
    (h : (out, t) ∈ support ((simulateQ (handler g pk) program).run s)) :
    (erase t).Valid g pk ∧ out.Valid (representedBasis g pk t.representations) := by
  have hsource : (out, erase t) ∈ support ((simulateQ (Reduction.handler g pk) program).run (erase s)) := by
    rw [← simulate_erase g pk program s, support_map]
    exact ⟨(out, t), h, rfl⟩
  exact Reduction.simulate_valid g pk program (erase s) hs halg out (erase t) hsource

/-- On every accepting nonbad path, the finite-store extractor returns the secret. -/
theorem run_extract (g : G) (hg : Function.Injective (fun x : F => x • g))
    (x : F) (adv : Adversary F G M) (p : (Bool × F) × State F G M)
    (h : p ∈ support (run g (x • g) adv))
    (hwin : p.1.1 = true) (hbad : p.2.bad = false) : p.1.2 = x := by
  apply Reduction.run_extract g hg x adv p.1 (erase p.2) _ hwin hbad
  rw [← run_erase g (x • g) adv, support_map]
  exact ⟨p, h, rfl⟩

/-- The source solver fixes `g`, whereas the finite-store solver uses its input
generator. Their complete DLog experiments agree at the specified generator. -/
theorem dlogExperiment_eq (g : G) (adv : Adversary F G M) :
    DiffieHellman.dlogExperiment g (dlogReduction adv) =
      DiffieHellman.dlogExperiment g (Reduction.dlogReduction g adv) := by
  simp only [DiffieHellman.dlogExperiment, dlogReduction_eq]

theorem security [Fintype F] (g : G) (hg : Function.Injective (fun x : F => x • g))
    (adv : Adversary F G M) (qS qH : Nat)
    (hS : ∀ pk, IsQueryBoundP (adv.main (initial g pk))
      (fun q => Reduction.signRequest q = true) qS)
    (hH : ∀ pk, IsQueryBoundP (adv.main (initial g pk))
      (fun q => Reduction.hashRequest q = true) qH) :
    𝒟[game g adv] {true} ≤
      𝒟[DiffieHellman.dlogExperiment g (dlogReduction adv)] {true} +
        (qH + 1 : ENNReal) * (Fintype.card F : ENNReal)⁻¹ +
        (qS : ENNReal) * (qS + qH) * (Fintype.card F : ENNReal)⁻¹ := by
  rw [dlogExperiment_eq]
  exact Schnorr.AGM.security g hg adv qS qH hS hH

end Signatures.Runtime.SchnorrAGM
