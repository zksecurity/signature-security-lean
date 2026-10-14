import Signatures.Schnorr.Proofs.AGMCacheGrowth

/-! Adaptive composition of the honest/simulated signing comparison.
Cache growth consumes hash/signing budgets; private randomness is unrestricted. -/

open OracleComp OracleSpec AlgebraicGroupModel.Interaction
open scoped ENNReal

namespace Schnorr.AGM.Reduction

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F] [Fintype F]

private theorem signing_slack (k qS qH : Nat) (hS : 0 < qS) (delta : ENNReal) :
    (k : ENNReal) * delta + ((qS - 1 : Nat) : ENNReal) *
        ((k + qS + qH : Nat) : ENNReal) * delta ≤
      (qS : ENNReal) * ((k + qS + qH : Nat) : ENNReal) * delta := by
  have hk : k ≤ k + qS + qH := by omega
  have hc : (qS : ENNReal) = ((qS - 1 : Nat) : ENNReal) + 1 := by
    exact_mod_cast (show qS = qS - 1 + 1 by omega)
  calc (k : ENNReal) * delta + ((qS - 1 : Nat) : ENNReal) *
        ((k + qS + qH : Nat) : ENNReal) * delta
      ≤ ((k + qS + qH : Nat) : ENNReal) * delta + ((qS - 1 : Nat) : ENNReal) *
        ((k + qS + qH : Nat) : ENNReal) * delta := by gcongr
    _ = _ := by rw [hc]; ring

/-- Comparison for any final probabilistic observation, preserving adaptive branching. -/
theorem compare_observe {B : Type}
    (g : G) (hg : Function.Injective (fun x : F => x • g)) (x : F)
    (program : OracleComp (explainedSpec F (Group G) (Request M) (Reply F M))
      (Explained F (M × F) (Group G)))
    (qS qH k : Nat)
    (hS : IsQueryBoundP program (fun q => signRequest q = true) qS)
    (hH : IsQueryBoundP program (fun q => hashRequest q = true) qH)
    (s : State F G M) (hk : CacheBound s k)
    (observe : Explained F (M × F) (Group G) → State F G M → ProbComp B)
    (event : B → Prop) :
    Pr[event | (simulateQ (honestHandler g x) program).run s >>= fun p => observe p.1 p.2] ≤
      Pr[event | (simulateQ (handler g (x • g)) program).run s >>= fun p => observe p.1 p.2] +
        (qS : ENNReal) * ((k + qS + qH : Nat) : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  induction program using OracleComp.inductionOn generalizing qS qH k s with
  | pure out =>
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact le_add_right le_rfl
  | query_bind q next ih =>
      rw [isQueryBoundP_query_bind_iff] at hS hH
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
      rcases q with ⟨⟨request, groups⟩, coeffs⟩
      cases request with
      | random n =>
          simp [signRequest, hashRequest] at hS hH
          apply probEvent_bind_congr_le_add
          intro p hp
          have hcache := handler_cacheBound g (x • g) s k hk
            ⟨⟨Request.random n, groups⟩, coeffs⟩ p.1 p.2 hp
          exact ih p.1 qS qH k (hS p.1) (hH p.1) p.2 (by simpa [cacheCharge] using hcache)
      | hash m =>
          simp [signRequest, hashRequest] at hS hH
          apply probEvent_bind_congr_le_add
          intro p hp
          have hcache := handler_cacheBound g (x • g) s k hk
            ⟨⟨Request.hash m, groups⟩, coeffs⟩ p.1 p.2 hp
          have ht : k + 1 + qS + (qH - 1) = k + qS + qH := by omega
          simpa only [ht] using ih p.1 qS (qH - 1) (k + 1)
            (hS p.1) (hH.2 p.1) p.2 hcache
      | sign m =>
          simp [signRequest, hashRequest] at hS hH
          have ht : k + 1 + (qS - 1) + qH = k + qS + qH := by omega
          by_cases he : groups () = []
          · simp only [honestHandler, handler, StateT.run, he, ne_eq, not_true_eq_false, ite_false]
            change Pr[event | honestSign g x s m >>= fun p =>
                (simulateQ (honestHandler g x) (next p.1)).run p.2 >>= fun z => observe z.1 z.2] ≤
              Pr[event | simulatedSign g (x • g) s m >>= fun p =>
                (simulateQ (handler g (x • g)) (next p.1)).run p.2 >>= fun z => observe z.1 z.2] + _
            have hstep := honestSign_bind_le g hg x s m k hk
              (fun p => (simulateQ (honestHandler g x) (next p.1)).run p.2 >>= fun z => observe z.1 z.2)
              (fun p => (simulateQ (handler g (x • g)) (next p.1)).run p.2 >>= fun z => observe z.1 z.2)
              event (((qS - 1 : Nat) : ENNReal) * ((k + qS + qH : Nat) : ENNReal) *
                (Fintype.card F : ENNReal)⁻¹) (by
                intro c z
                simpa only [signingOutput, ht, Reply] using
                  ih (signingReply (z • g - c • (x • g)) z) (qS - 1) qH (k + 1)
                    (hS.2 _) (hH _) (signedState s g (x • g) m c z)
                    (hk.signedState g (x • g) m c z))
            rw [add_assoc] at hstep
            exact hstep.trans (add_le_add le_rfl (signing_slack k qS qH hS.1 _))
          · simp only [honestHandler, handler, StateT.run, he, ne_eq, not_false_eq_true,
              ite_true, pure_bind]
            have htail := ih (scalarReply (0 : F)) (qS - 1) qH (k + 1)
              (hS.2 _) (hH _) (rejected s) (hk.rejected.mono (Nat.le_succ k))
            rw [ht] at htail
            refine htail.trans (add_le_add le_rfl ?_)
            gcongr
            exact Nat.sub_le qS 1

/-- Honest instrumented signing and the actual reduction differ by at most the
standard qS*(qS+qH)/|F| programming-collision loss. -/
theorem honest_simulated (g : G) (hg : Function.Injective (fun x : F => x • g))
    (adv : Adversary F G M) (qS qH : Nat)
    (hS : ∀ pk, IsQueryBoundP (adv.main (initial g pk)) (fun q => signRequest q = true) qS)
    (hH : ∀ pk, IsQueryBoundP (adv.main (initial g pk)) (fun q => hashRequest q = true) qH) :
    𝒟[honestGame g adv] {true} ≤ 𝒟[simulatedGame g adv] {true} +
      (qS : ENNReal) * (qS + qH) * (Fintype.card F : ENNReal)⁻¹ := by
  rw [evalDist_apply_singleton, evalDist_apply_singleton,
    ← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  simp only [honestGame, simulatedGame, honestRun, run, StateT.run_bind, bind_assoc]
  apply probEvent_bind_congr_le_add
  intro x _
  simpa only [zero_add, Nat.cast_add] using compare_observe g hg x
    (adv.main (initial g (x • g))) qS qH 0 (hS (x • g)) (hH (x • g)) {}
    cacheBound_empty
    (fun out st => do let p ← (finish g (x • g) out).run st; pure p.1.1) (· = true)

/-- Security of the instrumented honest game, before erasing its metadata. -/
theorem honest_security (g : G) (hg : Function.Injective (fun x : F => x • g))
    (adv : Adversary F G M) (qS qH : Nat)
    (hS : ∀ pk, IsQueryBoundP (adv.main (initial g pk)) (fun q => signRequest q = true) qS)
    (hH : ∀ pk, IsQueryBoundP (adv.main (initial g pk)) (fun q => hashRequest q = true) qH) :
    𝒟[honestGame g adv] {true} ≤
      𝒟[DiffieHellman.dlogExperiment g (dlogReduction g adv)] {true} +
        (qH + 1 : ENNReal) * (Fintype.card F : ENNReal)⁻¹ +
        (qS : ENNReal) * (qS + qH) * (Fintype.card F : ENNReal)⁻¹ :=
  (honest_simulated g hg adv qS qH hS hH).trans
    (add_le_add (simulated_security g hg adv qH hH) le_rfl)

end Schnorr.AGM.Reduction
