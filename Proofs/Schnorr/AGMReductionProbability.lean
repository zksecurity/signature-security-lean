import Proofs.Schnorr.AGMRunSound
import VCVio.EvalDist.Monad.Disagreement.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-! The adaptive exceptional-challenge bound for the single-pass AGM reduction.
Only fresh hash reads can set bad; signing and private randomness preserve it. -/

open OracleComp OracleSpec GroupModel.Interaction
open scoped ENNReal

namespace Schnorr.AGM.Reduction

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F] [Fintype F]

def hashRequest (q : Explained F (Request M) (Group G)) : Bool :=
  match q.value.data with | .hash _ => true | _ => false

theorem read_bad (s : State F G M) (hb : s.bad = false) (key : M × G) (a : Affine F) :
    Pr{let p ← (read key a).run s}[p.2.bad = true] ≤ (Fintype.card F : ENNReal)⁻¹ := by
  cases hc : s.cache key with
  | some e => simp [read, StateT.run, hc, hb]
  | none =>
      simp only [read, StateT.run, hc, bind_pure_comp, prEvent_map, Function.comp_def,
        record, hb, Bool.false_or, decide_eq_true_eq, bad_challenge_iff]
      exact (SampleableType.prEvent_uniformSample_eq_singleton (-a.secret)).le

theorem handler_bad (g pk : G) (s : State F G M) (hb : s.bad = false)
    (q : Explained F (Request M) (Group G)) :
    Pr{let p ← (handler g pk q).run s}[p.2.bad = true] ≤
      if hashRequest q then (Fintype.card F : ENNReal)⁻¹ else 0 := by
  rcases q with ⟨⟨request, groups⟩, coeffs⟩
  cases request with
  | random n =>
      by_cases he : groups () = [] <;>
        simp [handler, StateT.run, hashRequest, he, rejected, hb]
  | hash m =>
      simp only [handler, StateT.run, hashRequest, ite_true]
      split
      · rename_i R coeff hR hcoeff
        simpa only [bind_pure_comp, prEvent_map, Function.comp_def, StateT.run] using
          read_bad s hb (m, R) (flatten coeff s.representations)
      · simp [rejected, hb]
  | sign m =>
      by_cases he : groups () = []
      · simp only [handler, StateT.run, hashRequest, he, ne_eq, not_true_eq_false, ite_false]
        apply le_of_eq
        apply prEvent_eq_zero_of_forall_mem_support
        intro p hp hbad
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
        obtain ⟨c, _, z, _, rfl⟩ := hp
        simp [signedState, hb] at hbad
      · simp [handler, StateT.run, hashRequest, he, rejected, hb]

/-- The bound counts all hash calls, so it is valid under arbitrary adaptive repeats. -/
theorem simulate_bad
    (g pk : G)
    (program : OracleComp (explainedSpec F (Group G) (Request M) (Reply F M))
      (Explained F (M × F) (Group G)))
    (n : Nat) (hq : IsQueryBoundP program (fun q => hashRequest q = true) n)
    (s : State F G M) (hb : s.bad = false) :
    Pr{let p ← (simulateQ (handler g pk) program).run s}[p.2.bad = true] ≤
      (n : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  induction program using OracleComp.inductionOn generalizing s n with
  | pure out => simp [hb]
  | query_bind q next ih =>
      rw [isQueryBoundP_query_bind_iff] at hq
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      have hstep := handler_bad g pk s hb q
      have htail : ∀ p ∈ support ((handler g pk q).run s), ¬p.2.bad = true →
          Pr{let z ← (simulateQ (handler g pk) (next p.1)).run p.2}[z.2.bad = true] ≤
            ((if hashRequest q = true then n - 1 else n : Nat) : ENNReal) *
              (Fintype.card F : ENNReal)⁻¹ := by
        intro p _ hp
        exact ih p.1 _ (hq.2 p.1) p.2 (by simpa using hp)
      have hsplit := prEvent_bind_le_prEvent_add_of_support _ _ _ _ htail
      refine hsplit.trans ((add_le_add hstep le_rfl).trans ?_)
      by_cases hh : hashRequest q = true
      · have hn : 0 < n := hq.1.resolve_left (not_not.mpr hh)
        simp only [hh, ite_true]
        rw [← one_add_mul, ← Nat.cast_one, ← Nat.cast_add]
        have he : 1 + (n - 1) = n := by omega
        rw [he]
      · simp [hh]

theorem finish_bad (g pk : G) (s : State F G M) (hb : s.bad = false)
    (out : Explained F (M × F) (Group G)) :
    Pr{let p ← (finish g pk out).run s}[p.2.bad = true] ≤
      (Fintype.card F : ENNReal)⁻¹ := by
  unfold finish
  split
  · rename_i R coeff hR hcoeff
    simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
    simpa only [bind_pure_comp, prEvent_map, Function.comp_def] using
      read_bad s hb (out.value.data.1, R) (flatten coeff s.representations)
  · simp [hb]

/-- The final verifier query adds one opportunity for the exceptional challenge. -/
theorem run_bad (g pk : G) (adv : Adversary F G M) (qH : Nat)
    (hq : IsQueryBoundP (adv.main (initial g pk)) (fun q => hashRequest q = true) qH) :
    Pr{let p ← run g pk adv}[p.2.bad = true] ≤
      (qH + 1 : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  simp only [run, StateT.run_bind]
  have htail : ∀ p ∈ support ((simulateQ (handler g pk) (adv.main (initial g pk))).run {}),
      ¬p.2.bad = true → Pr{let z ← (finish g pk p.1).run p.2}[z.2.bad = true] ≤
        (Fintype.card F : ENNReal)⁻¹ := by
    intro p _ hp
    exact finish_bad g pk p.2 (by simpa using hp) p.1
  refine (prEvent_bind_le_prEvent_add_of_support _ _ _ _ htail).trans ?_
  have hbody := simulate_bad g pk (adv.main (initial g pk)) qH hq {} rfl
  simpa only [add_mul, one_mul] using add_le_add hbody (le_refl (Fintype.card F : ENNReal)⁻¹)

theorem run_success_le (g : G) (hg : Function.Injective (fun x : F => x • g))
    (x : F) (adv : Adversary F G M) (qH : Nat)
    (hq : IsQueryBoundP (adv.main (initial g (x • g))) (fun q => hashRequest q = true) qH) :
    Pr{let p ← run g (x • g) adv}[p.1.1 = true] ≤
      Pr{let p ← run g (x • g) adv}[p.1.2 = x] +
        (qH + 1 : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  have hsplit : Pr{let p ← run g (x • g) adv}[p.1.1 = true] ≤
      Pr{let p ← run g (x • g) adv}[p.1.2 = x] +
        Pr{let p ← run g (x • g) adv}[p.2.bad = true] := by
    refine (prEvent_mono_of_support _ _ (fun p => p.1.2 = x ∨ p.2.bad = true) ?_).trans
      (prEvent_or_le _ _ _)
    intro p hp hw
    by_cases hb : p.2.bad = true
    · exact Or.inr hb
    · exact Or.inl (run_extract g hg x adv p.1 p.2 hp hw (by simpa using hb))
  exact hsplit.trans (add_le_add le_rfl (run_bad g (x • g) adv qH hq))

/-- This game uses simulated signing. Relating it to the source game requires
the separate signing-simulation comparison; its name makes that boundary explicit. -/
def simulatedGame (g : G) (adv : Adversary F G M) : ProbComp Bool := do
  let x ← $ᵗ F
  let p ← run g (x • g) adv
  pure p.1.1

/-- Native probability endpoint for the simulated game and the actual one-pass solver. -/
theorem simulated_security (g : G) (hg : Function.Injective (fun x : F => x • g))
    (adv : Adversary F G M) (qH : Nat)
    (hq : ∀ pk, IsQueryBoundP (adv.main (initial g pk)) (fun q => hashRequest q = true) qH) :
    𝒟[simulatedGame g adv] {true} ≤
      𝒟[DiffieHellman.dlogExperiment g (dlogReduction g adv)] {true} +
        (qH + 1 : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by
  rw [← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton,
    ← add_zero (Pr{let b ← DiffieHellman.dlogExperiment g (dlogReduction g adv)}[b = true])]
  simp only [simulatedGame, DiffieHellman.dlogExperiment, dlogReduction,
    bind_map_left, bind_assoc, pure_bind]
  -- The secret draw has no disagreement set; the slack comes from each fixed-key run.
  refine prEvent_bind_le_add_of_disagree (D := fun _ => False)
    (prEvent_eq_zero_of_forall_not _ _ fun _ => id).le fun x _ _ => ?_
  simpa only [bind_pure_comp, prEvent_map, Function.comp_def, decide_eq_true_eq] using
    run_success_le g hg x adv qH (hq (x • g))

end Schnorr.AGM.Reduction
