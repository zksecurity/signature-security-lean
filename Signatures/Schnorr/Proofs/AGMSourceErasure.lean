import Signatures.Schnorr.Proofs.AGMSourceHandler
import Signatures.Schnorr.Proofs.AGMRunSound

/-! Erasing representation metadata recovers the original source oracle exactly. -/

open OracleComp OracleSpec AlgebraicGroupModel.Interaction OracleComp.DeferredSampling

set_option backward.isDefEq.respectTransparency false

namespace Schnorr.AGM.Reduction.Source

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]

theorem erase_signed (g : G) (x : F) (s : Reduction.State F G M)
    (m : M) (c r : F) :
    erase (signedState s g (x • g) m c (r + c * x)) =
      (⟨s.signed ++ [m], s.malformed⟩,
        match s.cache (m, r • g) with
        | some _ => (erase s).2
        | none => (erase s).2.cacheQuery (m, r • g) c) := by
  simp only [signedState, shiftedCommit]
  cases hc : s.cache (m, r • g) with
  | some e => rfl
  | none =>
      apply Prod.ext
      · rfl
      · ext key
        by_cases hk : key = (m, r • g)
        · subst key; simp [erase]
        · simp [erase, hk, QueryCache.cacheQuery_of_ne]

theorem sign_erase (g : G) (x : F) (s : Reduction.State F G M) (m : M) :
    𝒮[(fun p => (p.1, erase p.2)) <$> honestSign g x s m] =
      𝒮[do let r ← $ᵗ F
           let (c, cache') ← ((M × G →ₒ F).randomOracle (m, r • g)).run (erase s).2
           pure (signingReply (r • g) (r + c * x),
             (⟨s.signed ++ [m], s.malformed⟩, cache'))] := by
  rw [evalSPMF_map, honestSign_normal, ← evalSPMF_map]
  simp only [map_bind, map_pure]
  apply evalSPMF_bind_congr_left
  intro r
  rw [randomOracle.run_eq]
  cases hc : s.cache (m, r • g) with
  | some e =>
      have he : (erase s).2 (m, r • g) = some e.challenge := by simp [erase, hc]
      simp only [he, hc, pure_bind, signingOutput, shiftedCommit, map_bind, map_pure, erase_signed, hc]
  | none =>
      have he : (erase s).2 (m, r • g) = none := by simp [erase, hc]
      simp only [he, hc, bind_assoc, pure_bind, signingOutput, shiftedCommit, map_bind, map_pure, erase_signed, hc]

theorem handler_erase (g : G) (x : F) (s : Reduction.State F G M)
    (q : Explained F (Request M) (Group G))
    (hq : q.Valid (representedBasis g (x • g) s.representations)) :
    𝒮[(fun p => (p.1, erase p.2)) <$> (honestHandler g x q).run s] =
      𝒮[(close (Schnorr.AGM.handler g x q.value)).run (erase s)] := by
  rcases q with ⟨⟨request, groups⟩, coeffs⟩
  cases request with
  | random n =>
      rw [handler_random]
      simp only [honestHandler, handler, StateT.run, map_bind, map_pure]
      by_cases he : groups () = [] <;> simp [he, erase, rejected]
  | hash m =>
      by_cases hsingle : ∃ R, groups () = [R]
      · obtain ⟨R, hR⟩ := hsingle
        obtain ⟨co, hco, _, _⟩ := valid_singleton g (x • g) R s.representations
          ⟨⟨Request.hash m, groups⟩, coeffs⟩ hq hR
        change coeffs () = [co] at hco
        rw [handler_hash g x m groups R hR]
        simp only [honestHandler, handler, StateT.run, hR, hco, map_bind, map_pure]
        have hr := congrArg (fun oa => (fun p => (scalarReply (G := G) p.1, p.2)) <$> oa)
          (read_erase s (m, R) (flatten co s.representations))
        simpa only [Functor.map_map, map_bind, map_pure, ← map_eq_pure_bind, Reply, StateT.run] using
          congrArg evalSPMF hr
      · have hn : ∀ R, groups () ≠ [R] := by simpa using hsingle
        cases hg : groups () with
        | nil =>
            simp only [honestHandler, handler, Schnorr.AGM.handler, hg, close_bind,
            close_pure, StateT.run_bind, StateT.run_pure, close_reject, pure_bind, map_pure]
            simp only [StateT.run_bind, StateT.run_pure, close_reject, pure_bind,
              StateT.run, map_pure]
            rfl
        | cons R tail =>
            cases tail with
            | nil => exact (hn R hg).elim
            | cons R' rest =>
                simp only [honestHandler, handler, Schnorr.AGM.handler, hg, close_bind,
                  close_pure, StateT.run_bind, StateT.run_pure, close_reject, pure_bind, map_pure]
                simp only [StateT.run_bind, StateT.run_pure, close_reject, pure_bind,
                  StateT.run, map_pure]
                rfl
  | sign m =>
      by_cases he : groups () = []
      · rw [handler_sign g x m groups he]
        simp only [honestHandler, StateT.run, he, ne_eq, not_true_eq_false, ite_false]
        convert sign_erase g x s m using 1 <;> rfl
      · simp only [honestHandler, Schnorr.AGM.handler, he, ne_eq, not_false_eq_true,
          ite_true, close_bind, close_pure, StateT.run_bind, StateT.run_pure,
          close_reject, pure_bind, StateT.run, map_pure]
        rfl

end Schnorr.AGM.Reduction.Source
