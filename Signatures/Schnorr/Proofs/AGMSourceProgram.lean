import Signatures.Schnorr.Proofs.AGMSourceErasure

/-! The source-game correspondence composes over every adaptive algebraic path. -/

open OracleComp OracleSpec AlgebraicGroupModel.Interaction

set_option backward.isDefEq.respectTransparency false

namespace Schnorr.AGM.Reduction.Source

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]

theorem simulate_observe {B : Type} (g : G) (x : F)
    (program : OracleComp (explainedSpec F (Group G) (Request M) (Reply F M))
      (Explained F (M × F) (Group G)))
    (s : Reduction.State F G M) (hs : s.Valid g (x • g))
    (halg : IsAlgebraic (representedBasis g (x • g) s.representations) program)
    (obsL : Explained F (M × F) (Group G) → Reduction.State F G M → ProbComp B)
    (obsR : Explained F (M × F) (Group G) → ClosedState F G M → ProbComp B)
    (hobs : ∀ out t, t.Valid g (x • g) →
      out.Valid (representedBasis g (x • g) t.representations) →
      𝒮[obsL out t] = 𝒮[obsR out (erase t)]) :
    𝒮[(simulateQ (honestHandler g x) program).run s >>= fun p => obsL p.1 p.2] =
      𝒮[(simulateQ (fun q => close (Schnorr.AGM.handler g x q.value)) program).run
        (erase s) >>= fun p => obsR p.1 p.2] := by
  induction program using OracleComp.inductionOn generalizing s with
  | pure out =>
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact hobs out s hs halg
  | query_bind q next ih =>
      obtain ⟨hq, hn⟩ := (isAlgebraic_query _ _ _).mp halg
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
      conv_rhs =>
        rw [evalSPMF_bind, ← handler_erase g x s q hq, ← evalSPMF_bind]
      rw [bind_map_left]
      apply evalSPMF_bind_congr
      rintro ⟨reply, t⟩ ht
      have hstep := handler_spec g (x • g) s hs q hq reply t
        (honestHandler_support g x s q (reply, t) ht)
      exact ih reply t hstep.1 (by rw [hstep.2]; exact hn reply)

/-- Closing the shared lazy oracle commutes with adaptive execution. -/
theorem close_simulate {I A : Type} {spec : OracleSpec I}
    (h : QueryImpl spec (StateT (Schnorr.AGM.State M) (OracleComp (BaseSpec F G M))))
    (program : OracleComp spec A) :
    close (simulateQ h program) = simulateQ (fun q => close (h q)) program := by
  induction program using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure, close_pure]
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, close_bind]
      congr 1
      funext reply
      exact ih reply

/-- The chronological basis tracked by `Adversary.run` is observational metadata. -/
theorem run_project {N : Type → Type} [Monad N] [LawfulMonad N]
    (A : Adversary F G M) (h : QueryImpl (plainSpec (Group G) (Request M) (Reply F M)) N)
    (input : Message Unit (Group G)) :
    Prod.fst <$> A.run h input = simulateQ (fun q => h q.value) (A.main input) := by
  unfold AlgebraicGroupModel.Interaction.Adversary.run
  generalize A.main input = program
  generalize input.groups = basis
  induction program using OracleComp.inductionOn generalizing basis with
  | pure out => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, StateT.run_mk,
        bind_assoc, pure_bind, map_bind]
      congr 1
      funext reply
      exact ih reply _

end Schnorr.AGM.Reduction.Source
