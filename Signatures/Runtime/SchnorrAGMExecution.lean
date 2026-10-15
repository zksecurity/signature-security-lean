import Signatures.Runtime.SchnorrAGMCache

/-! Finite-store execution of the complete single-pass Schnorr AGM reduction.
The refinement preserves the joint output/state query tree for arbitrary adaptive
callers, including malformed requests. Runtime costs are a separate obligation. -/

open OracleComp OracleSpec AlgebraicGroupModel.Interaction Schnorr.AGM

namespace Signatures.Runtime.SchnorrAGM

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]

def handler (g pk : G) :
    QueryImpl (explainedSpec F (Group G) (Request M) (Reply F M))
      (StateT (State F G M) ProbComp) := by
  intro ⟨⟨request, groups⟩, coefficients⟩
  cases request with
  | random n => exact fun s => do
      let v ← unifSpec.query n
      pure (⟨v, fun _ => []⟩, if groups () = [] then s else rejected s)
  | hash m => exact fun s =>
      match groups (), coefficients () with
      | [R], [coeff] => do
          let (c, t) ← (read (m, R) (flatten coeff s.representations)).run s
          pure (scalarReply c, t)
      | _, _ => pure (scalarReply (0 : F), rejected s)
  | sign m => exact fun s =>
      if groups () ≠ [] then pure (scalarReply (0 : F), rejected s)
      else do
        let c ← $ᵗ F
        let z ← $ᵗ F
        pure (signingReply (z • g - c • pk) z, signedState s g pk m c z)

theorem handler_erase (g pk : G)
    (q : Explained F (Request M) (Group G)) (s : State F G M) :
    (fun p => (p.1, erase p.2)) <$> (handler g pk q).run s =
      (Reduction.handler g pk q).run (erase s) := by
  rcases q with ⟨⟨request, groups⟩, coefficients⟩
  cases request with
  | random n =>
      by_cases h : groups () = [] <;>
        simp [handler, Reduction.handler, StateT.run, h, bind_pure_comp, Functor.map_map]
  | hash m =>
      simp only [handler, Reduction.handler, StateT.run]
      split
      · rename_i R coeff hg hc
        have h := congrArg
          (Functor.map (fun p : F × Reduction.State F G M => (scalarReply (G := G) p.1, p.2)))
          (read_erase (m, R) (flatten coeff s.representations) s)
        simpa only [hg, hc, bind_pure_comp, Functor.map_map, erase, StateT.run,
          explainedSpec, OracleSpec.Range, Reply] using h
      · simp only [map_pure, erase_rejected]
  | sign m =>
      by_cases h : groups () ≠ [] <;>
        simp [handler, Reduction.handler, StateT.run, h, bind_pure_comp,
          Functor.map_map, map_bind]

/-- Refinement holds for every adaptive query tree, without assuming algebraicity. -/
theorem simulate_erase {A : Type} (g pk : G)
    (program : OracleComp (explainedSpec F (Group G) (Request M) (Reply F M)) A)
    (s : State F G M) :
    (fun p => (p.1, erase p.2)) <$> (simulateQ (handler g pk) program).run s =
      (simulateQ (Reduction.handler g pk) program).run (erase s) := by
  induction program using OracleComp.inductionOn generalizing s with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [← handler_erase g pk q s, bind_map_left]
      congr 1
      funext p
      exact ih p.1 p.2

def finish (g pk : G) (out : Explained F (M × F) (Group G)) :
    StateT (State F G M) ProbComp (Bool × F) := do
  match out.value.groups (), out.coefficients () with
  | [R], [coeff] =>
      let (m, z) := out.value.data
      let s ← get
      let c ← read (m, R) (flatten coeff s.representations)
      let s ← get
      let accepted := !s.malformed && decide (m ∉ s.signed ∧ z • g = R + c • pk)
      let solution := match cacheMap s.cache (m, R) with
        | some ⟨_, some a⟩ => (z - a.constant) / (a.secret + c)
        | _ => 0
      pure (accepted, solution)
  | _, _ => pure (false, 0)

theorem finish_erase (g pk : G) (out : Explained F (M × F) (Group G))
    (s : State F G M) :
    (fun p => (p.1, erase p.2)) <$> (finish g pk out).run s =
      (Reduction.finish g pk out).run (erase s) := by
  simp only [finish, Reduction.finish]
  split
  · rename_i R coeff hg hc
    simp only [hg, hc, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, map_bind]
    rw [← read_erase (out.value.data.1, R) (flatten coeff (erase s).representations) s,
      bind_map_left]
    simp only [map_pure, erase]
    rfl
  · simp only [StateT.run_pure, map_pure]

def run (g pk : G) (adv : Adversary F G M) : ProbComp ((Bool × F) × State F G M) :=
  (do
    let out ← simulateQ (handler g pk) (adv.main (initial g pk))
    finish g pk out).run {}

theorem run_erase (g pk : G) (adv : Adversary F G M) :
    (fun p => (p.1, erase p.2)) <$> run g pk adv = Reduction.run g pk adv := by
  simp only [run, Reduction.run, StateT.run_bind, map_bind]
  rw [← erase_initial, ← simulate_erase g pk _ {}, bind_map_left]
  congr 1
  funext p
  exact finish_erase g pk p.1 p.2

/-- Use the supplied generator, so the implementation needs no hidden fixed group input. -/
def dlogReduction (adv : Adversary F G M) : DiffieHellman.DLogAdversary F G :=
  fun g pk => (fun result => result.1.2) <$> run g pk adv

theorem dlogReduction_eq (g pk : G) (adv : Adversary F G M) :
    dlogReduction adv g pk = Reduction.dlogReduction g adv g pk := by
  have h := congrArg (Functor.map (fun p : (Bool × F) × Reduction.State F G M => p.1.2))
    (run_erase g pk adv)
  simpa only [dlogReduction, Reduction.dlogReduction, Functor.map_map] using h

end Signatures.Runtime.SchnorrAGM
