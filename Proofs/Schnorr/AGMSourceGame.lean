import Proofs.Schnorr.AGMSourceProgram

/-! The instrumented honest experiment has exactly the original AGM game's law. -/

open OracleComp OracleSpec AlgebraicGroupModel.Interaction

set_option backward.isDefEq.respectTransparency false

namespace Schnorr.AGM.Reduction.Source

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]

/-- Original verification, retaining the signing state only for freshness. -/
def finalCheck (g pk : G) (out : Explained F (M × F) (Group G)) :
    StateT (Schnorr.AGM.State M) (OracleComp (BaseSpec F G M)) Bool := do
  match out.value.groups () with
  | [R] =>
      let st ← get
      let c ← liftM ((BaseSpec F G M).query (.inr (out.value.data.1, R)))
      pure (!st.malformed && decide
        (out.value.data.1 ∉ st.signed ∧ out.value.data.2 • g = R + c • pk))
  | _ => pure false

theorem close_get (st : Schnorr.AGM.State M) (cache : Cache F G M) :
    (close (F := F) (G := G) (M := M) get).run (st, cache) =
      pure (st, (st, cache)) := by
  rw [close_run]
  simp [StateT.run_get]

theorem close_finalCheck (g pk : G) (out : Explained F (M × F) (Group G))
    (s : ClosedState F G M) :
    (close (finalCheck g pk out)).run' s =
      match out.value.groups () with
      | [R] => do
          let (c, _) ← ((M × G →ₒ F).randomOracle (out.value.data.1, R)).run s.2
          pure (!s.1.malformed && decide
            (out.value.data.1 ∉ s.1.signed ∧ out.value.data.2 • g = R + c • pk))
      | _ => pure false := by
  rcases s with ⟨st, cache⟩
  cases hg : out.value.groups () with
  | nil => simp only [finalCheck, hg, close_pure, StateT.run'_eq, StateT.run_pure, map_pure]
  | cons R rest =>
      cases rest with
      | cons R' rest =>
          simp only [finalCheck, hg, close_pure, StateT.run'_eq, StateT.run_pure, map_pure]
      | nil =>
          simp only [finalCheck, hg, StateT.run'_eq, close_bind, close_pure,
            StateT.run_bind, StateT.run_pure, close_get, pure_bind, close_hash,
            bind_map_left, map_bind, map_pure]

theorem finish_erase (g pk : G) (s : Reduction.State F G M)
    (out : Explained F (M × F) (Group G))
    (hout : out.Valid (representedBasis g pk s.representations)) :
    (fun p => p.1.1) <$> (Reduction.finish g pk out).run s =
      (close (finalCheck g pk out)).run' (erase s) := by
  rw [close_finalCheck]
  cases hg : out.value.groups () with
  | nil => simp only [Reduction.finish, hg, StateT.run_pure, map_pure]
  | cons R rest =>
      cases rest with
      | cons R' rest => simp only [Reduction.finish, hg, StateT.run_pure, map_pure]
      | nil =>
          obtain ⟨co, hco, _, _⟩ := valid_singleton g pk R s.representations out hout hg
          simp only [Reduction.finish, hg, hco, StateT.run_bind, StateT.run_get,
            StateT.run_pure, pure_bind, map_bind, map_pure]
          cases hc : s.cache (out.value.data.1, R) with
          | some e =>
              have he : (erase s).2 (out.value.data.1, R) = some e.challenge := by
                simp [erase, hc]
              rw [randomOracle.run_eq, he]
              simp only [Reduction.read, StateT.run, hc, pure_bind, erase]
          | none =>
              have he : (erase s).2 (out.value.data.1, R) = none := by simp [erase, hc]
              rw [randomOracle.run_eq, he]
              simp only [Reduction.read, StateT.run, hc, bind_assoc, pure_bind, record, erase]

def body (g : G) (x : F) (A : Adversary F G M) :
    StateT (Schnorr.AGM.State M) (OracleComp (BaseSpec F G M)) Bool := do
  let out ← simulateQ (fun q => Schnorr.AGM.handler g x q.value) (A.main (initial g (x • g)))
  finalCheck g (x • g) out

theorem honest_body (g : G) (x : F) (A : Adversary F G M) :
    𝒮[(fun p => p.1.1) <$> honestRun g x A] =
      𝒮[(close (body g x A)).run' ({}, ∅)] := by
  have h := simulate_observe g x (A.main (initial g (x • g))) {}
    (initial_valid g (x • g)) (by simpa using A.algebraic (initial g (x • g)))
    (fun out s => (fun p => p.1.1) <$> (Reduction.finish g (x • g) out).run s)
    (fun out s => (close (finalCheck g (x • g) out)).run' s)
    (fun out s _ hout => congrArg evalSPMF (finish_erase g (x • g) s out hout))
  simpa only [honestRun, body, close_bind, close_simulate, StateT.run_bind,
    StateT.run'_eq, map_bind, erase_empty] using h

theorem experiment_body (g : G) (A : Adversary F G M) :
    Schnorr.AGM.experiment g A = (do
      let x ← liftComp ($ᵗ F) (BaseSpec F G M)
      (body g x A).run' {}) := by
  unfold Schnorr.AGM.experiment
  congr 1
  funext x
  have hr := run_project A (Schnorr.AGM.handler g x) (initial g (x • g))
  unfold body
  rw [← hr]
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_map, bind_map_left,
    map_bind]
  congr 1
  funext p
  cases hg : p.1.1.value.groups () with
  | nil => simp only [finalCheck, hg, StateT.run_pure, map_pure]
  | cons R rest =>
      cases rest with
      | cons R' rest => simp only [finalCheck, hg, StateT.run_pure, map_pure]
      | nil =>
          simp only [finalCheck, hg, StateT.run_bind, StateT.run_get, pure_bind,
            StateT.run_pure, map_bind, map_pure]
          rfl

theorem game_body (g : G) (A : Adversary F G M) :
    Schnorr.AGM.game g A = (do
      let x ← $ᵗ F
      (close (body g x A)).run' ({}, ∅)) := by
  rw [Schnorr.AGM.game, experiment_body]
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, map_bind,
    roSim.run_liftM, liftComp_eq_liftM, bind_map_left]
  congr 1
  funext x
  simp only [close_run, StateT.run'_eq, simulateQ_map, StateT.run_map,
    Functor.map_map]
  rfl

end Schnorr.AGM.Reduction.Source

namespace Schnorr.AGM.Reduction

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]

/-- Representation bookkeeping and padded signing draws do not change the source game. -/
theorem honestGame_eq (g : G) (A : Adversary F G M) :
    𝒮[honestGame g A] = 𝒮[Schnorr.AGM.game g A] := by
  rw [honestGame, Source.game_body]
  apply evalSPMF_bind_congr'
  intro x
  simpa only [← map_eq_pure_bind] using Source.honest_body g x A

end Schnorr.AGM.Reduction
