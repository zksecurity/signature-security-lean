import Proofs.Runtime.SchnorrLazySeedBounds

/-! Exact first-pass recording law, including the returned tape. This will be
needed to compare joint two-pass distributions; a marginal output identity
alone cannot justify changing a forking implementation. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.LazySeed

variable {F A : Type} [Zero F]

/-- The lazy first pass stores precisely the chronological query log, in the
same run that produces the output. This includes both private families. -/
theorem run_log (main : OracleComp (replaySpec F) A) (saved : List (TapeCell F)) :
    (simulateQ oracle main).run ⟨saved, []⟩ =
      (fun p => (p.1, (⟨saved ++ encodeTape p.2, []⟩ : State F))) <$> main.withQueryLog := by
  induction main using OracleComp.inductionOn generalizing saved with
  | pure a => simp [encodeTape]
  | query_bind i next ih =>
      change (simulateQ oracle (OracleComp.queryBind i next)).run ⟨saved, []⟩ =
        (fun p => (p.1, (⟨saved ++ encodeTape p.2, []⟩ : State F))) <$>
          (OracleComp.queryBind i next).withQueryLog
      rw [Replay.withQueryLog_queryBind]
      change ((fun answer => (answer, (⟨saved ++ [encodeReply i answer], []⟩ : State F))) <$>
        (liftM ((replaySpec F).query i) : OracleComp (replaySpec F) _) >>=
          fun p => (simulateQ oracle (next p.1)).run p.2) =
        (fun p => (p.1, (⟨saved ++ encodeTape p.2, []⟩ : State F))) <$>
          ((liftM ((replaySpec F).query i) : OracleComp (replaySpec F) _) >>= fun answer =>
            (fun p => (p.1, ⟨i, answer⟩ :: p.2)) <$> (next answer).withQueryLog)
      simp only [bind_map_left, map_bind]
      congr 1
      funext answer
      rw [ih]
      simp only [Functor.map_map, encodeTape, List.map_cons, List.append_assoc,
        List.singleton_append]

/-- Exact joint law for the implemented two-pass component: record the first
path, reset its saved seed, then execute the second path against that seed.
The remaining probability bridge must compare this encountered-path seed to
independently pregenerated seeds, including unused private entries. -/
theorem twoPass_seeded {B : Type} (main : OracleComp (replaySpec F) A)
    (replay : A → OracleComp (replaySpec F) B) (i : (replaySpec F).Domain)
    (slot : A → Nat) (answer : A → (replaySpec F).Range i) :
    Prod.fst <$> twoPass main replay i slot answer = (do
      let first ← main.withQueryLog
      let second ← (simulateQ seededOracle (replay first.1)).run'
        (((SeedTape.toSeed (encodeTape first.2)).takeAtIndex i (slot first.1)).addValue i (answer first.1))
      pure (first.1, second)) := by
  simp only [twoPass, map_bind, map_pure]
  rw [run_log main []]
  simp only [bind_map_left, List.nil_append]
  congr 1
  funext first
  have h := congrArg (Functor.map (fun b => (first.1, b)))
    (run'_seeded (replay first.1)
      (restart i (slot first.1) (answer first.1) ⟨encodeTape first.2, []⟩))
  rw [restart_seed] at h
  simpa only [StateT.run', StateT.run, Functor.map_map, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind] using h

end Signatures.Runtime.Schnorr.LazySeed
