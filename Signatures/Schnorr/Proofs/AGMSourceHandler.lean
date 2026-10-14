import Signatures.Schnorr.Proofs.AGMSourceClose
import Signatures.Schnorr.Proofs.AGMHonestSupport

/-! Primitive equations for the original source handler under the shared lazy cache. -/

open OracleComp OracleSpec AlgebraicGroupModel.Interaction

set_option backward.isDefEq.respectTransparency false

namespace Schnorr.AGM.Reduction.Source

variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]

theorem handler_random (g : G) (x : F) (n : Nat) (groups : Groups (Group G))
    (st : Schnorr.AGM.State M) (cache : Cache F G M) :
    (close (Schnorr.AGM.handler g x ⟨.random n, groups⟩)).run (st, cache) =
      (do let v ← (unifSpec.query n : ProbComp _)
          pure (⟨v, fun _ => []⟩,
            (if groups () = [] then st else {st with malformed := true}, cache))) := by
  by_cases he : groups () = [] <;>
    simp only [Schnorr.AGM.handler, he, ne_eq, not_true_eq_false, not_false_eq_true,
      ite_true, ite_false, close_bind, close_pure, StateT.run_bind, StateT.run_pure,
      close_reject, close_random, bind_map_left, pure_bind]

theorem handler_hash (g : G) (x : F) (m : M) (groups : Groups (Group G)) (R : G)
    (hR : groups () = [R]) (st : Schnorr.AGM.State M) (cache : Cache F G M) :
    (close (Schnorr.AGM.handler g x ⟨.hash m, groups⟩)).run (st, cache) =
      (do let (c, cache') ← ((M × G →ₒ F).randomOracle (m, R)).run cache
          pure (scalarReply c, (st, cache'))) := by
  simp only [Schnorr.AGM.handler, hR, close_bind, close_pure, StateT.run_bind,
    StateT.run_pure, close_hash, bind_map_left]

theorem handler_sign (g : G) (x : F) (m : M) (groups : Groups (Group G))
    (he : groups () = []) (st : Schnorr.AGM.State M) (cache : Cache F G M) :
    (close (Schnorr.AGM.handler g x ⟨.sign m, groups⟩)).run (st, cache) =
      (do let r ← $ᵗ F
          let (c, cache') ← ((M × G →ₒ F).randomOracle (m, r • g)).run cache
          pure (signingReply (r • g) (r + c * x), ({st with signed := st.signed ++ [m]}, cache'))) := by
  simp only [Schnorr.AGM.handler, he, ne_eq, not_true_eq_false, ite_false,
    close_bind, close_pure, StateT.run_bind, StateT.run_pure, close_sample, close_hash,
    close_modify, bind_map_left, bind_assoc, pure_bind]

/-- The reduction's first-representation bookkeeping leaves ordinary cache reads unchanged. -/
theorem read_erase (s : Reduction.State F G M) (key : M × G) (a : Affine F) :
    (fun p => (p.1, erase p.2)) <$> (Reduction.read key a).run s =
      (fun p => (p.1, ((erase s).1, p.2))) <$>
        ((M × G →ₒ F).randomOracle key).run (erase s).2 := by
  cases hc : s.cache key with
  | some e =>
      have he : (erase s).2 key = some e.challenge := by simp [erase, hc]
      rw [randomOracle.run_eq, he]
      simp only [Reduction.read, StateT.run, hc, map_pure]
  | none =>
      have he : (erase s).2 key = none := by simp [erase, hc]
      rw [randomOracle.run_eq, he]
      simp only [Reduction.read, StateT.run, hc, map_bind, map_pure, erase_record,
        Functor.map_map]

end Schnorr.AGM.Reduction.Source
