import Signatures.Runtime.CoronPairedCache

/-! Fuse the final verification hash and extraction into a paired cache read.
The discarded hash value and terminal transcript entry are unobserved. The
scalar/coin draw on a fresh message is preserved as an exact oracle computation. -/
namespace Signatures.Runtime.Coron.Paired
open OracleComp OracleSpec
variable {F M G : Type} {qS : Nat} [DecidableEq M]
    [Field F] [SampleableType F] [AddCommGroup G] [Module F G]

noncomputable def finish (X : G) (forgery : M × G) (entries : List (M × (F × Fin (qS + 1)))) : ProbComp G :=
  (fun result => forgery.2 - result.1.1 • X) <$>
    ((BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F × Fin (qS + 1))) (.inr forgery.1)).run entries

theorem finish_hash (g X h : G) (forgery : M × G) (state : State F M G qS) :
    finish X forgery state.1 =
      (fun result => forgery.2 - (scalars result.2.1 forgery.1).getD 0 • X) <$>
        (oracle g X h (.inl (.inr forgery.1))).run state := by
  simp only [finish, oracle, LazyAGM.listOracle, LazyAGM.listReply, StateT.run, Functor.map_map]
  have lookup := BLS.LazyAGM.Reduction.privateListOracle_lookup (R := F × Fin (qS + 1)) forgery.1 state.1
  simp only [StateT.run] at lookup
  simp only [lookup]
  cases found : state.1.lookup forgery.1 with
  | none => simp [Functor.map_map, scalars]
  | some entry => simp [found, scalars]

theorem reduction_finish (g X h : G) (program : BLS.ROM.Adversary M G) :
    reduction (F := F) (qS := qS) g X h program =
      (simulateQ (oracle (F := F) (qS := qS) g X h) program).run ([], ([], [])) >>=
        fun result => finish X result.1 result.2.1 := by
  simp only [reduction, BLS.ROM.cacheForgery, simulateQ_bind, StateT.run_bind, map_bind]
  apply bind_congr
  intro result
  rw [finish_hash g X h result.1 result.2]
  simp only [simulateQ_spec_query, simulateQ_pure, StateT.run_pure, map_pure, bind_pure_comp]
  rfl

end Signatures.Runtime.Coron.Paired
