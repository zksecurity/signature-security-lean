import Proofs.Runtime.BackendStructuredCache
import Proofs.BLS.LazyAGMList

/-! Injective index encodings preserve complete weighted cache evaluation.
The relation maps only the finite encountered cache and the supplied term list;
it is a proof relation, not a runtime traversal of the index universe. -/

open OracleComp OracleSpec Model.LazyAGM
open BLS.LazyAGM.Reduction (privateListOracle privateListOracle_lookup)

namespace Signatures.Runtime.WeightedAGM

variable {F I J R : Type} [DecidableEq I] [DecidableEq J] [SampleableType R]

/-- A private read preserves the answer and the entire encoded list, including
its order, repeated keys and shadowed bindings. -/
theorem privateRead_encoded (encode : I → J) (hi : Function.Injective encode)
    (key : I) (cache : List (I × R)) :
    (privateListOracle (M := J) (R := R) (.inr (encode key))).run
        (cache.map (Prod.map encode id)) =
      (fun p => (p.1, p.2.map (Prod.map encode id))) <$>
        (privateListOracle (M := I) (R := R) (.inr key)).run cache := by
  rw [privateListOracle_lookup, privateListOracle_lookup,
    BackendProgram.StructuredCache.lookup_encoded encode hi]
  cases h : cache.lookup key <;> simp [Functor.map_map]

variable [AddCommMonoid R] [SMul F R]

/-- Encoding every index preserves the joint value/cache distribution of the
whole ordered evaluation, including zero coefficients and repeated indices. -/
theorem evalTerms_encoded (encode : I → J) (hi : Function.Injective encode)
    (rows : List (I × F)) (cache : List (I × R)) :
    (simulateQ (privateListOracle (M := J) (R := R))
      (evalTerms (rows.map (Prod.map encode id)))).run (cache.map (Prod.map encode id)) =
      (fun p => (p.1, p.2.map (Prod.map encode id))) <$>
        (simulateQ (privateListOracle (M := I) (R := R)) (evalTerms rows)).run cache := by
  induction rows generalizing cache with
  | nil => simp [evalTerms]
  | cons row rows ih =>
      simp only [List.map_cons, evalTerms, Prod.map_fst, Prod.map_snd, id_eq,
        simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
      rw [privateRead_encoded encode hi]
      simp only [bind_map_left, map_bind]
      apply congrArg
      funext first
      rw [ih]
      simp only [bind_map_left, map_pure]

end Signatures.Runtime.WeightedAGM
