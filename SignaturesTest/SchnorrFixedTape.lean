import Proofs.Schnorr.FixedTapeROM
import Proofs.Runtime.SchnorrSeededSecurity
import Lean.Util.CollectAxioms

open OracleComp OracleSpec

namespace SignaturesTest.SchnorrFixedTape

private abbrev Spec := Schnorr.FixedTape.Spec (Fin 2)

noncomputable local instance : IsUniformSpec (Unit →ₒ Fin 2) :=
  IsUniformSpec.ofFintypeInhabited _

private def afterHash : OracleComp Spec (Fin 2 × Fin 2) := do
  let c ← Spec.query (.inr ())
  let b ← Spec.query (.inl 1)
  pure (c, b)

private def seed : QuerySeed Spec :=
  (∅ : QuerySeed Spec).addValue (.inl 1) (1 : Fin 2) |>.addValue (.inr ()) (0 : Fin 2)

/-- This private bit is read after the changed hash, but must stay one in both executions. -/
example : ((seed.takeAtIndex (.inr ()) 0).addValue (.inr ()) (1 : Fin 2)) (.inl 1) =
    [(1 : Fin 2)] := by
  rw [Schnorr.FixedTape.private_seed_unchanged]
  simp [seed, QuerySeed.addValue, QuerySeed.addValues]

example : (simulateQ seededOracle afterHash).run' seed = pure (0, 1) := by
  rfl

example : (simulateQ seededOracle afterHash).run'
    ((seed.takeAtIndex (.inr ()) 0).addValue (.inr ()) (1 : Fin 2)) = pure (1, 1) := by
  rfl

example : seededForkWithSeedValue afterHash (Schnorr.FixedTape.bounds 1 1 1)
    (.inr ()) (fun _ => some (0 : Fin 2)) seed (1 : Fin 2) =
      pure (some ((0, 1), (1, 1))) := by
  rfl

private def finalOnly : OracleComp Spec (Fin 2) := Spec.query (.inr ())

/-- Even with no adversarial hash calls, the final verifier query supplies one
real fork position. Additional seed capacity must not turn its denominator into two. -/
example : (1 / 2 : ENNReal) ≤ Pr[fun r => r.isSome |
    Schnorr.FixedTape.completeFork finalOnly [] 0 0 (fun _ => some (0 : Fin 1))] := by
  have h := Schnorr.FixedTape.completeFork_success_bound finalOnly [] 0 0
    (fun _ => some (0 : Fin 1))
  norm_num at h ⊢
  exact h

open Signatures.Runtime Signatures.Runtime.Schnorr in
private def sparseFamilies : Program CryptoOp (Command 1000) [] (boundedNat 1000) :=
  .bind (.query (.random ⟨0, by omega⟩) .unit)
    (.query (.random ⟨1000, by omega⟩) .unit)

/-- Large sampler arities do not allocate every smaller family. -/
example : Signatures.Runtime.Schnorr.sourceFamilies sparseFamilies =
    [Sum.inr (), Sum.inl (Sum.inl 0), Sum.inl (Sum.inl 1000)] := rfl

example : Signatures.Runtime.Schnorr.Seeded.budget sparseFamilies 10 (fun _ => 0) 0
    (Sum.inl (Sum.inl 500)) = 0 := by decide

end SignaturesTest.SchnorrFixedTape

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``Schnorr.FixedTape.first_no_live, ``Schnorr.FixedTape.replay_live_bound,
      ``Schnorr.FixedTape.private_seed_unchanged, ``Schnorr.FixedTape.fork_success_bound,
      ``Signatures.Runtime.SeededReplay.seededFork_support_context,
      ``Schnorr.FixedTape.completeFork_success_bound,
      ``Schnorr.FixedTape.complete_replay_live_bound,
      ``FiatShamir.FixedTape.pointwise_extraction_bound,
      ``FiatShamir.FixedTape.euf_cma_bound, ``Schnorr.FixedTape.security,
      ``Signatures.Runtime.SourceBudget.denote_totalQueryBound,
      ``Signatures.Runtime.Schnorr.macroPass_seedBudget,
      ``Signatures.Runtime.Schnorr.macroPass_forkPoint_reachable,
      ``Signatures.Runtime.Schnorr.Seeded.fork_support_context,
      ``Signatures.Runtime.Schnorr.Seeded.fork_success_bound,
      ``Signatures.Runtime.Schnorr.Seeded.replay_live_bound,
      ``Signatures.Runtime.Schnorr.Seeded.pointwise_extraction_bound,
      ``Signatures.Runtime.Schnorr.Seeded.security] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
