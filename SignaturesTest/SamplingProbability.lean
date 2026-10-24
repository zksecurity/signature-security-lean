import Proofs.Runtime.HeapProbability

open Signatures.Runtime OracleComp
open scoped ENNReal

example (n w k : Nat) [NeZero n] (h : n ≤ 2^w) :
    MarkedProbability.bad (PaddedSampling.decoded n w k) ≤ (1/2 : ℝ≥0∞)^k :=
  PaddedSampling.decoded_bad_le n w k h

example {A : Type} (a : A) :
    MarkedProbability.bad
      (MarkedProbability.simulate (MachineSampling.real 3 3 2)
        (pure a : OracleComp (MachineSampling.spec (ZMod 3)) A)) = 0 :=
  MarkedProbability.bad_pure a

example {A : Type} (p : PMF (A × Bool)) :
    MarkedProbability.bad (p.map (fun out => (out.1, true || out.2))) = 1 :=
  MarkedProbability.bad_mark p true

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``MarkedProbability.event_le_add_bad, ``MarkedProbability.simulate_bound,
      ``MarkedProbability.simulate_state,
      ``PaddedSampling.decoded_good_le, ``PaddedSampling.decoded_bad_le,
      ``QueryCost.isQueryBound, ``Program.run_queryCost, ``Program.run_mmap,
      ``MachineSampling.tree_bound, ``MachineSampling.packageTree_bound,
      ``MachineSampling.probability, ``MachineSampling.ideal_measure,
      ``MachineSampling.uniformSample_law, ``MachineSampling.package_ideal_probability,
      ``HeapMachine.effects_probability, ``HeapMachine.package_probability,
      ``HeapMachine.package_error, ``HeapMachine.scalarValue_eq] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
