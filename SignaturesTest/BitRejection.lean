import Proofs.Runtime.BitRejectionDistribution
import Lean.Util.CollectAxioms

open Signatures.Runtime HeapBits SharedHeap BitRejection PrimeFieldCircuit OracleComp
open scoped ENNReal

namespace SignaturesTest.BitRejection

-- Test instrumentation is separate from the controller's proved cell counter.
private def tapeOracle : QueryImpl bitSpec (StateM (List Bool × Nat)) :=
  fun _ state => (state.1.headD false, (state.1.tail, state.2+1))

private def testRun (n w k : Nat) (tape : List Bool) :=
  (simulateQ tapeOracle (execute (compile n w k))).run (tape, 0)

#eval show IO Unit from do
  for w in List.range 5 do
    for x in List.range (2^w) do
      for y in List.range (2^w) do
        let cmp := BitRejection.compare (natBits w x) (natBits w y)
        unless cmp.value == compareOfLessAndEq x y && cmp.steps == 4*w+1 do
          throw <| IO.userError "bit comparator mismatch"
    for k in List.range 4 do
      for tapeNumber in List.range (2^(w*k)) do
        let tape := natBits (w*k) tapeNumber
        let words : List (Fin (2^w)) := (List.range k).map fun i =>
          ⟨(tapeNumber / 2^(w*i)) % (2^w), Nat.mod_lt _ (by positivity)⟩
        for n in List.range (2^w+2) do
          let expected := RejectionSampling.runTape n words
          let (actual, rest, bits) := testRun n w k tape
          unless actual.value.map exponent == expected.1.map Fin.val do
            throw <| IO.userError s!"rejection result mismatch at n={n}, w={w}, k={k}"
          unless bits == w*expected.2 && rest.length+bits == w*k && bits ≤ w*k do
            throw <| IO.userError "sampler consumed the wrong bit prefix"
          unless actual.steps ≤ k*(10*w+6)+1 do
            throw <| IO.userError "sampler exceeded its CPU bound"
          if let some word := actual.value then
            unless word.length == w && exponent word < n do
              throw <| IO.userError "accepted an invalid result"
          let (fallback, remaining, used) :=
            (simulateQ tapeOracle (executeDefault (compile n w k))).run (tape, 0)
          unless fallback.value == (actual.value.getD (natBits w 0), actual.value.isNone) &&
              remaining == rest && used == bits do
            throw <| IO.userError "fallback lost the failure flag or consumed extra randomness"
          unless fallback.steps ≤ k*(10*w+6)+2*w+3 do
            throw <| IO.userError "fallback construction exceeded its CPU bound"

#eval show IO Unit from do
  let mut counts := Array.replicate 6 0
  for tape in List.range 512 do
    let (out, _, _) := testRun 5 3 3 (natBits 9 tape)
    let i := (out.value.map exponent).getD 5
    counts := counts.modify i (· + 1)
  unless counts == #[97, 97, 97, 97, 97, 27] do
    throw <| IO.userError s!"bit sampler output counts: {counts}"
  let first := testRun 5 3 3 (natBits 3 0 ++ natBits 3 7 ++ natBits 3 7)
  let last := testRun 5 3 3 (natBits 3 7 ++ natBits 3 7 ++ natBits 3 4)
  let abort := testRun 5 3 3 (natBits 9 511)
  unless first.2.2 == 3 && last.2.2 == 9 && abort.2.2 == 9 && abort.1.value.isNone do
    throw <| IO.userError "early/final/exhausted sampler path mismatch"

example : ((simulateQ (fun _ : Unit => PMF.uniformOfFintype Bool)
    (execute (compile 4 2 1))).map Run.value) none = 0 := by
  rw [execute_failure 4 2 1 (by decide)]
  norm_num [ENNReal.mul_inv_cancel]

example : ((simulateQ (fun _ : Unit => PMF.uniformOfFintype Bool)
    (execute (compile 1 0 1))).map Run.value) (some []) = 1 := by
  have h := execute_some 1 0 1 (by decide) 0
  norm_num [natBits] at h
  simpa only [PMF.map_apply] using h

example (w k : Nat) : ((simulateQ (fun _ : Unit => PMF.uniformOfFintype Bool)
    (execute (compile 0 w k))).map Run.value) none = 1 := by
  rw [execute_failure 0 w k (Nat.zero_le _)]
  simp

example : IsQueryBoundP (execute (compile 5 3 3)) (fun _ => True) 9 :=
  execute_queries 5 3 3

example (out : Run (Option (List Bool))) (h : out ∈ support (execute (compile 5 3 3))) :
    out.steps ≤ 109 := execute_steps 5 3 3 out h

example (out : Run (List Bool × Bool)) (h : out ∈ support (executeDefault (compile 5 3 3))) :
    out.value.1.length = 3 ∧ exponent out.value.1 < 5 ∧ out.steps ≤ 117 :=
  executeDefault_support 5 3 3 (by decide) out h

example : IsQueryBoundP (executeDefault (compile 5 3 3)) (fun _ => True) 9 :=
  executeDefault_queries 5 3 3

end SignaturesTest.BitRejection

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``BitRejection.compare_spec, ``BitRejection.accepts_compile,
      ``BitRejection.run_support, ``BitRejection.execute_steps,
      ``BitRejection.simulateQ_run, ``BitRejection.execute_queries,
      ``BitRejection.drawWord_distribution, ``BitRejection.run_distribution,
      ``BitRejection.execute_distribution, ``BitRejection.execute_failure,
      ``BitRejection.execute_failure_size, ``BitRejection.execute_some,
      ``BitRejection.executeDefault_support, ``BitRejection.executeDefault_queries,
      ``BitRejection.executeDefault_distribution, ``BitRejection.executeDefault_bad] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
