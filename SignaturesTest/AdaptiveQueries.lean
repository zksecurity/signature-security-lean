import Proofs.Model.LazyAGM
import Signatures.BLS.Spec.ROMInternal

/-! Reply-dependent queries, stopping, and outputs in both lazy oracle interfaces.
These are execution tests, not cryptographic hardness claims. -/

open BLS.ROM

open OracleComp OracleSpec

namespace SignaturesTest.AdaptiveQueries

private def output (m : Nat) : Model.LazyAGM.Output Nat Nat := ⟨m, 0, [], []⟩

private def algebraicForger : Model.LazyAGM.Adversary Nat Unit Nat Nat Bool where
  main pk := do
    let a : Nat ← liftM ((Model.LazyAGM.advSpec Unit Nat Nat).query (.inr (if pk then 3 else 0)))
    if a = 0 then return output 99
    let b : Nat ← liftM ((Model.LazyAGM.advSpec Unit Nat Nat).query (.inr (a + 1)))
    return output (b + 1)

-- Reply-dependent signing queries retain their order and exact responses.
example : Model.LazyAGM.fixedRun algebraicForger true (fun _ => 3) (fun m => m + 1) =
    pure (output 7, ([], [(3, 4), (5, 6)])) := by
  simp [Model.LazyAGM.fixedRun, Model.LazyAGM.fixedImpl, Model.LazyAGM.handler, algebraicForger]

example : Model.LazyAGM.fixedRun algebraicForger false (fun _ => 3) (fun _ => 0) =
    pure (output 99, ([], [(0, 0)])) := by
  simp [Model.LazyAGM.fixedRun, Model.LazyAGM.fixedImpl, Model.LazyAGM.handler, algebraicForger]

private def romForger (pk : Nat) : OracleComp (advSpec Nat Nat) (Nat × Nat) := do
  let h : Nat ← liftM ((advSpec Nat Nat).query (.inl (.inr pk)))
  let s : Nat ← liftM ((advSpec Nat Nat).query (.inr h))
  if s = 0 then return (pk, 0)
  let h' : Nat ← liftM ((advSpec Nat Nat).query (.inl (.inr (s + 1))))
  return (s + 1, h')

private def romReplies (signO : Nat → Nat) : QueryImpl (advSpec Nat Nat) ProbComp :=
  fun
  | .inl (.inl n) => (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inl (.inr m) => pure (m + 1)
  | .inr m => pure (signO m)

-- Hash answers choose signing queries; signing answers choose later hashes and the target.
example : simulateQ (romReplies (fun m => m + 2)) (romForger 3) = pure (7, 8) := by
  simp [romForger, romReplies]

example : simulateQ (romReplies (fun _ => 0)) (romForger 3) = pure (3, 0) := by
  simp [romForger, romReplies]

end SignaturesTest.AdaptiveQueries
