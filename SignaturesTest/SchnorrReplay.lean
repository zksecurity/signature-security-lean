import VCVio.CryptoFoundations.ReplayForkCost

/-! Concrete replay boundaries: retain the prefix, resample the suffix, reject equal answers. -/

open OracleComp OracleSpec
open PFunctor.FreeM PFunctor.FreeM.Cursor

namespace SignaturesTest.SchnorrReplay

private def threeQueries : OracleComp (Unit →ₒ Bool) (Bool × Bool × Bool) :=
  OracleComp.queryBind () fun prior =>
    OracleComp.queryBind () fun challenge =>
      OracleComp.queryBind () fun suffix => pure (prior, challenge, suffix)

private def path (a b c : Bool) : Path threeQueries := ⟨a, b, c, PUnit.unit⟩

-- The selected second query resumes after the recorded prefix, not from the beginning.
example (a b c : Bool) :
    ((locateAt? () threeQueries (path a b c) 1).get (by rfl)).occurrence.resume (!b) =
      OracleComp.queryBind () (fun suffix => pure (a, !b, suffix)) := by
  rfl

-- The focused answer and suffix are resampled; only the prefix is shared.
example (a b c : Bool) :
    (fun view : ForkView () threeQueries 1 =>
      (output threeQueries view.firstPath, output threeQueries view.secondPath)) <$>
        ((locateAt? () threeQueries (path a b c) 1).get (by rfl)).fork =
      (do
        let b' ← ((Unit →ₒ Bool).query () : OracleComp (Unit →ₒ Bool) Bool)
        let c' ← ((Unit →ₒ Bool).query () : OracleComp (Unit →ₒ Bool) Bool)
        pure ((a, b, c), (a, b', c'))) := by
  rfl

-- An absent occurrence cannot be turned into a rewind point.
example (a b c : Bool) : locateAt? () threeQueries (path a b c) 3 = none := by rfl

-- Replaying the same challenge cannot produce an accepted extraction witness.
example (view : ForkView () threeQueries 1)
    (heq : view.firstAnswer = view.secondAnswer) :
    classifyForkView threeQueries (fun _ => 1) () (fun _ => some 1) 1 view = none := by
  simp [classifyForkView, heq]

-- Different challenges alone do not suffice: the second run must select the same query.
example (view : ForkView () threeQueries 1)
    (select : (Bool × Bool × Bool) → Option (Fin 2))
    (hsecond : select (output threeQueries view.secondPath) ≠ some 1) :
    classifyForkView threeQueries (fun _ => 1) () select 1 view = none := by
  simp [classifyForkView, hsecond]

-- The bound counts both executions, not just the suffix that survives the success guard.
example : IsQueryBoundP
    (contextFork threeQueries (fun _ => 1) () (fun _ => some 1)) (fun _ => True) 6 := by
  apply isQueryBoundP_contextFork (fun _ => True) _ _ _ _ 3
  exact ⟨Or.inr (by decide), fun _ =>
    ⟨Or.inr (by decide), fun _ => ⟨Or.inr (by decide), fun _ => trivial⟩⟩⟩

end SignaturesTest.SchnorrReplay
