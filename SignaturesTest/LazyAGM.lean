import Proofs.BLS.LazyAGM
import Signatures.OOPS.Spec.LazyAGM
import Mathlib.Algebra.Field.ZMod

open OracleComp OracleSpec Model.LazyAGM Model.LazyAGM.Proofs

namespace SignaturesTest.LazyAGM

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def output (m : Nat) : Output Nat Nat := ⟨m, 0, [], []⟩

private def adaptive : Adversary Nat Nat Nat Nat Nat where
  main pk := do
    let h : Nat ← liftM ((advSpec Nat Nat Nat).query (.inl (.inr pk)))
    let s : Nat ← liftM ((advSpec Nat Nat Nat).query (.inr h))
    if s = 0 then return output pk
    let h' : Nat ← liftM ((advSpec Nat Nat Nat).query (.inl (.inr (s + 1))))
    return output h'

-- Hashes choose signing inputs; signatures choose later hashes and whether execution stops.
example : fixedRun adaptive 3 (fun n => n + 1) (fun n => n + 2) =
    pure (output 8, ([(3, 4), (7, 8)], [(4, 6)])) := by
  simp [fixedRun, fixedImpl, handler, adaptive]

example : fixedRun adaptive 3 (fun n => n + 1) (fun _ => 0) =
    pure (output 3, ([(3, 4)], [(4, 0)])) := by
  simp [fixedRun, fixedImpl, handler, adaptive]

private def repr : Output (ZMod 5) Bool := ⟨true, 0, [2, 4], [3, 1]⟩

-- Extra coefficients cannot manufacture unobserved base or signature tokens.
example : materialize (ι := Bool) (1 : ZMod 5) repr ([], []) = 0 := by decide
example : materialize (1 : ZMod 5) repr ([(false, 3)], []) = 1 := by decide
example : baseCoeff ([2, 4] : List (ZMod 5)) [(false, 1), (false, 1)] false = 1 := by decide
example : baseCoeff ([2, 4] : List (ZMod 5)) [(false, 1), (false, 1)] true = 0 := by decide

example : OOPS.LazyAGM.admissible (F := ZMod 5) 1 (2, true)
    [(1, true), (1, true), (2, false), (3, false)] := by
  unfold OOPS.LazyAGM.admissible
  decide
example : ¬ OOPS.LazyAGM.admissible (F := ZMod 5) 1 (3, true)
    [(1, true), (2, true)] := by
  unfold OOPS.LazyAGM.admissible
  decide

private def signFirst : Adversary (ZMod 5) Bool Bool (ZMod 5) (ZMod 5) where
  main _ := do
    let _ : ZMod 5 ← liftM ((advSpec Bool Bool (ZMod 5)).query (.inr false))
    let _ : ZMod 5 ← liftM ((advSpec Bool Bool (ZMod 5)).query (.inl (.inr false)))
    let _ : ZMod 5 ← liftM ((advSpec Bool Bool (ZMod 5)).query (.inl (.inr false)))
    return repr

private def cacheProbe : OracleComp (baseSpec Bool (ZMod 5)) Bool := do
  let (_, tr) ← Model.LazyAGM.run BLS.LazyAGM.terms 2 signFirst 2
  let target ← evalTerms [(true, (1 : ZMod 5))]
  let targetAgain ← evalTerms [(true, (1 : ZMod 5))]
  match tr with
  | ([(false, h), (false, h')], [(false, s)]) =>
    pure (decide (h = h' ∧ s = 2 • h ∧ target = targetAgain))
  | _ => pure false

-- This executes the actual lazy interpreter. Signing initializes the same cache used by later
-- hashes; internal lookups add no visible tokens. A fresh verification lookup is cached too.
example : 𝒮[(simulateQ (lazyImpl (ι := Bool) (G₁ := ZMod 5)) cacheProbe).run' ∅] =
    𝒮[(pure true : ProbComp Bool)] := by
  rw [show lazyImpl (ι := Bool) (G₁ := ZMod 5) = BLS.CoCDH.lazyCoinImpl from rfl,
    BLS.CoCDH.evalSPMF_lazyCoin_eq_table]
  simp only [tableExtending_empty]
  have htable (H : Bool → ZMod 5) :
      simulateQ (BLS.CoCDH.coinTableImpl H) cacheProbe = pure true := by
    simp only [cacheProbe, simulateQ_bind,
      run_table (F := ZMod 5) (ι := Bool) (G₁ := ZMod 5) (G₂ := ZMod 5)
        BLS.LazyAGM.terms BLS.Proofs.indicatorWeight (by
        intro H m
        simp [BLS.LazyAGM.terms, BLS.Proofs.indicatorWeight]),
      evalTerms_table, pure_bind]
    simp [fixedRun, fixedImpl, handler, signFirst,
      AlgebraicGroupModel.LinFunctional.realSign, BLS.Proofs.indicatorWeight]
  simp_rw [htable]
  apply evalSPMF_ext
  intro b
  rw [probOutput_bind_const]
  simp

/-- info: 'Model.LazyAGM.Proofs.advantage_eq_realGame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Model.LazyAGM.Proofs.advantage_eq_realGame

end SignaturesTest.LazyAGM
