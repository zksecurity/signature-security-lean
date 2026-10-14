import Signatures.Runtime.GeneralCaller
import Signatures.Runtime.Refinement

/-! Exact handler-state refinement for general callers. Ghost instrumentation
is erased with both returned values and charged runtime unchanged. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.GeneralCaller

variable {I A B : Type} {spec : OracleSpec I}
  {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
  [DecidableEq I] {Q : QuantitativeStepClass C}
  {bd : Boundary C spec.toPFunctor A B}
  (R : Caller (Q := Q) (bd := bd))
  {m : Type → Type} [Monad m] [LawfulMonad m] {S T : Type}

omit [DecidableEq I] in
/-- State refinement also composes through an arbitrary source computation's
adaptive continuations, independently of its implementation language. -/
theorem simulateQ_refines (repr : S → T)
    (implementation : QueryImpl spec (StateT S m))
    (reference : QueryImpl spec (StateT T m))
    (h : ∀ i, StateRefines repr (implementation i) (reference i))
    (program : OracleComp spec B) :
    StateRefines repr (simulateQ implementation program) (simulateQ reference program) := by
  induction program using OracleComp.inductionOn with
  | pure value => simpa using StateRefines.pure (m := m) repr value
  | query_bind i k ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleSpec.query,
        OracleQuery.cont_mk, OracleQuery.input_mk, id_map]
      exact StateRefines.bind repr (h i) ih

theorem runFrom_refines (repr : S → T)
    (implementation : Handler (spec := spec) (StateT S m))
    (reference : Handler (spec := spec) (StateT T m))
    (h : ∀ i, StateRefines repr (implementation i) (reference i))
    (fuel : Nat) (state : R.machine.State) :
    StateRefines repr (runFrom R implementation fuel state)
      (runFrom R reference fuel state) := by
  induction fuel generalizing state with
  | zero => exact StateRefines.pure repr _
  | succ fuel ih =>
      cases hv : R.machine.view state with
      | inl value => simp only [runFrom, hv]; exact StateRefines.pure repr _
      | inr request =>
          rcases request with ⟨i, next⟩
          simp only [runFrom, hv]
          apply StateRefines.bind repr (h i)
          intro answer
          apply StateRefines.bind repr (ih (next answer.value))
          intro rest
          exact StateRefines.pure repr _

theorem run_refines (repr : S → T)
    (implementation : Handler (spec := spec) (StateT S m))
    (reference : Handler (spec := spec) (StateT T m))
    (h : ∀ i, StateRefines repr (implementation i) (reference i))
    (fuel : Nat) (input : A) :
    StateRefines repr (run R implementation fuel input) (run R reference fuel input) := by
  apply StateRefines.bind repr (runFrom_refines R repr implementation reference h fuel _)
  intro result
  exact StateRefines.pure repr _

/-- A proof-only counter; its update contributes no cost because it is erased
from the actual executed handler, with exact cost equality proved below. -/
def countCalls (H : Handler (spec := spec) (StateT S m)) :
    Handler (spec := spec) (StateT (S × Nat) m) := fun i state => do
  let p ← (H i).run state.1
  pure (p.1, (p.2, state.2 + 1))

theorem run_countCalls_refines (H : Handler (spec := spec) (StateT S m))
    (fuel : Nat) (input : A) :
    StateRefines Prod.fst (run R (countCalls H) fuel input) (run R H fuel input) := by
  apply run_refines R Prod.fst _ _ ?_ fuel input
  intro i state
  simp [countCalls, StateT.run, bind_pure_comp]

def zeroHandler (H : Handler (spec := spec) m) : Handler (spec := spec) m :=
  fun i => (fun r => ⟨r.value, 0⟩) <$> H i

theorem zeroHandler_erase (H : Handler (spec := spec) m) (fuel : Nat) (input : A) :
    Run.value <$> run R (zeroHandler H) fuel input = Run.value <$> run R H fuel input := by
  simp only [run, bind_pure_comp, Functor.map_map]
  rw [runFrom_erase, runFrom_erase]
  simp [zeroHandler]

end Signatures.Runtime.GeneralCaller
