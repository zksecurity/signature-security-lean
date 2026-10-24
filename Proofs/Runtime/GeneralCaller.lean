import Proofs.Runtime.Composition
import PolyFun.Realizability.Quantitative
import VCVio.OracleComp.Coinductive.Machine

/-! Costed execution of general oracle callers.

Local computation is supplied by a quantitative realization, not by the arithmetic
program language. Initialization, reading the next query/result, and consuming a
reply all carry code in the selected backend. In particular, a continuation may
perform arbitrary computation, but its enabled update is charged.

The interpreter uses a query-fuel bound. Fuel exhaustion is observable; an
implementation/termination certificate must exclude it before using the runner
as a realization of an unbounded source computation. Costs remain relative to
the selected backend and explicit interpreter control charges.
-/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.GeneralCaller

variable {I A B : Type} {spec : OracleSpec I}
  {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
  [DecidableEq I] {Q : QuantitativeStepClass C}
  {bd : Boundary C spec.toPFunctor A B}

abbrev Caller := QuantitativeRealization Q bd

variable (R : Caller (Q := Q) (bd := bd))

/-- Handlers return their actual work along with the reply. -/
abbrev Handler (m : Type → Type) := (i : I) → m (Run (spec.Range i))

/-- One head read per visited state, one enabled update per answered query, and
explicit return/dispatch control. No computation in a continuation is free. -/
def runFrom {m : Type → Type} [Monad m] (H : Handler (spec := spec) m) :
    Nat → R.machine.State → m (Run (Option B))
  | 0, state =>
      pure ⟨match R.machine.view state with
        | .inl result => some result
        | .inr _ => none, Q.cost R.headCode state + 1⟩
  | fuel + 1, state =>
      match R.machine.view state with
      | .inl result => pure ⟨some result, Q.cost R.headCode state + 1⟩
      | .inr ⟨i, next⟩ => do
          let answer ← H i
          let rest ← runFrom H fuel (next answer.value)
          pure ⟨rest.value, Q.cost R.headCode state + answer.steps +
            Q.cost R.updateCode (state, ⟨i, answer.value⟩) + rest.steps + 2⟩

/-- Initialization is charged once, using the caller's actual backend code. -/
def run {m : Type → Type} [Monad m] (H : Handler (spec := spec) m)
    (fuel : Nat) (input : A) : m (Run (Option B)) := do
  let result ← runFrom R H fuel (R.machine.init input)
  pure ⟨result.value, Q.cost R.initCode input + result.steps + 1⟩

/-- Erased execution has the same control flow as bounded machine execution. -/
def denoteFrom {m : Type → Type} [Monad m] (H : QueryImpl spec m) :
    Nat → R.machine.State → m (Option B)
  | 0, state => pure (match R.machine.view state with
      | .inl result => some result
      | .inr _ => none)
  | fuel + 1, state => match R.machine.view state with
      | .inl result => pure (some result)
      | .inr ⟨i, next⟩ => H i >>= fun answer => denoteFrom H fuel (next answer)

theorem runFrom_erase {m : Type → Type} [Monad m] [LawfulMonad m]
    (H : Handler (spec := spec) m) (fuel : Nat) (state : R.machine.State) :
    Run.value <$> runFrom R H fuel state =
      denoteFrom R (fun i => Run.value <$> H i) fuel state := by
  induction fuel generalizing state with
  | zero => simp [runFrom, denoteFrom]
  | succ fuel ih =>
      cases hv : R.machine.view state with
      | inl result => simp [runFrom, denoteFrom, hv]
      | inr request =>
          rcases request with ⟨i, next⟩
          simp only [runFrom, denoteFrom, hv, map_bind, map_pure, bind_map_left]
          simp_rw [← ih]
          simp only [bind_pure_comp]

theorem denoteFrom_eq_runWith {m : Type → Type} [Monad m] [LawfulMonad m]
    (H : QueryImpl spec m) (fuel : Nat) (state : R.machine.State) :
    denoteFrom R H fuel state = R.machine.runWith H fuel state := by
  induction fuel generalizing state with
  | zero =>
      cases hv : R.machine.view state <;>
        simp [denoteFrom, runWith, unroll, hv]
  | succ fuel ih =>
      cases hv : R.machine.view state with
      | inl result => simp [denoteFrom, runWith, unroll, hv]
      | inr request =>
          rcases request with ⟨i, next⟩
          rw [R.machine.runWith_query_succ H fuel state i next hv]
          simp only [denoteFrom, hv, ih]

/-- The costed runner realizes the source program through every lawful handler.
The implementation certificate rules out fuel exhaustion on every reply path. -/
theorem run_erase {m : Type → Type} [Monad m] [LawfulMonad m]
    (H : Handler (spec := spec) m) (fuel : Nat) (input : A)
    (program : A → OracleComp spec B)
    (hprogram : R.machine.ImplementsWithin program fuel) :
    Run.value <$> run R H fuel input =
      some <$> simulateQ (fun i => Run.value <$> H i) (program input) := by
  simp only [run, bind_pure_comp, Functor.map_map]
  rw [runFrom_erase, denoteFrom_eq_runWith]
  exact hprogram.simulateQ_run_eq _ input

variable {J L S : Type} {target : OracleSpec J} {source : OracleSpec L}

/-- General callers preserve per-handler domination, including state invariants
and amortized potentials. This theorem does not inspect arithmetic source code. -/
theorem runFrom_dominated
    (inv : S → Prop) (potential : S → Int)
    (implementation : Handler (spec := spec) (StateT S (OracleComp target)))
    (reference : Handler (spec := spec) (OracleComp source))
    (hhandler : ∀ i, DominatedBy inv potential (implementation i) (reference i))
    (fuel : Nat) (state : R.machine.State) :
    DominatedBy inv potential (runFrom R implementation fuel state)
      (runFrom R reference fuel state) := by
  induction fuel generalizing state with
  | zero =>
      intro s hs z hz
      simp only [runFrom, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      exact ⟨hs, _, by simp [runFrom], rfl, le_rfl⟩
  | succ fuel ih =>
      cases hv : R.machine.view state with
      | inl result =>
          intro s hs z hz
          simp only [runFrom, hv, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst z
          exact ⟨hs, _, by simp [runFrom, hv], rfl, le_rfl⟩
      | inr request =>
          rcases request with ⟨i, next⟩
          intro s hs z hz
          simp only [runFrom, hv, StateT.run_bind, StateT.run_pure,
            mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
          obtain ⟨⟨answer, s₁⟩, ha, ⟨rest, s₂⟩, hr, rfl⟩ := hz
          obtain ⟨hs₁, answer', ha', hva, hca⟩ := hhandler i s hs (answer, s₁) ha
          obtain ⟨hs₂, rest', hr', hvr, hcr⟩ := ih (next answer.value) s₁ hs₁ (rest, s₂) hr
          refine ⟨hs₂, ⟨rest'.value, Q.cost R.headCode state + answer'.steps +
            Q.cost R.updateCode (state, ⟨i, answer'.value⟩) + rest'.steps + 2⟩,
            ?_, hvr, ?_⟩
          · simp only [runFrom, hv, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
            exact ⟨answer', ha', rest', by simpa [hva] using hr', rfl⟩
          · dsimp at hca hcr ⊢
            rw [hva]
            push_cast
            omega

theorem run_dominated
    (inv : S → Prop) (potential : S → Int)
    (implementation : Handler (spec := spec) (StateT S (OracleComp target)))
    (reference : Handler (spec := spec) (OracleComp source))
    (hhandler : ∀ i, DominatedBy inv potential (implementation i) (reference i))
    (fuel : Nat) (input : A) :
    DominatedBy inv potential (run R implementation fuel input)
      (run R reference fuel input) := by
  intro s hs z hz
  simp only [run, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨⟨result, s'⟩, hr, rfl⟩ := hz
  obtain ⟨hs', result', hr', hv, hc⟩ :=
    runFrom_dominated R inv potential implementation reference hhandler fuel
      (R.machine.init input) s hs (result, s') hr
  refine ⟨hs', ⟨result'.value, Q.cost R.initCode input + result'.steps + 1⟩,
    ?_, hv, ?_⟩
  · simp only [run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
    exact ⟨result', hr', rfl⟩
  · dsimp at hc ⊢
    omega

end Signatures.Runtime.GeneralCaller
