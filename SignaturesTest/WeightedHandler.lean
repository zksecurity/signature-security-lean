import Proofs.Runtime.BackendWeightedHandlerBudget
import Proofs.Runtime.BackendWeightedHandlerDescription
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.WeightedAGM

namespace SignaturesTest.WeightedHandler

-- Both domains are infinite, and a signing message is not a hash index.
private abbrev Message := Nat × Bool
private abbrev Request := GeneralRequest Nat Message 3
private abbrev Spec := generalSpec Nat Message Nat 3
private abbrev Trace := List (Nat ⊕ Message)

example : generalKind (.inl (.inl 2) : Request) = 0 := rfl
example : generalKind (.inl (.inr 314159) : Request) = 1 := rfl
example : generalKind (.inr (314159, true) : Request) = 2 := rfl

example : generalSource (ι := Nat) (M := Message) (G₁ := Nat) 3 (.inl (.inr 314159)) =
    liftM ((Model.LazyAGM.advSpec Nat Message Nat).query (.inl (.inr 314159))) := rfl

example : generalSource (ι := Nat) (M := Message) (G₁ := Nat) 3 (.inr (314159, true)) =
    liftM ((Model.LazyAGM.advSpec Nat Message Nat).query (.inr (314159, true))) := rfl

example : generalSource (ι := Nat) (M := Message) (G₁ := Nat) 3 (.inl (.inl 3)) =
    liftM ((Model.LazyAGM.advSpec Nat Message Nat).query (.inl (.inl 3))) := rfl

private def hashValue (p : Nat × Trace) : Nat × Trace :=
  (p.1 + 1, p.2 ++ [.inl p.1])

private def signValue (p : Message × Trace) : Nat × Trace :=
  (if p.1.2 then p.1.1 else 0, p.2 ++ [.inr p.1])

section Compiled

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.IsDistributive]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase Nat Nat Nat Nat Bool))
  (bd : Boundary C Spec.toPFunctor Unit Nat)
  (ports : NativePorts (Q := Q) rep key (.pair key message) bd)
  (sampler : BoundedSampler rep key (.pair key message) bd ports (iface := iface))
  (store : C.Str Trace)
  (hashCode : Q.Realizer (StepClass.HasProd.prod (rep.ty key) store)
    (StepClass.HasProd.prod (rep.ty point₁) store) hashValue)
  (signCode : Q.Realizer (StepClass.HasProd.prod (rep.ty (.pair key message)) store)
    (StepClass.HasProd.prod (rep.ty point₁) store) signValue)

-- The compiled hash branch tags the original request and retains existing state.
example : (NativeHandler.code rep key (.pair key message) bd ports sampler store
    (.atomic hashCode) (.atomic signCode)).denote (.inl (.inr 7), [.inr (99, false)]) =
      pure (tagHash (M := Message) (randomBound := 3) (7, 8), [.inr (99, false), .inl 7]) := by
  rw [NativeHandler.code_denote]
  simp only [NativeHandler.source, StateT.run, Code.denote]
  rfl

-- A zero result still records the exact structured signing message.
example : (NativeHandler.code rep key (.pair key message) bd ports sampler store
    (.atomic hashCode) (.atomic signCode)).denote (.inr (7, false), [.inl 99]) =
      pure (tagSign (ι := Nat) (randomBound := 3) ((7, false), 0), [.inl 99, .inr (7, false)]) := by
  rw [NativeHandler.code_denote]
  simp only [NativeHandler.source, StateT.run, Code.denote]
  rfl

-- The signing query depends on a prior hash reply; a later hash depends on the
-- signing reply. The complete trace is checked, not just the final result.
private def adaptive : OracleComp Spec Nat := do
  let h ← Spec.query (.inl (.inr 7))
  let s ← Spec.query (.inr (h, true))
  Spec.query (.inl (.inr s))

example : (simulateQ (NativeHandler.source (iface := iface) rep key (.pair key message) store
    (.atomic hashCode) (.atomic signCode)) adaptive).run [.inr (99, false)] =
      pure (9, [.inr (99, false), .inl 7, .inr (8, true), .inl 8]) := by
  simp only [adaptive, simulateQ_bind, simulateQ_spec_query, NativeHandler.source, Code.denote]
  rfl

variable [C.HasOption] [Q.HasOption] [OptionCode (Q := Q)]
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

-- Exhaustion before an unanswered query preserves the store and returns none.
example (i : Request) (next : Spec.Range i → R.machine.State)
    (hv : R.machine.view (R.machine.init ()) = .inr ⟨i, next⟩) (saved : Trace) :
    (NativeHandler.caller rep key (.pair key message) bd ports sampler store
      (.atomic hashCode) (.atomic signCode) R 0).denote ((), saved) = pure (none, saved) := by
  simp only [NativeHandler.caller, Caller.program, Caller.fromState, Code.denote, map_pure, pure_bind]
  exact Caller.stop_query R store (R.machine.init ()) saved i next hv

-- Adaptive source composition uses the actual native dispatcher and arbitrary
-- realized caller. Termination is supplied by the general machine interface.
example (fuel : Nat) (hprogram : R.machine.ImplementsWithin (fun _ => adaptive) fuel)
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat) :
    Run.value <$> (NativeHandler.caller rep key (.pair key message) bd ports sampler store
      (.atomic hashCode) (.atomic signCode) R fuel).run control queryCost ((), []) =
        pure (some 9, [.inl 7, .inr (8, true), .inl 8]) := by
  rw [NativeHandler.caller_erase rep key (.pair key message) bd ports sampler store
    (.atomic hashCode) (.atomic signCode) control queryCost R fuel (fun _ => adaptive) hprogram]
  simp only [adaptive, simulateQ_bind, simulateQ_spec_query, NativeHandler.source,
    StateT.run_map, Code.denote]
  rfl

end Compiled

open Lean Meta

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``NativeHandler.group_denote, ``NativeHandler.random_denote,
      ``NativeHandler.code_denote, ``NativeHandler.code_executed_run, ``NativeHandler.executed_erase,
      ``NativeHandler.caller_denote, ``NativeHandler.caller_erase,
      ``NativeHandler.request_size, ``NativeHandler.random_bound, ``NativeHandler.group_bound,
      ``NativeHandler.code_bound, ``NativeHandler.group_description,
      ``NativeHandler.random_description, ``NativeHandler.code_description,
      ``NativeHandler.caller_description] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: finite hash-index or signing-message domain required"
        for forbidden in #[``NativeHandler.code, ``NativeHandler.caller,
            ``GeneralCaller.Budget] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: supplied completed-dispatcher/caller certificate"

end SignaturesTest.WeightedHandler
