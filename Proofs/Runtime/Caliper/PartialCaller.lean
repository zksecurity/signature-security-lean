import Proofs.Runtime.Caliper.CallerPresentation
import Proofs.Runtime.Caliper.CallerQueryBounds

/-! A source presentation may stop on replies outside the represented interface.
Related replies take the exact local continuation. Termination and query bounds
are conditions on local transitions; zero-fuel pending calls remain excluded. -/
namespace Signatures.Runtime.CaliperBackend.PartialCaller
open OracleComp OracleSpec PFunctor.DynSystem.DynComputation
variable {C Q R B A I : Type} {spec : OracleSpec I}
    (query : Q → I) (reply : (q : Q) → spec.Range (query q) → Option R)
    (advance : C × R → B ⊕ (Q × C)) (fallback : B)

def next (q : Q) (state : C) (answer : spec.Range (query q)) : B ⊕ (Q × C) :=
  match reply q answer with | none => .inl fallback | some value => advance (state, value)

def source : Nat → B ⊕ (Q × C) → OracleComp spec B
  | _, .inl result => pure result
  | 0, .inr _ => pure fallback
  | fuel + 1, .inr (q, state) => queryBind (query q) (fun answer => source fuel (next query reply advance fallback q state answer))

def Terminates : Nat → B ⊕ (Q × C) → Prop
  | _, .inl _ => True
  | 0, .inr _ => False
  | fuel + 1, .inr (q, state) => ∀ answer, ∀ value, reply q answer = some value →
      Terminates fuel (advance (state, value))

variable (initial : A → B ⊕ (Q × C))
def machine : OracleMachine spec A B :=
  ofStep (fun head => match head with
    | .inl result => .inl result
    | .inr (q, state) => .inr ⟨query q, next query reply advance fallback q state⟩) initial

theorem head_matches (head : B ⊕ (Q × C)) :
    CallerMachine.Matches (machine query reply advance fallback initial) query Sum.inr head head := by
  cases head with
  | inl result => exact .returned result _ (by simp [machine])
  | inr pending =>
    exact .pending pending.1 pending.2 (next query reply advance fallback pending.1 pending.2)
      (by simp [machine])

theorem advance_matches (q : Q) (state : C)
    (continuation : spec.Range (query q) → (machine query reply advance fallback initial).State)
    (view : (machine query reply advance fallback initial).view (.inr (q, state)) = .inr ⟨query q, continuation⟩)
    (represented : R) (original : spec.Range (query q)) (decoded : reply q original = some represented) :
    CallerMachine.Matches (machine query reply advance fallback initial) query Sum.inr
      (advance (state, represented)) (continuation original) := by
  have canonical : (machine query reply advance fallback initial).view (.inr (q, state)) =
      .inr ⟨query q, next query reply advance fallback q state⟩ := by simp [machine]
  rw [(machine query reply advance fallback initial).next_eq_of_view_query view canonical]
  rw [next, decoded]
  exact head_matches query reply advance fallback initial (advance (state, represented))

theorem unroll_eq_source (fuel : Nat) (head : B ⊕ (Q × C))
    (terminates : Terminates query reply advance fuel head) :
    (machine query reply advance fallback initial).unroll fuel head =
      some <$> source query reply advance fallback fuel head := by
  induction fuel generalizing head with
  | zero =>
    cases head with
    | inl result => rfl
    | inr pending => exact False.elim terminates
  | succ fuel ih =>
    cases head with
    | inl result => rfl
    | inr pending =>
      change queryBind (query pending.1) (fun answer =>
        (machine query reply advance fallback initial).unroll fuel (next query reply advance fallback pending.1 pending.2 answer)) = _
      change queryBind (query pending.1) _ = queryBind (query pending.1) _
      congr 1
      funext answer
      cases decoded : reply pending.1 answer with
      | none => simp only [next, decoded]; cases fuel <;> rfl
      | some value =>
        simp only [next, decoded]
        exact ih (advance (pending.2, value)) (terminates answer value decoded)

theorem implements (fuel : Nat)
    (terminates : ∀ input, Terminates query reply advance fuel (initial input)) :
    (machine query reply advance fallback initial).ImplementsWithin
      (fun input => source query reply advance fallback fuel (initial input)) fuel :=
  fun input => unroll_eq_source query reply advance fallback initial fuel (initial input) (terminates input)

omit fallback initial in
theorem Terminates.nonempty_result (available : ∀ q, ∃ answer value, reply q answer = some value)
    {fuel : Nat} {head : B ⊕ (Q × C)} (terminates : Terminates query reply advance fuel head) : Nonempty B := by
  induction fuel generalizing head with
  | zero =>
    cases head with
    | inl result => exact ⟨result⟩
    | inr pending => exact False.elim terminates
  | succ fuel ih =>
    cases head with
    | inl result => exact ⟨result⟩
    | inr pending =>
      obtain ⟨answer, value, decoded⟩ := available pending.1
      exact ih (terminates answer value decoded)

variable (predicate : I → Prop) [DecidablePred predicate]
def QueryBound : Nat → Nat → B ⊕ (Q × C) → Prop
  | _, _, .inl _ => True
  | 0, _, .inr _ => False
  | fuel + 1, count, .inr (q, state) =>
      (¬ predicate (query q) ∨ 0 < count) ∧
        ∀ answer value, reply q answer = some value →
          QueryBound fuel (if predicate (query q) then count - 1 else count) (advance (state, value))

omit fallback initial in
theorem QueryBound.terminates {fuel count : Nat} {head : B ⊕ (Q × C)}
    (bounded : QueryBound query reply advance predicate fuel count head) :
    Terminates query reply advance fuel head := by
  induction fuel generalizing count head with
  | zero => cases head <;> exact bounded
  | succ fuel ih =>
    cases head with
    | inl _ => trivial
    | inr pending => exact fun answer value decoded => ih (bounded.2 answer value decoded)

omit initial in
theorem QueryBound.source {fuel count : Nat} {head : B ⊕ (Q × C)}
    (bounded : QueryBound query reply advance predicate fuel count head) :
    IsQueryBoundP (source query reply advance fallback fuel head) predicate count := by
  induction fuel generalizing count head with
  | zero =>
    cases head with
    | inl result => trivial
    | inr pending => exact False.elim bounded
  | succ fuel ih =>
    cases head with
    | inl result => trivial
    | inr pending =>
      refine ⟨bounded.1, ?_⟩
      intro answer
      change IsQueryBoundP (PartialCaller.source query reply advance fallback fuel
        (next query reply advance fallback pending.1 pending.2 answer)) predicate
          (if predicate (query pending.1) then count - 1 else count)
      cases decoded : reply pending.1 answer with
      | none => rw [next, decoded]; cases fuel <;> trivial
      | some value =>
        rw [next, decoded]
        exact ih (bounded.2 answer value decoded)

end Signatures.Runtime.CaliperBackend.PartialCaller
