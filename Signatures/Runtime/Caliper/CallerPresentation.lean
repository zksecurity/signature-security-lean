import Signatures.Runtime.Caliper.CallerMachine

/-! Construct the oracle-machine presentation from a caller's local transitions.
The pending request is already part of the controller packet; the private state
need not redundantly encode it. Reply representation is an interface conversion,
not an uncharged instruction available to the caller. Local Caliper realizers
and their resource bounds are supplied separately by the execution layer. -/
namespace Signatures.Runtime.CaliperBackend.CallerMachine
open OracleComp OracleSpec PFunctor.DynSystem.DynComputation

variable {C Q R B A I : Type} {spec : OracleSpec I}
    (query : Q → I) (reply : (q : Q) → spec.Range (query q) → R)
    (advance : C × R → B ⊕ (Q × C)) (initial : A → B ⊕ (Q × C))

/-- The machine's state is exactly the caller's returned/pending packet. -/
def ofCaller : OracleMachine spec A B :=
  ofStep (fun head => match head with
    | .inl result => .inl result
    | .inr (q, c) => .inr ⟨query q, fun answer => advance (c, reply q answer)⟩) initial

theorem ofCaller_matches (head : B ⊕ (Q × C)) :
    Matches (ofCaller query reply advance initial) query Sum.inr head head := by
  cases head with
  | inl result =>
      apply Matches.returned
      simp [ofCaller]
  | inr pending =>
      exact .pending pending.1 pending.2
        (fun answer => advance (pending.2, reply pending.1 answer)) (by simp [ofCaller])

/-- Local head correspondence follows from the reply conversion alone. -/
theorem ofCaller_advance (q : Q) (c : C)
    (next : spec.Range (query q) → (ofCaller query reply advance initial).State)
    (view : (ofCaller query reply advance initial).view (.inr (q, c)) = .inr ⟨query q, next⟩)
    (represented : R) (original : spec.Range (query q))
    (equal : represented = reply q original) :
    Matches (ofCaller query reply advance initial) query Sum.inr
      (advance (c, represented)) (next original) := by
  have canonical : (ofCaller query reply advance initial).view (.inr (q, c)) =
      .inr ⟨query q, fun answer => advance (c, reply q answer)⟩ := by simp [ofCaller]
  rw [(ofCaller query reply advance initial).next_eq_of_view_query view canonical, equal]
  exact ofCaller_matches query reply advance initial _

/-- Every possible sequence of replies reaches a return before exhausting the
query allowance. Zero fuel permits a return, but not a pending request. -/
def Terminates : Nat → B ⊕ (Q × C) → Prop
  | _, .inl _ => True
  | 0, .inr _ => False
  | fuel + 1, .inr (q, c) => ∀ answer, Terminates fuel (advance (c, reply q answer))

theorem terminates_iff_resolvesIn (fuel : Nat) (head : B ⊕ (Q × C)) :
    Terminates query reply advance fuel head ↔
      (ofCaller query reply advance initial).ResolvesIn fuel head := by
  induction fuel generalizing head with
  | zero => cases head <;> simp [Terminates, ResolvesIn, ofCaller]
  | succ fuel ih =>
    cases head with
    | inl result => simp [Terminates, ResolvesIn, ofCaller]
    | inr pending => simpa only [Terminates, ResolvesIn, ofCaller, view_ofStep] using
        (forall_congr' fun answer => ih (advance (pending.2, reply pending.1 answer)))

variable (fuel : Nat)
    (terminates : ∀ input, Terminates query reply advance fuel (initial input))

/-- The finite source tree is derived from the caller and its local termination
proof. Choice assembles mathematical trees; it is not part of the emitted code. -/
noncomputable def sourceOfCaller : A → OracleComp spec B := fun input =>
  (unroll_eq_map_some_of_resolvesIn
    ((terminates_iff_resolvesIn query reply advance initial fuel (initial input)).mp
      (terminates input))).choose

theorem ofCaller_implements :
    (ofCaller query reply advance initial).ImplementsWithin
      (sourceOfCaller query reply advance initial fuel terminates) fuel := fun input =>
  (unroll_eq_map_some_of_resolvesIn
    ((terminates_iff_resolvesIn query reply advance initial fuel (initial input)).mp
      (terminates input))).choose_spec

end Signatures.Runtime.CaliperBackend.CallerMachine
