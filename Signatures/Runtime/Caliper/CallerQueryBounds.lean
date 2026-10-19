import Signatures.Runtime.Caliper.CallerPresentation
import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-! Query allowances proved directly on local caller transitions transfer to
the constructed source tree. Every reply branch must terminate; a truncated
pending caller cannot satisfy these bounds just by exhausting its fuel. -/
namespace Signatures.Runtime.CaliperBackend.CallerMachine
open OracleComp OracleSpec PFunctor.DynSystem.DynComputation
variable {C Q R B A I : Type} {spec : OracleSpec I}
    (query : Q → I) (reply : (q : Q) → spec.Range (query q) → R)
    (advance : C × R → B ⊕ (Q × C)) (predicate : I → Prop) [DecidablePred predicate]

def QueryBound : Nat → Nat → B ⊕ (Q × C) → Prop
  | _, _, .inl _ => True
  | 0, _, .inr _ => False
  | fuel + 1, count, .inr (q, c) =>
      (¬ predicate (query q) ∨ 0 < count) ∧
        ∀ answer, QueryBound fuel (if predicate (query q) then count - 1 else count)
          (advance (c, reply q answer))

theorem QueryBound.terminates {fuel count : Nat} {head : B ⊕ (Q × C)}
    (bounded : QueryBound query reply advance predicate fuel count head) :
    Terminates query reply advance fuel head := by
  induction fuel generalizing count head with
  | zero => cases head <;> exact bounded
  | succ fuel ih =>
      cases head with
      | inl _ => trivial
      | inr pending => exact fun answer => ih (bounded.2 answer)

variable (initial : A → B ⊕ (Q × C))
theorem QueryBound.unroll {fuel count : Nat} {head : B ⊕ (Q × C)}
    (bounded : QueryBound query reply advance predicate fuel count head) :
    IsQueryBoundP ((ofCaller query reply advance initial).unroll fuel head) predicate count := by
  induction fuel generalizing count head with
  | zero =>
      cases head with
      | inl _ => trivial
      | inr _ => exact False.elim bounded
  | succ fuel ih =>
      cases head with
      | inl _ => trivial
      | inr pending => exact ⟨bounded.1, fun answer => ih (bounded.2 answer)⟩

variable (fuel : Nat) (terminates : ∀ input, Terminates query reply advance fuel (initial input))
include terminates in
theorem sourceOfCaller_queryBound (count : Nat)
    (bounded : ∀ input, QueryBound query reply advance predicate fuel count (initial input)) (input : A) :
    IsQueryBoundP (sourceOfCaller query reply advance initial fuel terminates input) predicate count := by
  have implemented := ofCaller_implements query reply advance initial fuel terminates input
  change (ofCaller query reply advance initial).run fuel input =
    some <$> sourceOfCaller query reply advance initial fuel terminates input at implemented
  apply (isQueryBoundP_map_iff _ some count).mp
  rw [← implemented]
  exact QueryBound.unroll query reply advance predicate initial (bounded input)

end Signatures.Runtime.CaliperBackend.CallerMachine
