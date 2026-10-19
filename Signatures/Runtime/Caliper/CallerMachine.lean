import Signatures.Runtime.Caliper.CallerControlRefinement
import VCVio.OracleComp.Coinductive.Machine

/-! Link the generated caller's source semantics to an arbitrary original
OracleMachine. Source states and private stores can be unbounded mathematical
types: their bounded represented counterparts use explicit views. The local
caller transition must match the original machine's next view, and the handler
must match the original typed reply and private store jointly. No completed
controller equivalence or efficiency is assumed. -/

namespace Signatures.Runtime.CaliperBackend.CallerMachine
open Caliper OracleComp OracleSpec CallerControl
open PFunctor.DynSystem.DynComputation

variable {C Q R B S A T I J : Type} {source : OracleSpec I} {target : OracleSpec J}
    (machine : OracleMachine source A B) (query : Q → I) (state : C → machine.State)

/-- The represented caller packet is the original machine's current head.
Pending packets retain the original machine state, rather than a host callback. -/
inductive Matches : (B ⊕ (Q × C)) → machine.State → Prop where
  | returned (value : B) (current : machine.State) (view : machine.view current = .inl value) :
      Matches (.inl value) current
  | pending (position : Q) (current : C) (next : source.Range (query position) → machine.State)
      (view : machine.view (state current) = .inr ⟨query position, next⟩) :
      Matches (.inr (position, current)) (state current)

variable (stored : S → T) (replyMatches : (q : Q) → R → source.Range (query q) → Prop)

def replyRelation (q : Q) (represented : R × S) (original : source.Range (query q) × T) : Prop :=
  replyMatches q represented.1 original.1 ∧ stored represented.2 = original.2

def observe (value : Packet C Q B S) : Option B × T :=
  ((answer value).1, stored value.2)

variable (advance : C × R → B ⊕ (Q × C)) (H : Q × S → OracleComp target (R × S))
    (original : QueryImpl source (StateT T (OracleComp target)))
    (invariant : Nat → Frame C Q S → Prop)
    (handlerMatches : ∀ remaining value, invariant (remaining + 1) value →
      Synchronizes (replyRelation query stored replyMatches value.1.1)
        (H (value.1.1, value.2)) ((original (query value.1.1)).run (stored value.2)))
    (advanceMatches : ∀ remaining q c saved, invariant (remaining + 1) ((q, c), saved) →
      ∀ next : source.Range (query q) → machine.State,
        machine.view (state c) = .inr ⟨query q, next⟩ →
        ∀ reply originalReply, replyMatches q reply originalReply →
          Matches machine query state (advance (c, reply)) (next originalReply))
    (preserves : ∀ remaining value, invariant (remaining + 1) value →
      ∀ reply ∈ support (H (value.1.1, value.2)), Valid invariant remaining (advance (value.1.2, reply.1), reply.2))

include handlerMatches advanceMatches preserves in
theorem start_synchronizes (fuel : Nat) (value : Packet C Q B S) (current : machine.State)
    (valid : Valid invariant fuel value) (matched : Matches machine query state value.1 current) :
    Synchronizes (fun represented original => observe stored represented = original)
      (start advance H fuel value) ((machine.runWith original fuel current).run (stored value.2)) := by
  induction fuel generalizing value current with
  | zero =>
    rcases value with ⟨value, saved⟩
    cases matched with
    | returned value current view =>
      rw [machine.runWith_return original 0 current value view]
      exact .pure rfl
    | pending q c next view =>
      rw [machine.runWith_query_zero original (state c) (query q) next view]
      exact .pure rfl
  | succ fuel ih =>
    rcases value with ⟨value, saved⟩
    cases matched with
    | returned value current view =>
      rw [machine.runWith_return original (fuel + 1) current value view]
      exact .pure rfl
    | pending q c next view =>
      change Synchronizes _ (denote advance H (fuel + 1) ((q, c), saved)) _
      rw [denote_succ, machine.runWith_query_succ_stateT original fuel (state c) (query q) next view]
      apply (handlerMatches fuel ((q, c), saved) valid).with_support.bind
        (fun reply => start advance H fuel (advance (c, reply.1), reply.2))
        (fun reply => (machine.runWith original fuel (next reply.1)).run reply.2)
      intro reply originalReply related
      have nextValid := preserves fuel ((q, c), saved) valid reply related.2.1
      have nextMatches := advanceMatches fuel q c saved valid next view reply.1 originalReply.1 related.1.1
      have refined := ih (advance (c, reply.1), reply.2) (next originalReply.1) nextValid nextMatches
      simpa only [related.1.2] using refined

include handlerMatches advanceMatches preserves in
theorem start_eq_runWith (fuel : Nat) (value : Packet C Q B S) (current : machine.State)
    (valid : Valid invariant fuel value) (matched : Matches machine query state value.1 current) :
    observe stored <$> start advance H fuel value =
      (machine.runWith original fuel current).run (stored value.2) := by
  have synchronized := start_synchronizes machine query state stored replyMatches advance H original invariant
    handlerMatches advanceMatches preserves fuel value current valid matched
  simpa only [id_map] using synchronized.map_eq (observe stored) id (fun _ _ related => related)

include handlerMatches advanceMatches preserves in
/-- The original implementation certificate excludes cutoff and identifies the
actual source program, including the original oracle's final private store. -/
theorem start_eq_simulateQ (fuel : Nat) (value : Packet C Q B S) (input : A)
    (valid : Valid invariant fuel value) (matched : Matches machine query state value.1 (machine.init input))
    (program : A → OracleComp source B) (implements : machine.ImplementsWithin program fuel) :
    observe stored <$> start advance H fuel value =
      (fun result => (some result.1, result.2)) <$>
        (simulateQ original (program input)).run (stored value.2) := by
  rw [start_eq_runWith machine query state stored replyMatches advance H original invariant
    handlerMatches advanceMatches preserves fuel value (machine.init input) valid matched]
  change (machine.runWithInput original fuel input).run (stored value.2) = _
  rw [implements.simulateQ_run_eq original input]
  exact StateT.run_map _ _ _

end Signatures.Runtime.CaliperBackend.CallerMachine
