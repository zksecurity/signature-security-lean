import Proofs.Runtime.Caliper.SchnorrAGMLocalAlgebraic

/-! Construct the shared AGM adversary from local Caliper caller transitions.
Represented initial inputs and replies keep their exact continuations. Other
inputs and replies return a universally algebraic fallback only in the source
extension; the implemented handler never takes those branches. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Full.Caller.Partial
open Caliper OracleComp OracleSpec AlgebraicGroupModel.Interaction
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS randomBound : Nat} {M F G A : Type}
    (layout : CallerExtraction.Layouts w M F G qH qS randomBound A)

theorem initial_injective (first second : layout.service.scheme.config.Value)
    (equal : _root_.Schnorr.AGM.initial first.val.1 first.val.2 =
      _root_.Schnorr.AGM.initial second.val.1 second.val.2) : first = second := by
  apply Subtype.ext
  have points := congrArg (fun input => input.groups ()) equal
  change [first.val.1, first.val.2] = [second.val.1, second.val.2] at points
  exact Prod.ext (List.cons.inj points).1 (List.cons.inj (List.cons.inj points).2).1

noncomputable def representInput (input : Message Unit (_root_.Schnorr.AGM.Group G)) :
    Option layout.service.scheme.config.Value := by
  classical
  exact if represented : ∃ value : layout.service.scheme.config.Value,
      input = _root_.Schnorr.AGM.initial value.val.1 value.val.2
    then some represented.choose else none

theorem representInput_eq_some (input : Message Unit (_root_.Schnorr.AGM.Group G))
    (value : layout.service.scheme.config.Value) :
    representInput layout input = some value ↔
      input = _root_.Schnorr.AGM.initial value.val.1 value.val.2 := by
  classical
  unfold representInput
  split
  · rename_i available
    constructor
    · intro equal
      obtain rfl := Option.some.inj equal
      exact available.choose_spec
    · intro equal
      exact congrArg some (initial_injective layout _ _ (available.choose_spec.symm.trans equal))
  · rename_i missing
    constructor
    · intro equal
      cases equal
    · intro equal
      exact (missing ⟨value, equal⟩).elim

theorem representInput_initial (value : layout.service.scheme.config.Value) :
    representInput layout (_root_.Schnorr.AGM.initial value.val.1 value.val.2) = some value :=
  (representInput_eq_some layout _ value).mpr rfl

variable (caller : Caller layout) (fallback : layout.forgery.Value) (fuel : Nat)

noncomputable def main (input : Message Unit (_root_.Schnorr.AGM.Group G)) :
    OracleComp (Interface.sourceSpec F G M) (Explained F (M × F) (_root_.Schnorr.AGM.Group G)) :=
  match representInput layout input with
  | none => pure (Interface.decodeForgery fallback.val)
  | some value => (fun output => Interface.decodeForgery output.val) <$>
      PartialCaller.source (CallerHandler.query layout.service) (CallerHandler.decodeReply layout.service)
        caller.advance fallback fuel (caller.initial value)

theorem main_initial (value : layout.service.scheme.config.Value) :
    main layout caller fallback fuel (_root_.Schnorr.AGM.initial value.val.1 value.val.2) =
      (fun output => Interface.decodeForgery output.val) <$>
        PartialCaller.source (CallerHandler.query layout.service) (CallerHandler.decodeReply layout.service)
          caller.advance fallback fuel (caller.initial value) := by
  simp only [main, representInput_initial]

section Algebraic
variable [Zero F] [AddMonoid G] [SMul F G]
    (fallbackValid : ∀ basis, (Interface.decodeForgery fallback.val).Valid basis)
    (algebraic : ∀ value, LocallyAlgebraic layout caller fuel
      (_root_.Schnorr.AGM.initial value.val.1 value.val.2).groups (caller.initial value))

include fallbackValid algebraic in
theorem main_algebraic (input : Message Unit (_root_.Schnorr.AGM.Group G)) :
    IsAlgebraic input.groups (main layout caller fallback fuel input) := by
  unfold main
  cases decoded : representInput layout input with
  | none => exact fallbackValid _
  | some value =>
    rw [(representInput_eq_some layout input value).mp decoded]
    exact source_algebraic layout caller fallback fallbackValid fuel _ _ (algebraic value)

noncomputable def adversary : _root_.Schnorr.AGM.Adversary F G M where
  main := main layout caller fallback fuel
  algebraic := main_algebraic layout caller fallback fuel fallbackValid algebraic
end Algebraic

theorem main_queryBound (predicate : Interface.SourceRequest F G M → Prop) [DecidablePred predicate]
    (count : Nat) (bounded : QueryBound layout caller predicate count fuel)
    (input : Message Unit (_root_.Schnorr.AGM.Group G)) :
    IsQueryBoundP (main layout caller fallback fuel input) predicate count := by
  unfold main
  cases representInput layout input with
  | none => trivial
  | some value =>
    apply (isQueryBoundP_map_iff _ _ count).mpr
    exact PartialCaller.QueryBound.source _ _ _ _ _ (bounded value)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Full.Caller.Partial
