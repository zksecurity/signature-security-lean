import Proofs.Schnorr.CaliperAGMSource
import Proofs.Schnorr.CaliperAGM
import Lean.Util.CollectAxioms

/-! Rejected source replies stop immediately; represented replies preserve the
local transition. The public constructor must derive the AGM source, machine,
correspondence and complete-reduction witness from local contracts. -/
namespace SignaturesTest.CaliperPartialCaller
open OracleComp OracleSpec Signatures.Runtime.CaliperBackend

private def spec : OracleSpec Bool := fun _ => Bool
private def decode (_ : Bool) (answer : Bool) : Option Bool := if answer then some answer else none
private def advance (_ : Unit × Bool) : Bool ⊕ (Bool × Unit) := .inl false
private def initial (q : Bool) : Bool ⊕ (Bool × Unit) := .inr (q, ())

-- The fallback differs from the local result, so continuing on a rejected
-- reply would change the observable result of this example.
example : PartialCaller.next (spec := spec) id decode advance true false () false = .inl true := rfl
example : PartialCaller.next (spec := spec) id decode advance true false () true = .inl false := rfl

private theorem source_eq (q : Bool) :
    PartialCaller.source (spec := spec) id decode advance true 1 (initial q) =
      queryBind q (fun answer => pure (!answer)) := by
  change queryBind q _ = queryBind q _
  congr 1
  funext answer
  cases answer <;> rfl

private theorem bounded (q : Bool) :
    PartialCaller.QueryBound (spec := spec) id decode advance (fun _ => True) 1 1 (initial q) := by
  exact ⟨Or.inr (by decide), fun _ _ _ => trivial⟩

private theorem terminates (q : Bool) :
    PartialCaller.Terminates (spec := spec) id decode advance 1 (initial q) :=
  PartialCaller.QueryBound.terminates _ _ _ _ (bounded q)

example (q : Bool) :
    (PartialCaller.machine (spec := spec) id decode advance true initial).unroll 1 (initial q) =
      some <$> queryBind q (fun answer => pure (!answer)) := by
  rw [PartialCaller.unroll_eq_source _ _ _ _ _ _ _ (terminates q), source_eq]

example (q : Bool) :
    IsQueryBoundP (queryBind q (fun answer => pure (!answer)) : OracleComp spec Bool) (fun _ => True) 1 := by
  rw [← source_eq]
  exact PartialCaller.QueryBound.source _ _ _ _ _ (bounded q)

-- A default source equation at zero fuel is not a termination certificate.
example (q : Bool) :
    ¬ PartialCaller.Terminates (spec := spec) id decode advance 0 (initial q) := by
  simp [PartialCaller.Terminates, initial]

-- An uncounted call still needs fuel. A counted call still needs allowance.
example (q : Bool) :
    ¬ PartialCaller.QueryBound (spec := spec) id decode advance (fun _ => False) 0 0 (initial q) := by
  simp [PartialCaller.QueryBound, initial]
example (q : Bool) :
    ¬ PartialCaller.QueryBound (spec := spec) id decode advance (fun _ => True) 1 0 (initial q) := by
  simp [PartialCaller.QueryBound, initial]

-- A nonempty result follows without assuming one when every request admits
-- some represented reply. Schnorr derives this availability from zero replies.
example {I Q R C B : Type} {oracle : OracleSpec I} (query : Q → I)
    (reply : (q : Q) → oracle.Range (query q) → Option R)
    (step : C × R → B ⊕ (Q × C))
    (available : ∀ q, ∃ answer value, reply q answer = some value)
    (fuel : Nat) (head : B ⊕ (Q × C))
    (stops : PartialCaller.Terminates query reply step fuel head) : Nonempty B :=
  PartialCaller.Terminates.nonempty_result _ _ _ available stops

section SchnorrConstructor
open Caliper Signatures.Runtime BoundedSource
variable {F G M : Type} [Field F] [SampleableType F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [DecidableEq M]
    {queries : Schnorr.QueryAllowance} {generator : G}
    (P : Schnorr.CaliperAGM.Parameters F G M queries generator)
    (caller : SchnorrAGM.Full.Caller P.layout)
    (allowances : Schnorr.CaliperAGM.LocalQueries P caller)
    (resources : SchnorrAGM.Full.Caller.Bounds P.layout caller P.callerLimits)
    (algebraic : Schnorr.CaliperAGM.LocalAlgebraic P caller)

private noncomputable def constructed :=
  Schnorr.CaliperAGM.AlgebraicAdversary.ofLocalCaller P caller allowances resources algebraic

example : (constructed P caller allowances resources algebraic).caller = caller := rfl

example (input : P.layout.service.scheme.config.Value) :
    (constructed P caller allowances resources algebraic).source.main
      (Schnorr.AGM.initial input.val.1 input.val.2) =
      (fun output => SchnorrAGM.Native.Interface.decodeForgery output.val) <$>
        PartialCaller.source (SchnorrAGM.CallerHandler.query P.layout.service)
          (SchnorrAGM.CallerHandler.decodeReply P.layout.service) caller.advance
          (allowances.fallback P caller) queries.total (caller.initial input) :=
  SchnorrAGM.Full.Caller.Partial.main_initial P.layout caller (allowances.fallback P caller) queries.total input

example (input : P.layout.service.scheme.config.Value) :
    SchnorrAGM.Full.Caller.Partial.representInput P.layout
      (Schnorr.AGM.initial input.val.1 input.val.2) = some input :=
  SchnorrAGM.Full.Caller.Partial.representInput_initial P.layout input

example (basis : AlgebraicGroupModel.Interaction.Groups (Schnorr.AGM.Group G)) :
    (SchnorrAGM.Native.Interface.decodeForgery (allowances.fallback P caller).val).Valid basis :=
  allowances.fallback_valid P caller basis

-- Source synthesis feeds the existing actual-code, time, stored-program and
-- total-memory theorem, not just the query-count theorem.
private theorem reduction_within :
    P.within P.solverTime
      (Signatures.Runtime.SchnorrAGM.dlogReduction (constructed P caller allowances resources algebraic).source) :=
  Schnorr.CaliperAGM.reduction_within P (constructed P caller allowances resources algebraic)

private theorem security [Fintype F] (generates : Function.Injective (fun scalar : F => scalar • generator)) :
    𝒟[Schnorr.AGM.game generator (constructed P caller allowances resources algebraic).source] {true} ≤
      P.dlogBound P.solverTime +
        (queries.hash + 1 : ENNReal) * (Fintype.card F : ENNReal)⁻¹ +
        (queries.sign : ENNReal) * (queries.sign + queries.hash) * (Fintype.card F : ENNReal)⁻¹ :=
  Schnorr.CaliperAGM.security P (constructed P caller allowances resources algebraic) generates
end SchnorrConstructor

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``PartialCaller.unroll_eq_source, ``PartialCaller.implements,
      ``PartialCaller.Terminates.nonempty_result, ``PartialCaller.QueryBound.source,
      ``SchnorrAGM.CallerHandler.defaultReply_represented, ``SchnorrAGM.CallerHandler.decodeReply_eq_some,
      ``SchnorrAGM.CallerHandler.decodeReply_available, ``SchnorrAGM.Full.Caller.Partial.invariant,
      ``SchnorrAGM.Full.Caller.Partial.correspondence, ``SchnorrAGM.Full.Caller.Partial.blank_valid,
      ``SchnorrAGM.Full.Caller.Partial.source_algebraic, ``SchnorrAGM.Full.Caller.Partial.representInput_eq_some,
      ``SchnorrAGM.Full.Caller.Partial.main_initial, ``SchnorrAGM.Full.Caller.Partial.adversary,
      ``SchnorrAGM.Full.Caller.Partial.main_queryBound, ``Schnorr.CaliperAGM.LocalQueries.fallback_valid,
      ``Schnorr.CaliperAGM.AlgebraicAdversary.ofLocalCaller, ``source_eq, ``reduction_within, ``security] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  let constructor := (← getConstInfo ``Schnorr.CaliperAGM.AlgebraicAdversary.ofLocalCaller).type
  forallTelescope constructor fun params _ => do
    for param in params do
      let premise ← inferType param
      for forbidden in #[``OracleMachine, ``OracleComp, ``Schnorr.AGM.Adversary,
          ``AlgebraicGroupModel.Interaction.Adversary, ``SchnorrAGM.Full.Caller.Source,
          ``SchnorrAGM.Full.Caller.Invariant, ``Interactive.Within, ``cyclicDLogWithin] do
        if (premise.find? (fun expression => expression.isConstOf forbidden)).isSome then
          throwError "local caller constructor assumes a derived source/reduction certificate: {forbidden}"
  for required in #[``Schnorr.CaliperAGM.LocalQueries, ``Schnorr.CaliperAGM.LocalAlgebraic,
      ``SchnorrAGM.Full.Caller.Bounds] do
    unless (constructor.find? (fun expression => expression.isConstOf required)).isSome do
      throwError "local caller constructor omits local obligation {required}"
  let body := (← getConstInfo ``Schnorr.CaliperAGM.AlgebraicAdversary.ofLocalCaller).value?.get!
  for required in #[``SchnorrAGM.Full.Caller.Partial.adversary,
      ``SchnorrAGM.Full.Caller.Partial.correspondence] do
    unless (body.find? (fun expression => expression.isConstOf required)).isSome do
      throwError "local caller constructor must derive {required}"

end SignaturesTest.CaliperPartialCaller
