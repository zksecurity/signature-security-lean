import Signatures.Runtime.BackendSchnorrROMSelectionPolynomial
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Native replay selection: chronological live entries, final-query allowance,
failed verification, cutoff, and defined behavior on every result list. -/

open PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr ListROM

namespace SignaturesTest.SchnorrROMSelection

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5
private abbrev Output := cachePassOutput.Value (cryptoBase F F F Nat Nat)
private abbrev Cache := List ((Nat × F) × F)

private def completed (live : Cache) (response : F := 2) : Output :=
  (((7, 3, response), 2), ((1, 2), [((7, 3), 4)], live))

private def execute (cost : PrimitiveCosts) (qH : Nat) (xs : List Output) : Bool × Nat :=
  (NativeSelection.expression qH).denote (arithmetic F F F Nat Nat cost) (xs, ())

/-- Empty/cutoff results reject without supplying a message inhabitant. -/
example (cost : PrimitiveCosts) : execute cost 10 [] = (false, 0) := by
  rw [execute, NativeSelection.expression_denote]
  rfl

/-- The final verification query is a valid selection even with no attacker hash calls. -/
example (cost : PrimitiveCosts) : execute cost 0 [completed [((7, 3), 2)]] = (true, 0) := by
  rw [execute, NativeSelection.expression_denote]
  decide

/-- Newest-first cache order must be reversed before assigning the replay ordinal. -/
example (cost : PrimitiveCosts) : execute cost 1 [completed [((7, 3), 2), ((9, 4), 1)]] = (true, 1) := by
  rw [execute, NativeSelection.expression_denote]
  decide

/-- The same successful forgery rejects when its ordinal exceeds the public allowance. -/
example (cost : PrimitiveCosts) : execute cost 0 [completed [((7, 3), 2), ((9, 4), 1)]] = (false, 0) := by
  rw [execute, NativeSelection.expression_denote]
  decide

/-- A managed-cache hit cannot substitute for a missing live-cache entry. -/
example (cost : PrimitiveCosts) : execute cost 2 [completed [((9, 4), 1)]] = (false, 0) := by
  rw [execute, NativeSelection.expression_denote]
  decide

/-- Finding the right key does not bypass the signature equation. -/
example (cost : PrimitiveCosts) : execute cost 2 [completed [((7, 3), 2)] 0] = (false, 0) := by
  rw [execute, NativeSelection.expression_denote]
  decide

/-- On duplicate keys, use the earliest chronological occurrence. -/
example (cost : PrimitiveCosts) :
    execute cost 0 [completed [((7, 3), 2), ((9, 4), 1), ((7, 3), 0)]] = (true, 0) := by
  rw [execute, NativeSelection.expression_denote]
  decide

/-- Malformed multi-result lists have explicit last-result behavior. -/
example (cost : PrimitiveCosts) :
    execute cost 2 [completed [((7, 3), 2)], completed [((7, 3), 2)] 0] = (false, 0) := by
  rw [execute, NativeSelection.expression_denote]
  decide

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``NativeSelection.verifyExpression_denote, ``NativeSelection.indexExpression_denote,
      ``NativeSelection.guardExpression_denote, ``NativeSelection.oneExpression_denote,
      ``NativeSelection.expression_denote, ``NativeSelection.oneValue_selectionRun,
      ``NativeSelection.source_singleton, ``NativeSelection.value_source, ``NativeSelection.value_index_le,
      ``NativeSelection.findStep_count, ``NativeSelection.findStep_fold_count,
      ``NativeSelection.liveIndexBody_time, ``NativeSelection.liveIndexFold_time,
      ``NativeSelection.liveIndex_time, ``NativeSelection.liveIndex_cost,
      ``NativeSelection.selector_description, ``NativeSelection.indexTime_polynomial,
      ``NativeSelection.description_polynomial, ``NativeSelection.verifyExpression_time,
      ``NativeSelection.guardExpression_time, ``NativeSelection.indexExpressionWith_time,
      ``NativeSelection.oneExpressionWith_time, ``NativeSelection.choice_size,
      ``NativeSelection.oneValue_index_le, ``NativeSelection.oneExpression_time,
      ``NativeSelection.selector_cost, ``NativeSelection.timeBudget_polynomial] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``NativeSelection.source_singleton, ``NativeSelection.value_source,
      ``NativeSelection.value_index_le, ``NativeSelection.liveIndex_time, ``NativeSelection.liveIndex_cost,
      ``NativeSelection.selector_description] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[``Bounds, ``GeneralCaller.Budget, ``Program, ``SourceCertificate,
            ``Fintype, ``Finite, ``Inhabited, ``Expression.compile, ``Expression.compileBound] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: do not assume a completed component budget, restricted attacker or finite/default message"
        let userName := (← getFVarLocalDecl param).userName
        if #[`domainSize, `valid, `hselector, `hscan, `hreverse].contains userName then
          throwError "{name}: discharge scan/reversal costs and preserve source scope"
  forallTelescope (← getConstInfo ``NativeSelection.liveIndex_cost).type fun _ conclusion => do
    unless (conclusion.find? (fun e => e.isConstOf ``QuantitativeStepClass.cost)).isSome &&
        (conclusion.find? (fun e => e.isConstOf ``Expression.compile)).isSome &&
        (conclusion.find? (fun e => e.isConstOf ``liveIndex)).isSome do
      throwError "charge the actual compiled chronological lookup"
  forallTelescope (← getConstInfo ``NativeSelection.selector_cost).type fun params conclusion => do
    let mut completed := false
    let mut primitives := false
    for param in params do
      let type ← inferType param
      if (type.find? (fun e => e.isConstOf ``NativePass.CompletedBound)).isSome then
        completed := true
      if (type.find? (fun e => e.isConstOf ``NativeSelection.Operations)).isSome then
        primitives := true
      for forbidden in #[``Bounds, ``GeneralCaller.Budget, ``Program, ``SourceCertificate,
          ``Fintype, ``Finite, ``Inhabited, ``Expression.compile, ``Expression.compileBound] do
        if (type.find? (fun e => e.isConstOf forbidden)).isSome then
          throwError "derive complete selector runtime from pass encodings and primitive operations"
    unless completed && primitives &&
        (conclusion.find? (fun e => e.isConstOf ``QuantitativeStepClass.cost)).isSome &&
        (conclusion.find? (fun e => e.isConstOf ``NativeSelection.selector)).isSome do
      throwError "certify the actual complete selector and retain pass/primitive contracts"
  for name in #[``NativeSelection.Operations.scale, ``NativeSelection.Operations.add,
      ``NativeSelection.Operations.point, ``NativeSelection.Operations.message,
      ``NativeSelection.Operations.increment, ``NativeSelection.Operations.compare] do
    let type := (← getConstInfo name).type
    for forbidden in #[``Bounds, ``Expression.compile, ``Expression.compileBound, ``NativeSelection.selector] do
      if (type.find? (fun e => e.isConstOf forbidden)).isSome then
        throwError "primitive contracts must not hide a completed selector/component budget"

end SignaturesTest.SchnorrROMSelection
