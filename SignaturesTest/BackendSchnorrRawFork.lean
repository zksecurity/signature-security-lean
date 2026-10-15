import Signatures.Runtime.BackendSchnorrRawForkDescription
import Signatures.Runtime.BackendSchnorrRawLookupCost
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Executed controller cases distinguish a missing challenge from a stored
zero, preserve selection failures, and reject a changed second selector. The
whole-controller runtime is separate from the complete lookup resource bound. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr Signatures.Runtime.Schnorr.RawTape

namespace SignaturesTest.BackendSchnorrRawFork

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5

private def cells : List (TapeCell F) := [(3, 0, 1), (1, 0, 0), (99, 0, 7), (1, 4, 0)]

example : NativeLookup.expression.denote (arithmetic F F F Nat Nat PrimitiveCosts.unit)
    ((1, cells), ()) = (true, 4) := by
  rw [NativeLookup.expression_value]
  rfl

example : NativeLookup.expression.denote (arithmetic F F F Nat Nat PrimitiveCosts.unit)
    ((0, cells), ()) = (true, 0) := by
  rw [NativeLookup.expression_value]
  rfl

example : NativeLookup.expression.denote (arithmetic F F F Nat Nat PrimitiveCosts.unit)
    ((2 ^ 64, cells), ()) = (false, 0) := by
  rw [NativeLookup.expression_value]
  rfl

private def selectionExpression (found : Bool) : Expr CryptoOp [.nat] NativeFork.choiceTy :=
  .pair (.bool found) (.var .here)

private def passExpression (recordZero : Bool) :
    Expr CryptoOp [NativeFork.passInput .nat] (NativeFork.passOutput .nat) :=
  .pair (.snd (.var .here))
    (if recordZero then
      .pair (.cons (.pair (.nat 1) (.pair (.op .zero .unit) (.nat 0))) .nil)
        (.snd (.fst (.var .here)))
    else .fst (.var .here))

section Execution

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F F F Nat Nat))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F F F Nat Nat cost).execute instr))
  (sampler other : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

private def controller (found recordZero : Bool) :=
  NativeFork.code (config := .nat) (out := .nat) rep data cost primitive
    (NativeFork.compileLocal rep data cost primitive (selectionExpression found))
    (.atomic (NativeFork.compileLocal rep data cost primitive (passExpression recordZero))) sampler

/-- Selection failure never executes replacement sampling. -/
example : (controller rep data cost primitive sampler false false).denote 7 = pure (.inl ()) := by
  rw [controller, NativeFork.denote]
  simp [Code.denote, passExpression, selectionExpression, Expr.denote, Var.get]

/-- The actual costed execution is independent of the unreachable sampler. -/
example (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat) :
    (controller rep data cost primitive sampler false false).run control queryCost 7 =
      (controller rep data cost primitive other false false).run control queryCost 7 := by
  rfl

/-- Missing entry plus replacement zero must execute replay and may succeed. -/
example (hs : sampler.denote () = pure (0 : F)) :
    (controller rep data cost primitive sampler true false).denote 7 = pure (.inr (7, 7)) := by
  rw [controller, NativeFork.denote]
  simp [Code.denote, passExpression, selectionExpression, Expr.denote, Var.get, hs,
    values, SeedTape.values]

/-- A present zero with replacement zero is an unchanged challenge and rejects. -/
example (hs : sampler.denote () = pure (0 : F)) :
    (controller rep data cost primitive sampler true true).denote 0 = pure (.inl ()) := by
  rw [controller, NativeFork.denote]
  simp [Code.denote, passExpression, selectionExpression, Expr.denote, Var.get, hs,
    arithmetic, values, SeedTape.values, SeedTape.familyTag, decodeReply]

end Execution

example : (NativeFork.finishExpression .nat).denote (arithmetic F F F Nat Nat PrimitiveCosts.unit)
    (((true, 1), ((9, ([], [])), (0, 7))), ()) = (false, (7, 9)) := rfl

example : (NativeFork.finishExpression .nat).denote (arithmetic F F F Nat Nat PrimitiveCosts.unit)
    (((false, 0), ((9, ([], [])), (0, 7))), ()) = (false, (7, 9)) := rfl

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``NativeLookup.fold_found, ``NativeLookup.fold_answer, ``NativeLookup.read_values,
      ``NativeLookup.expression_value, ``NativeLookup.source, ``NativeLookup.description,
      ``NativeLookup.step_invariant, ``NativeLookup.fold_invariant, ``NativeLookup.property,
      ``NativeLookup.accumulator_size, ``NativeLookup.input_size, ``NativeLookup.body_time,
      ``NativeLookup.expression_time, ``NativeLookup.bound, ``NativeLookup.runtimeBound_polynomial,
      ``NativeFork.replay_denote, ``NativeFork.selected_denote, ``NativeFork.denote,
      ``NativeFork.source, ``NativeFork.compileLocal_description, ``NativeFork.chooseLocal_description,
      ``NativeFork.reject_description, ``NativeFork.description] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``NativeLookup.source, ``NativeFork.source] do
    forallTelescope (← getConstInfo name).type fun _ conclusion => do
      unless conclusion.isAppOf ``Eq do
        throwError "{name}: source law must preserve the entire computation"
      if (conclusion.find? (fun e => e.isConstOf ``MeasureTheory.Measure)).isSome then
        throwError "{name}: source correspondence must not discard query/state behavior"
  for name in #[``NativeLookup.code, ``NativeLookup.descriptionBound,
      ``NativeFork.code, ``NativeFork.descriptionBound] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        if (← inferType param).isConstOf ``Nat then
          unless (← getFVarLocalDecl param).userName == `allowance do
            throwError "{name}: stored code must not enumerate positions or tape lengths"
  for name in #[``NativeLookup.expressionTime, ``NativeLookup.runtimeBound] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        if (← inferType param).isConstOf ``Nat then
          unless #[`width, `cap, `comparisonTime, `subtractTime, `zeroTime].contains
              (← getFVarLocalDecl param).userName do
            throwError "{name}: lookup runtime must not include a numeric-position factor"
  forallTelescope (← getConstInfo ``NativeLookup.bound).type fun params conclusion => do
    unless conclusion.isAppOf ``Bounds do
      throwError "lookup runtime must cover all native paths"
    for param in params do
      let type ← inferType param
      for forbidden in #[``NativeLookup.compiled, ``NativeLookup.code, ``Bounds,
          ``Expression.compile, ``Expression.compileBound] do
        if (type.find? (fun e => e.isConstOf forbidden)).isSome then
          throwError "lookup runtime must be derived from primitive and backend laws"
  for name in #[``NativeFork.code, ``NativeFork.source] do
    let type := (← getConstInfo name).type
    for forbidden in #[``Program, `Signatures.Runtime.Schnorr.SourceCertificate] do
      if (type.find? (fun e => e.isConstOf forbidden)).isSome then
        throwError "native controller must accept actual general pass code"

end SignaturesTest.BackendSchnorrRawFork
