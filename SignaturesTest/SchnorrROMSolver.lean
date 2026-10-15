import Signatures.Runtime.BackendSchnorrROMSolverDescription
import Signatures.Runtime.BackendSchnorrROMSolverPolynomial
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Guarded extraction cases and scope regressions for the actual complete
general ROM solver. Source equality must include the native fork and extractor,
including both uniform fallback paths, with no supplied whole-solver law.
Runtime and polynomial closure must follow from original resources and primitive
contracts, without assuming completed solver or extractor efficiency. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr ListROM

namespace SignaturesTest.SchnorrROMSolver

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5

private theorem two_ne_one : (2 : F) ≠ 1 := by decide
private theorem one_ne_two : (1 : F) ≠ 2 := by decide

private def completed (R z c : F) : cachePassOutput.Value (cryptoBase F F F Nat Nat) :=
  (((0, R, z), c), (1, 2), [], [])

example : NativeExtraction.value ([], [completed 1 1 1]) = (false, 0) := rfl
example : NativeExtraction.value ([completed 1 1 1], []) = (false, 0) := rfl

example : NativeExtraction.value ([completed 1 4 2], [completed 1 1 1]) = (true, 3) := by
  norm_num [NativeExtraction.value, NativeExtraction.oneValue, completed, two_ne_one]

example : NativeExtraction.value ([completed 1 4 2], [completed 1 1 2]) = (false, 0) := by
  norm_num [NativeExtraction.value, NativeExtraction.oneValue, completed]

example : NativeExtraction.value ([completed 1 4 2], [completed 2 1 1]) = (false, 0) := by
  norm_num [NativeExtraction.value, NativeExtraction.oneValue, completed, one_ne_two]

example : NativeExtraction.expression.denote (arithmetic F F F Nat Nat PrimitiveCosts.unit)
    (([completed 1 4 2], [completed 1 1 1]), ()) = (true, 3) := by
  rw [NativeExtraction.expression_denote]
  norm_num [NativeExtraction.value, NativeExtraction.oneValue, completed, two_ne_one]

section Native

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F F F Nat Nat))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F F F Nat Nat cost).execute instr))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

example : (NativeExtraction.code rep data cost primitive sampler).denote (.inl ()) = sampler.denote () := rfl

example : (NativeExtraction.code rep data cost primitive sampler).denote
    (.inr ([completed 1 4 2], [completed 1 1 2])) = sampler.denote () := by
  rw [NativeExtraction.code_denote]
  norm_num [NativeExtraction.value, NativeExtraction.oneValue, completed]

example : (NativeExtraction.code rep data cost primitive sampler).denote
    (.inr ([completed 1 4 2], [completed 1 1 1])) = pure 3 := by
  rw [NativeExtraction.code_denote]
  norm_num [NativeExtraction.value, NativeExtraction.oneValue, completed, two_ne_one]

end Native

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``NativeExtraction.oneExpression_denote, ``NativeExtraction.expression_denote,
      ``NativeExtraction.checked_denote, ``NativeExtraction.code_denote, ``NativeExtraction.source,
      ``NativeExtraction.code_description, ``NativeSolver.code_denote, ``NativeSolver.source_of_resources,
      ``NativeSolver.source_reduction, ``NativeSolver.code_description,
      ``NativeExtraction.oneValue_scalar, ``NativeExtraction.oneValue_size,
      ``NativeExtraction.body_time, ``NativeExtraction.value_scalar, ``NativeExtraction.expression_cost,
      ``NativeSolver.input_size, ``NativeSolver.initialExpression_cost, ``NativeSolver.setup_bound,
      ``NativeSolver.code_bound_of_resources] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[``Bounds, ``GeneralCaller.Budget, ``Program, ``SourceCertificate,
            ``Fintype, ``Finite, ``Inhabited] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "the complete solver must preserve general attackers and arbitrary message types"
        let userName := (← getFVarLocalDecl param).userName
        if #[`hfirst, `hreplay, `hselect, `hfork, `hextract, `fork, `extractor, `domainSize].contains userName then
          throwError "derive complete source/code bounds from the actual installed components"
  for name in #[``NativeSolver.source_of_resources, ``NativeSolver.source_reduction] do
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      unless conclusion.isAppOf ``Eq && (conclusion.find? (fun e => e.isConstOf ``NativeSolver.code)).isSome do
        throwError "preserve the actual complete solver's computation"
      let mut measured := false
      for param in params do
        if ((← inferType param).find? (fun e => e.isConstOf ``QuantitativeRealization.RunsWithin)).isSome then
          measured := true
      unless measured do
        throwError "derive source correspondence from measured attacker resources"
      if name == ``NativeSolver.source_reduction then
        unless (conclusion.find? (fun e => e.isConstOf ``_root_.Schnorr.LazyROM.dlogReduction)).isSome do
          throwError "connect to the named reduction carrying the original security theorem"
  match ← getConstInfo ``NativeSolver.code with
  | .defnInfo info =>
      for required in #[``NativeSolver.initialExpression, ``NativeROMFork.code, ``NativeExtraction.code] do
        unless (info.value.find? (fun e => e.isConstOf required)).isSome do
          throwError "the solver must install setup, the actual fork and actual extraction"
  | _ => throwError "the complete native solver must have an executable definition"
  for name in #[``NativeExtraction.guardBody_time, ``NativeExtraction.candidateBody_time,
      ``NativeExtraction.oneWith_time, ``NativeExtraction.innerWith_time, ``NativeExtraction.outerWith_time,
      ``NativeExtraction.code_bound] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  forallTelescope (← getConstInfo ``NativeExtraction.code_bound).type fun params conclusion => do
    unless conclusion.isAppOf ``Bounds &&
        (conclusion.find? (fun e => e.isConstOf ``NativeExtraction.code)).isSome &&
        (conclusion.find? (fun e => e.isConstOf ``NativeExtraction.runtimeBound)).isSome do
      throwError "bound the actual extractor including both fallback paths"
    let mut componentBounds := #[]
    for param in params do
      if ((← inferType param).find? (fun e => e.isConstOf ``Bounds)).isSome then
        componentBounds := componentBounds.push (← getFVarLocalDecl param).userName
    unless componentBounds == #[`hsample] do
      throwError "derive extraction internally; only the original sampler may have a supplied budget"
  forallTelescope (← getConstInfo ``NativeSolver.code_bound_of_resources).type fun params conclusion => do
    unless conclusion.isAppOf ``Bounds do
      throwError "certify complete solver runtime and output size"
    for required in #[``NativeSolver.code, ``NativeSolver.InputBound, ``NativeSolver.resourcesTime,
        ``QuantitativeStepClass.size] do
      unless (conclusion.find? (fun e => e.isConstOf required)).isSome do
        throwError "preserve the actual solver, original-resource formula and encoded input/output bounds"
    let mut measured := false
    let mut resources := #[]
    let mut selectorOps := false
    let mut extractionOps := false
    for param in params do
      let type ← inferType param
      if (type.find? (fun e => e.isConstOf ``QuantitativeRealization.RunsWithin)).isSome then
        measured := true
      if type.isAppOf ``NativePass.Resources then
        resources := resources.push (← getFVarLocalDecl param).userName
      if type.isAppOf ``NativeSelection.Operations then
        selectorOps := true
      if type.isAppOf ``NativeExtraction.Operations then
        extractionOps := true
    unless measured && resources == #[`first, `second] && selectorOps && extractionOps do
      throwError "derive both pass, selector and extractor budgets from measured caller resources and primitive contracts"
  let operationInfo ← getConstInfoInduct ``NativeExtraction.Operations
  for ctor in operationInfo.ctors do
    forallTelescope (← getConstInfo ctor).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[``Bounds, ``GeneralCaller.Budget, ``NativeExtraction.expression,
            ``NativeExtraction.code, ``NativeExtraction.runtimeBound, ``NativeExtraction.localTime,
            ``NativePass.code, ``NativeSolver.code, ``Program, ``SourceCertificate,
            ``Fintype, ``Finite, ``Inhabited] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "extraction operation contracts must concern primitive costs and encodings only"
  for name in #[``NativeExtraction.frameWidth_polynomial, ``NativeExtraction.runtimeBound_polynomial,
      ``NativeSolver.resourcesTime_polynomial] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      unless conclusion.isAppOf ``PolynomiallyBounded do
        throwError "derive polynomial closure of the complete runtime formula"
      for param in params do
        let type ← inferType param
        for forbidden in #[``NativePass.TimeInputs.time, ``NativeROMFork.resourcesTime,
            ``NativeExtraction.runtimeBound, ``NativeExtraction.localTime, ``NativeSolver.resourcesTime,
            ``ExecutionProfile.runtimeBound, ``Bounds, ``Fintype, ``Finite, ``Inhabited] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "derive polynomial component runtimes without assuming completed component efficiency"
      if name == ``NativeSolver.resourcesTime_polynomial then
        unless (conclusion.find? (fun e => e.isConstOf ``NativeSolver.resourcesTime)).isSome do
          throwError "polynomial closure must cover the exact complete solver runtime"
  match ← getConstInfo ``NativeSolver.resourcesTime with
  | .defnInfo info =>
      for required in #[``NativeROMFork.resourcesTime, ``NativeExtraction.runtimeBound,
          ``ExecutionProfile.runtimeBound, ``NativeExtraction.frameWidth] do
        unless (info.value.find? (fun e => e.isConstOf required)).isSome do
          throwError "the complete formula must charge fork, extraction, original fallback sampling and control"
  | _ => throwError "the complete runtime formula must have an inspectable definition"

end SignaturesTest.SchnorrROMSolver
