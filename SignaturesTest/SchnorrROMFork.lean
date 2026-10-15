import Signatures.Runtime.BackendSchnorrROMForkDescription
import Signatures.Runtime.BackendSchnorrROMForkPolynomial
import Lean.Util.CollectAxioms

/-! Scope and axiom regressions for the installed general ROM fork. Its source
laws derive both executions from measured caller resources and actual pass code.
The runtime theorem derives both pass, selector and sampler budgets internally;
its original-resource records must not conceal completed component bounds. -/

open PFunctor
open PFunctor.DynSystem.DynComputation
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr ListROM RawTape

namespace SignaturesTest.SchnorrROMFork

example {F G₁ G₂ K M : Type} : NativeROMFork.output (F := F) (G₁ := G₁) (G₂ := G₂)
    (K := K) (M := M) none = .inl () := rfl

example {F G₁ G₂ K M : Type}
    (first second : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) :
    NativeROMFork.output (some (first, second)) = .inr ([first], [second]) := rfl

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``NativeROMFork.source_of_resources, ``NativeROMFork.result_shape_of_resources,
      ``NativeROMFork.code_description, ``NativeROMFork.output_size,
      ``NativePass.Resources.tapeWidth_le, ``NativePass.Resources.sampler_bound,
      ``NativePass.Resources.pass_bound, ``NativeROMFork.code_bound_of_resources] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[``Bounds, ``GeneralCaller.Budget, ``Program, ``SourceCertificate,
            ``Fintype, ``Finite, ``Inhabited] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: preserve arbitrary callers/messages without completed budgets or default messages"
        let userName := (← getFVarLocalDecl param).userName
        if #[`hfirst, `hreplay, `hselect, `pass, `selector, `valid, `domainSize].contains userName then
          throwError "{name}: derive pass/replay/selection laws for the actual installed code"
  for name in #[``NativeROMFork.source_of_resources, ``NativeROMFork.result_shape_of_resources] do
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      let mut measured := false
      let mut actual := (conclusion.find? (fun e => e.isConstOf ``NativeROMFork.code)).isSome
      for param in params do
        let type ← inferType param
        if (type.find? (fun e => e.isConstOf ``QuantitativeRealization.RunsWithin)).isSome then
          measured := true
        if (type.find? (fun e => e.isConstOf ``NativeROMFork.code)).isSome then
          actual := true
      unless measured && actual do
        throwError "derive the actual fork source/output shape from measured resources"
      if name == ``NativeROMFork.source_of_resources then
        unless conclusion.isAppOf ``Eq &&
            (conclusion.find? (fun e => e.isConstOf ``RawTape.fork)).isSome &&
            (conclusion.find? (fun e => e.isConstOf ``selectPass)).isSome do
          throwError "connect the complete native fork to the existing source fork/selector"
  match ← getConstInfo ``NativeROMFork.code with
  | .defnInfo info =>
      for required in #[``NativeFork.code, ``NativePass.code, ``NativeSelection.selector] do
        unless (info.value.find? (fun e => e.isConstOf required)).isSome do
          throwError "install the actual native pass and selector in the replay controller"
  | _ => throwError "the native ROM fork must have an executable definition"
  forallTelescope (← getConstInfo ``NativeROMFork.code_bound_of_resources).type fun params conclusion => do
    unless conclusion.isAppOf ``Bounds &&
        (conclusion.find? (fun e => e.isConstOf ``NativeROMFork.code)).isSome &&
        (conclusion.find? (fun e => e.isConstOf ``NativeROMFork.resourcesTime)).isSome do
      throwError "bound the whole installed fork with the original-resource runtime formula"
    let mut measured := false
    let mut resources := #[]
    let mut selectorOps := false
    for param in params do
      let type ← inferType param
      if (type.find? (fun e => e.isConstOf ``QuantitativeRealization.RunsWithin)).isSome then
        measured := true
      if type.isAppOf ``NativePass.Resources then
        resources := resources.push (← getFVarLocalDecl param).userName
      if type.isAppOf ``NativeSelection.Operations then
        selectorOps := true
    unless measured && resources == #[`first, `second] && selectorOps do
      throwError "derive both pass budgets and selection from original resources and primitive contracts"
  let resourceInfo ← getConstInfoInduct ``NativePass.Resources
  for ctor in resourceInfo.ctors do
    forallTelescope (← getConstInfo ctor).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[``Bounds, ``GeneralCaller.Budget, ``NativePass.code,
            ``NativeHandler.code, ``NativeSelection.selector, ``Program, ``SourceCertificate,
            ``Fintype, ``Finite, ``Inhabited] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "original pass resources must not hide finished budgets or restricted attackers"
  for name in #[``NativePass.TimeInputs.time_polynomial, ``NativeROMFork.controllerWidth_polynomial,
      ``NativeROMFork.resourcesTime_polynomial] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      unless conclusion.isAppOf ``PolynomiallyBounded do
        throwError "derive polynomial closure of the actual runtime formula"
      for param in params do
        let type ← inferType param
        for forbidden in #[``NativePass.TimeInputs.time, ``NativeROMFork.resourcesTime,
            ``NativeSelection.timeBudget, ``Bounds, ``Fintype, ``Finite, ``Inhabited] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "polynomial closure must not assume completed component efficiency or fixed finite domains"
  let polyInfo ← getConstInfoInduct ``NativePass.TimeInputs.Polynomial
  for ctor in polyInfo.ctors do
    forallTelescope (← getConstInfo ctor).type fun params _ => do
      for param in params do
        let type ← inferType param
        if (← isProp type) then
          unless type.isAppOf ``PolynomiallyBounded do
            throwError "time-input polynomial contracts must bound original numerical fields"
          for forbidden in #[``NativePass.TimeInputs.time, ``NativePass.timeBudget,
              ``NativeHandler.callerTime, ``NativeHandler.timeBudget, ``NativePass.finalHashTime,
              ``NativeSelection.timeBudget, ``ExecutionProfile.runtimeBound] do
            if (type.find? (fun e => e.isConstOf forbidden)).isSome then
              throwError "time-input contracts must not hide finished component polynomial bounds"
  match ← getConstInfo ``NativeROMFork.resourcesTime with
  | .defnInfo info =>
      for required in #[``NativeFork.runtimeBoundWithTapeWidth, ``NativePass.TimeInputs.time,
          ``NativeSelection.timeBudget, ``ExecutionProfile.runtimeBound] do
        unless (info.value.find? (fun e => e.isConstOf required)).isSome do
          throwError "the installed fork formula must include actual pass, selector and sampler costs"
  | _ => throwError "the installed runtime formula must have an inspectable definition"

end SignaturesTest.SchnorrROMFork
