import Signatures.Runtime.BackendSchnorrROMForkDescription
import Lean.Util.CollectAxioms

/-! Scope and axiom regressions for the installed general ROM fork. Its source
laws derive both executions from measured caller resources and actual pass code. -/

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
      ``NativeROMFork.code_description] do
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

end SignaturesTest.SchnorrROMFork
