import Signatures.Runtime.BackendSchnorrROMDescriptionPolynomial
import Signatures.Runtime.BackendSchnorrROMSecurity
import Lean.Util.CollectAxioms

/-! Guard the complete general ROM resource/security connection. Polynomial
stored code must come from original descriptions. The fixed-backend executable
and concrete hardness theorem must derive the solver's resources internally. -/

open PFunctor
open PFunctor.DynSystem.DynComputation
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr ListROM

namespace SignaturesTest.SchnorrROMResources

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Expression.variableDescription_polynomial, ``Expression.descriptionBound_polynomial,
      ``Expression.argumentsDescription_polynomial, ``Language.descriptionBound_polynomial,
      ``NativeSolver.codeDescription_eq, ``NativeSolver.DescriptionInputs.solver_polynomial,
      ``NativeSolver.DescriptionInputs.compiled_polynomial, ``NativeSolver.reduction_at_generator,
      ``NativeSolver.reduction_experiment, ``NativeSolver.program_within, ``NativeSolver.challenge_size,
      ``NativeSolver.security_of_resources] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``NativeSolver.reduction_at_generator, ``NativeSolver.reduction_experiment,
      ``NativeSolver.program_within, ``NativeSolver.security_of_resources] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[``Bounds, ``Within, ``NativeSolver.dlogWithin,
            ``GeneralCaller.Budget, ``Program, ``SourceCertificate, ``Finite, ``Inhabited] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            unless type.isAppOf ``Model.HardWithin do
              throwError "{name}: derive the solver's executable/resources from original contracts"
        if (type.find? (fun e => match e with
            | .const name _ => name.toString.contains ".AGM."
            | _ => false)).isSome then
          throwError "ordinary ROM must retain unrestricted attackers"
        if type.isAppOf ``Fintype then
          let arg := type.getAppArgs[0]!
          unless arg.isFVar && (← getFVarLocalDecl arg).userName == `F do
            throwError "only the field, not the message domain, may require a finite cardinality"
  forallTelescope (← getConstInfo ``NativeSolver.program_within).type fun params conclusion => do
    unless conclusion.isAppOf ``Within do
      throwError "construct an executable in the fixed backend"
    for required in #[``NativeSolver.reduction, ``NativeSolver.resourcesTime,
        ``NativeSolver.descriptionInputs, ``NativeSolver.DescriptionInputs.solver] do
      unless (conclusion.find? (fun e => e.isConstOf required)).isSome do
        throwError "the witness must use the complete source algorithm and derived actual time/code formulas"
    let mut measured := false
    let mut implementation := false
    let mut originalResources := #[]
    for param in params do
      let type ← inferType param
      let userName := (← getFVarLocalDecl param).userName
      if (type.find? (fun e => e.isConstOf ``QuantitativeRealization.RunsWithin)).isSome then
        measured := true
      if userName == `implementation then
        implementation := true
      if type.isAppOf ``NativePass.Resources then
        originalResources := originalResources.push userName
    unless measured && implementation && originalResources == #[`first, `second] do
      throwError "preserve the arbitrary caller's measured implementation and both original pass resource records"
  forallTelescope (← getConstInfo ``NativeSolver.reduction_experiment).type fun _ conclusion => do
    unless conclusion.isAppOf ``Eq do
      throwError "preserve exact DLog experiment equality"
    for required in #[``DiffieHellman.dlogExperiment, ``NativeSolver.reduction,
        ``_root_.Schnorr.LazyROM.dlogReduction] do
      unless (conclusion.find? (fun e => e.isConstOf required)).isSome do
        throwError "connect the executable's source to the named lazy security reduction"
  forallTelescope (← getConstInfo ``NativeSolver.security_of_resources).type fun params conclusion => do
    unless (conclusion.find? (fun e => e.isConstOf ``_root_.Schnorr.ROM.game)).isSome do
      throwError "the concrete theorem must bound the original EUF-CMA game"
    let mut originalHardness := false
    for param in params do
      let type ← inferType param
      if type.isAppOf ``Model.HardWithin &&
          (type.find? (fun e => e.isConstOf ``NativeSolver.dlogWithin)).isSome then
        originalHardness := true
    unless originalHardness do
      throwError "apply DLog hardness in the same fixed-backend resource class"
  forallTelescope (← getConstInfo ``NativeSolver.codeDescription_eq).type fun _ conclusion => do
    unless conclusion.isAppOf ``Eq do
      throwError "the numerical family formula must equal the existing complete stored-code budget"
    for required in #[``NativeSolver.codeDescription, ``NativeSolver.DescriptionInputs.solver,
        ``NativeSolver.descriptionInputs] do
      unless (conclusion.find? (fun e => e.isConstOf required)).isSome do
        throwError "connect original component descriptions to the actual whole-solver formula"
  for name in #[``NativeSolver.DescriptionInputs, ``NativeSolver.DescriptionInputs.Polynomial] do
    let info ← getConstInfoInduct name
    for ctor in info.ctors do
      forallTelescope (← getConstInfo ctor).type fun params _ => do
        for param in params do
          let type ← inferType param
          for forbidden in #[``NativeSolver.DescriptionInputs.solver, ``NativeSolver.DescriptionInputs.fork,
              ``NativeSolver.DescriptionInputs.pass, ``NativeSolver.DescriptionInputs.handler,
              ``NativeSolver.DescriptionInputs.extraction, ``NativeSolver.codeDescription,
              ``NativeROMFork.codeDescription, ``NativePass.codeDescription, ``Bounds, ``Within,
              ``Fintype, ``Finite] do
            if (type.find? (fun e => e.isConstOf forbidden)).isSome then
              throwError "description inputs must not hide completed component descriptions or efficiency"
          if (← isProp type) then
            forallTelescope type fun _ result => do
              unless result.isAppOf ``PolynomiallyBounded do
                throwError "description-family contracts must bound original numerical fields"
  for name in #[``NativeSolver.DescriptionInputs.solver_polynomial,
      ``NativeSolver.DescriptionInputs.compiled_polynomial] do
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      unless conclusion.isAppOf ``PolynomiallyBounded &&
          (conclusion.find? (fun e => e.isConstOf ``NativeSolver.DescriptionInputs.solver)).isSome do
        throwError "derive polynomial closure for the actual full stored-code formula"
      for param in params do
        let type ← inferType param
        for forbidden in #[``NativeSolver.DescriptionInputs.solver, ``NativeSolver.DescriptionInputs.fork,
            ``NativeSolver.DescriptionInputs.pass, ``NativeSolver.DescriptionInputs.handler,
            ``NativeSolver.DescriptionInputs.extraction, ``Within, ``Bounds] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "do not assume completed component stored-code bounds are polynomial"
  match ← getConstInfo ``NativeSolver.descriptionInputs with
  | .defnInfo info =>
      unless (info.value.find? (fun e => e.isConstOf ``Code.descriptionSize)).isSome do
        throwError "charge the original sampler's actual stored program"
      for forbidden in #[``NativeSolver.code, ``NativeROMFork.code, ``NativePass.code,
          ``NativeHandler.code, ``NativeExtraction.code, ``NativeSolver.codeDescription] do
        if (info.value.find? (fun e => e.isConstOf forbidden)).isSome then
          throwError "project original descriptions, not completed native components"
  | _ => throwError "original description inputs must have an inspectable definition"

end SignaturesTest.SchnorrROMResources
