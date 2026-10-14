import Signatures
import Lean.Util.CollectAxioms

open Signatures.Runtime Signatures.Runtime.BackendProgram
open Lean Meta Elab Command

-- The zero-signing case does not acquire an artificial singularity in the
-- negligible-loss bridge. The exact concrete loss remains unchanged.
example : Model.coronFactor 0 = 1 := by norm_num [Model.coronFactor]
example : Model.coronFactor 1 = 4 := by
  norm_num [Model.coronFactor, ENNReal.mul_inv]

run_cmd liftTermElabM do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``negligible_polynomial_eval_mul, ``PolynomiallyBounded.negligible_mul,
      ``Model.coronFactor_le, ``Model.negligible_of_coron_bound,
      ``NonuniformWithin.of_pointwise, ``NonuniformWithin.executable_family,
      ``NonuniformHardness.apply_of_pointwise,
      ``Coron.NativeSolver.Family.within_at, ``Coron.NativeSolver.Family.nonuniform_within,
      ``Coron.NativeSolver.Family.security_of_resources] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

-- Guard the public asymptotic statement's scope. It must derive the completed
-- solver's efficiency from caller/primitive contracts, allow varying groups,
-- charge actual caller descriptions, cover challenges, and allow infinite messages.
run_cmd liftTermElabM do
  let name := ``Coron.NativeSolver.Family.security_of_resources
  forallTelescope (← getConstInfo name).type fun params conclusion => do
    let mut resources := false
    let mut hardness := false
    let mut challenge := false
    let mut finiteMessage := false
    let mut families : Array Name := #[]
    let mut polynomial : Array Name := #[]
    for param in params do
      let binder ← param.fvarId!.getUserName
      let type ← inferType param
      if (type.find? (fun e => e.isAppOf ``Within || e.isAppOf ``NonuniformWithin ||
          e.isAppOf ``Coron.SourceCertificate)).isSome then
        throwError "{name}: a completed-solver or arithmetic-source certificate became a premise"
      if binder == `hrun then
        resources := (type.find? (fun e =>
          e.isAppOf ``PFunctor.DynSystem.DynComputation.QuantitativeRealization.RunsWithin)).isSome
      if binder == `hardness then
        hardness := type.isAppOf ``Coron.NativeSolver.Family.coCDHNonuniformHardness
      if binder == `hchallenge then challenge := true
      if #[`F, `G₁, `G₂, `Gₜ, `M].contains binder then
        unless type.isForall && type.bindingDomain!.isConstOf ``Nat && type.bindingBody!.isSort do
          throwError "{name}: {binder} must vary with the security parameter"
        families := families.push binder
      if type.isForall then
        let body := type.bindingBody!
        if body.isAppOf ``Fintype || body.isAppOf ``Finite then
          let family := body.getAppArgs[0]!.getAppFn
          if let .fvar id := family then
            if (← id.getUserName) == `M then finiteMessage := true
      if type.isAppOf ``PolynomiallyBounded then polynomial := polynomial.push binder
    if finiteMessage then
      throwError "{name}: finite-message family assumption returned"
    unless resources && hardness && challenge && families.size == 5 do
      throwError "{name}: missing resource/hardness/challenge/family scope"
    for required in #[`hSigning, `hInput, `hWork, `hQueries, `hInitCode, `hHeadCode, `hUpdateCode] do
      unless polynomial.contains required do
        throwError "{name}: missing polynomial premise {required}"
    unless conclusion.isAppOf ``negligible do
      throwError "{name}: conclusion must be negligible signature success"
