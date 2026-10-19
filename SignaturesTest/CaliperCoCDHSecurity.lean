import Signatures.BLS.Statement
import Lean.Util.CollectAxioms

/-! Guard the public co-CDH migration: ordinary outputs, fixed actual Caliper
resources, complete challenge coverage and derived polynomial overhead. -/
namespace SignaturesTest.CaliperCoCDHSecurity
open Lean Meta Signatures.Runtime Signatures.Runtime.CaliperBackend

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Interactive.Within.viewInput, ``coCDHWithin.mono, ``coCDHSuccessBound_mono,
      ``CoronFull.scalar_valid, ``CoronFull.point_valid, ``CoronFull.challenge_valid,
      ``CoronFull.coCDH_within, ``BLS.CaliperCoCDH.reduction_within,
      ``BLS.Proofs.cocdh_probability, ``BLS.cocdh_security,
      ``coCDHNonuniformWithin.of_pointwise,
      ``BLS.CaliperCoCDH.Family.PolynomialResources.solverTime,
      ``BLS.CaliperCoCDH.Family.PolynomialResources.solverCode,
      ``BLS.CaliperCoCDH.Family.PolynomialResources.solverMemory,
      ``BLS.CaliperCoCDH.Family.reduction_nonuniform, ``BLS.cocdh_security_asymptotic] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

-- The public route cannot fall back to the old backend or algebraic outputs.
run_meta do
  for name in #[``BLS.CoCDHSecurityModel.mk, ``BLS.UnrestrictedAdversary,
      ``BLS.CaliperCoCDH.Parameters.mk, ``BLS.CaliperCoCDH.Adversary.mk,
      ``BLS.coCDHSuccessBound, ``BLS.Proofs.cocdh_security,
      ``BLS.CaliperCoCDH.Family.Proofs.security] do
    let info ← getConstInfo name
    for expression in #[info.type, (info.value? true).getD info.type] do
      for forbidden in #[`BLS.ExecutionModel, `BLS.GeneralCoCDH.Parameters,
          `BLS.GeneralCoCDH.Adversary, `BLS.GeneralCoCDH.reduction_within,
          `Signatures.Runtime.Coron.NativeSolver.coCDHWithin,
          ``BLS.CaliperAGM.Parameters, ``BLS.CaliperAGM.AlgebraicAdversary,
          ``PFunctor.StepClass, ``PFunctor.QuantitativeStepClass] do
        if (expression.find? (fun e => e.isConstOf forbidden)).isSome then
          throwError "{name}: unexpected abstract-backend or algebraic dependency {forbidden}"
  for (name, required) in #[( ``BLS.CoCDHSecurityModel.mk, #[``BLS.CaliperCoCDH.Parameters]),
      (``BLS.UnrestrictedAdversary, #[``BLS.CaliperCoCDH.Adversary]),
      (``BLS.coCDHSuccessBound, #[``coCDHWithin,
        ``BLS.CaliperCoCDH.Parameters.solverCode, ``BLS.CaliperCoCDH.Parameters.solverMemory]),
      (``BLS.Proofs.cocdh_security, #[``BLS.CaliperCoCDH.reduction_within]),
      (``BLS.CaliperCoCDH.Family.Proofs.security, #[``BLS.CaliperCoCDH.Family.reduction_nonuniform])] do
    let info ← getConstInfo name
    for symbol in required do
      unless (#[info.type, (info.value? true).getD info.type]).any
          (fun e => (e.find? (fun sub => sub.isConstOf symbol)).isSome) do
        throwError "{name}: missing constructed Caliper dependency {symbol}"

-- Complete-solver polynomiality and domain cardinality bounds are not component assumptions.
run_meta do
  let type := (← getConstInfo ``BLS.CaliperCoCDH.Family.PolynomialResources.mk).type
  for forbidden in #[``BLS.CaliperCoCDH.Parameters.solverTime,
      ``BLS.CaliperCoCDH.Parameters.solverCode, ``BLS.CaliperCoCDH.Parameters.solverMemory,
      ``Fintype.card, ``Interactive.Within,
      ``Interactive.NonuniformWithin, ``coCDHNonuniformWithin, ``coCDHNonuniformHardness] do
    if (type.find? (fun e => e.isConstOf forbidden)).isSome then
      throwError "completed-solver or domain-size premise in component record: {forbidden}"
  -- The range also indexes service types; reject a numeric bound on the range,
  -- while permitting that index in the types of represented component widths.
  forallTelescope type fun parameters _ => do
    for parameter in parameters do
      let premise ← inferType parameter
      if premise.isAppOf ``PolynomiallyBounded then
        lambdaTelescope premise.getAppArgs[0]! fun _ resource => do
          if resource.getAppFn.isConstOf ``BLS.CaliperCoCDH.Parameters.randomBound then
            throwError "polynomial sampling-range cardinality required"
  for (name, moduleName) in #[( ``BLS.cocdh_security_asymptotic, `Signatures.BLS.CaliperCoCDHFamilyStatement),
      (``BLS.CaliperCoCDH.Family.Proofs.security, `Signatures.BLS.Proofs.CaliperCoCDHFamily)] do
    unless (← findModuleOf? name) == some moduleName do
      throwError "{name}: keep the statement and proof in their separate files"

example (curve : Model.PairingCurve) [model : BLS.CoCDHSecurityModel curve]
    (n : Nat) (queries : BLS.QueryAllowance) (time : Nat) :
    BLS.coCDHSuccessBound curve n queries time = (model.parameters n queries).coCDHBound time := rfl

-- The derived certificate covers all challenges sampled by the original game.
example (curve : Model.PairingCurve) [model : BLS.CoCDHSecurityModel curve]
    (n : Nat) (queries : BLS.QueryAllowance) (A : BLS.UnrestrictedAdversary curve n queries)
    (scalar : curve.Scalar n) (point : curve.SignatureGroup n) :
    (model.parameters n queries).challenge.valid
      (scalar • curve.keyGenerator n, curve.generator n, scalar • curve.generator n, point) :=
  (BLS.CaliperCoCDH.reduction_within (model.parameters n queries) A (curve.generates n).surjective).1 scalar point

open OracleComp in
example (curve : Model.PairingCurve) [model : BLS.CoCDHSecurityModel curve]
    (queries : Nat → BLS.QueryAllowance)
    (adversary : ∀ n, BLS.UnrestrictedAdversary curve n (queries n))
    (resources : BLS.CaliperCoCDH.Family.PolynomialResources (fun n => model.parameters n (queries n)))
    (hardness : BLS.CaliperCoCDH.Family.coCDHHardness (fun n => model.parameters n (queries n))) :
    negligible (fun n => 𝒟[BLS.Game.rom curve n (adversary n).source] {true}) :=
  BLS.cocdh_security_asymptotic curve queries adversary resources hardness

end SignaturesTest.CaliperCoCDHSecurity
