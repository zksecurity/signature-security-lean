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
      ``BLS.CaliperCoCDH.Family.reduction_nonuniform, ``BLS.cocdh_security_asymptotic,
      ``BLSCallerHandler.termination_advance, ``CoronCaller.Caller.Invariant.ofTerminates,
      ``CoronCaller.Caller.Correspondence.ofCaller, ``CoronCaller.Caller.Correspondence.ofCaller_queryBound,
      ``BLS.CaliperCoCDH.Parameters.point_valid, ``BLS.CaliperCoCDH.Parameters.callerCorrespondence,
      ``BLS.CaliperCoCDH.CallerQueries.terminates, ``BLS.CaliperCoCDH.Adversary.ofCaller] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

-- Local code/query bounds construct the source, machine and invariant. These
-- must not reappear as assumptions of the public constructor or its records.
run_meta do
  for name in #[``BLS.CaliperCoCDH.Adversary.ofCaller, ``BLS.CaliperCoCDH.CallerQueries.mk,
      ``CoronCaller.Caller.Fits.mk] do
    let type := (← getConstInfo name).type
    for forbidden in #[``OracleComp, ``OracleComp.OracleMachine, ``CoronCaller.Caller.Correspondence,
        ``CoronCaller.Caller.Invariant, ``PFunctor.DynSystem.DynComputation.ImplementsWithin,
        ``Interactive.Within, ``coCDHWithin] do
      if (type.find? (fun e => e.isConstOf forbidden)).isSome then
        throwError "{name}: constructor requires a separately supplied source or completed certificate: {forbidden}"
  let body := (← getConstInfo ``BLS.CaliperCoCDH.Adversary.ofCaller).value?.get!
  for required in #[``BLS.CaliperCoCDH.Parameters.callerCorrespondence,
      ``CoronCaller.Caller.Invariant.ofTerminates] do
    unless (body.find? (fun e => e.isConstOf required)).isSome do
      throwError "public constructor must derive its proof through {required}"

-- Proof fields can be factored into auxiliary declarations by Lean. Check the
-- resulting source allowances directly, in addition to the constructor's axiom audit.
open OracleComp in
example (curve : Model.PairingCurve) [model : BLS.CoCDHSecurityModel curve]
    (n : Nat) (queries : BLS.QueryAllowance)
    (caller : CoronCaller.Caller (model.parameters n queries).layout)
    (resources : CoronCaller.Caller.Fits (model.parameters n queries).layout caller (model.parameters n queries).callerLimits)
    (allowances : BLS.CaliperCoCDH.CallerQueries (model.parameters n queries) (curve.generates n).surjective caller)
    (pk : curve.KeyGroup n) :
    let A := BLS.CaliperCoCDH.Adversary.ofCaller (model.parameters n queries) (curve.generates n).surjective caller resources allowances
    IsQueryBoundP (A.source pk) (fun i => BLS.queryKind i = 0) queries.random ∧
      IsQueryBoundP (A.source pk) (fun i => BLS.queryKind i = 1) queries.hash ∧
      IsQueryBoundP (A.source pk) (fun i => Sum.isRight i = true) queries.sign := by
  let A := BLS.CaliperCoCDH.Adversary.ofCaller (model.parameters n queries) (curve.generates n).surjective caller resources allowances
  exact ⟨A.randomQueries pk, A.hashQueries pk, A.signingQueries pk⟩

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

-- A caller built by the new constructor is accepted by the same public theorem.
open OracleComp in
example (curve : Model.PairingCurve) [model : BLS.CoCDHSecurityModel curve]
    (n : Nat) (queries : BLS.QueryAllowance)
    (caller : CoronCaller.Caller (model.parameters n queries).layout)
    (resources : CoronCaller.Caller.Fits (model.parameters n queries).layout caller (model.parameters n queries).callerLimits)
    (allowances : BLS.CaliperCoCDH.CallerQueries (model.parameters n queries) (curve.generates n).surjective caller) :
    let adversary := BLS.CaliperCoCDH.Adversary.ofCaller (model.parameters n queries) (curve.generates n).surjective caller resources allowances
    𝒟[BLS.cocdhEufCmaGame curve n adversary] {true} ≤
      Model.coronFactor queries.sign * BLS.coCDHSuccessBound curve n queries (BLS.cocdhReductionTime curve n queries) :=
  BLS.cocdh_security curve n queries
    (BLS.CaliperCoCDH.Adversary.ofCaller (model.parameters n queries) (curve.generates n).surjective caller resources allowances)

end SignaturesTest.CaliperCoCDHSecurity
