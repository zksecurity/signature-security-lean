import Signatures.BLS.Statement
import Signatures.BLS.GeneralAGMStatement
import Signatures.BLS.GeneralExecutionModel
import Lean.Util.CollectAxioms

/-! Guard the public statement and its underlying resource theorem. In
particular, bundling must not hide a finished-solver budget or an arithmetic
attacker requirement, and the message/public-key types stay unrestricted. -/

open Lean Meta
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.LazyAGM.NativeSolver

namespace SignaturesTest.GeneralAGMStatement

-- Keep the public theorem in the scheme's main statement file.
run_meta do
  unless (← findModuleOf? ``BLS.agm_security) == some `Signatures.BLS.Statement do
    throwError "BLS.agm_security must be defined in Signatures.BLS.Statement"
  for name in #[``BLS.Proofs.agm_security, ``BLS.Proofs.agm_security_common_budget,
      ``BLS.dlogSuccessBound_mono, ``BLS.Proofs.cocdh_security,
      ``BLS.agmEufCmaGame_eq, ``BLS.cocdhEufCmaGame_eq] do
    unless (← findModuleOf? name) == some `Signatures.BLS.Proofs.GeneralSecurity do
      throwError "{name}: supporting proof must stay in the separate proof file"

-- Keep both lower-level wrappers small, and the public theorem aligned with
-- curve/security parameter/query allowances/adversary. Resource proofs stay in the records.
run_meta do
  for (name, expected) in #[( ``BLS.GeneralAGM.security, 2), (``BLS.GeneralAGM.Family.security, 3),
      (``BLS.agm_security, 4), (``BLS.cocdh_security, 4)] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      let mut explicitCount := 0
      for param in params do
        if (← getFVarLocalDecl param).binderInfo == .default then
          explicitCount := explicitCount + 1
      unless explicitCount == expected do
        throwError "{name}: expected {expected} explicit public arguments, found {explicitCount}"

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Model.le_advantageBound, ``Model.hardWithin_advantageBound, ``Model.advantageBound_le,
      ``challenge_size, ``security_of_resources, ``BLS.GeneralAGM.security, ``BLS.GeneralAGM.Family.security,
      ``BLS.agm_security, ``BLS.dlogSuccessBound_mono,
      ``BLS.agmEufCmaGame_eq, ``BLS.GeneralAGM.reductions_within, ``BLS.CaliperAGM.reductions_within,
      ``BLS.AlgebraicAdversary.query_allowances, ``BLS.cocdh_security, ``BLS.cocdhEufCmaGame_eq,
      ``BLS.GeneralCoCDH.reduction_within, ``BLS.UnrestrictedAdversary.query_allowances] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

run_meta do
  for name in #[``security_of_resources, ``BLS.GeneralAGM.security, ``BLS.GeneralAGM.reductions_within,
      ``BLS.GeneralAGM.Family.security, ``BLS.GeneralAGM.Parameters.mk, ``BLS.GeneralAGM.AlgebraicAdversary.mk,
      ``BLS.agm_security,
      ``BLS.AGMSecurityModel.mk, ``BLS.CaliperAGM.Parameters.mk, ``BLS.CaliperAGM.AlgebraicAdversary.mk,
      ``BLS.CaliperAGM.reductions_within, ``BLS.ExecutionModel.mk, ``Model.PairingCurve.mk,
      ``BLS.cocdh_security, ``BLS.CoCDHSecurityModel.mk, ``BLS.GeneralCoCDH.Parameters.mk,
      ``BLS.GeneralCoCDH.Adversary.mk, ``BLS.GeneralCoCDH.reduction_within] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[``Bounds, ``GeneralCaller.Budget,
            `Signatures.Runtime.AGM.SourceCertificate,
            `Signatures.Runtime.Coron.SourceCertificate,
            `Signatures.Runtime.Schnorr.SourceCertificate] do
          if type.find? (fun e => e.isConstOf forbidden) |>.isSome then
            throwError "{name}: hidden completed-code budget or arithmetic attacker: {forbidden}"
        forallTelescope type fun _ premise => do
          if premise.isAppOf ``Finite || premise.isAppOf ``Fintype then
            for base in params do
              let declaration ← getFVarLocalDecl base
              if declaration.userName == `M || declaration.userName == `G₂ then
                if premise.find? (fun e => e == base) |>.isSome then
                  throwError "{name}: finite message or public-key domain required"

-- The public bound and its implementation/resource class stay inspectable.
run_meta do
  let info ← getConstInfo ``BLS.GeneralAGM.Parameters.securityBound
  unless info.value?.isSome do
    throwError "securityBound must be a transparent definition"
  let info ← getConstInfo ``BLS.GeneralAGM.Parameters.dlogBound
  unless info.value?.isSome do
    throwError "dlogBound must expose its implementation/resource class"

-- The public AGM route uses literal Caliper programs and the proved complete
-- reduction certificates. Keep the old abstract backend confined to its own API.
run_meta do
  for name in #[``BLS.AGMSecurityModel.mk, ``BLS.AlgebraicAdversary,
      ``BLS.CaliperAGM.Parameters.mk, ``BLS.CaliperAGM.AlgebraicAdversary.mk,
      ``BLS.dlogSuccessBound, ``BLS.Proofs.agm_security] do
    let info ← getConstInfo name
    for expression in #[info.type, (info.value? true).getD info.type] do
      for forbidden in #[``BLS.ExecutionModel, ``BLS.GeneralAGM.Parameters,
          ``BLS.GeneralAGM.AlgebraicAdversary, ``BLS.GeneralAGM.reductions_within,
          ``PFunctor.StepClass, ``PFunctor.QuantitativeStepClass,
          ``Signatures.Runtime.LazyAGM.NativeSolver.dlogWithin] do
        if expression.find? (fun e => e.isConstOf forbidden) |>.isSome then
          throwError "{name}: old abstract backend in public Caliper route: {forbidden}"
  for (name, required) in #[( ``BLS.AGMSecurityModel.mk, #[``BLS.CaliperAGM.Parameters]),
      (``BLS.AlgebraicAdversary, #[``BLS.CaliperAGM.AlgebraicAdversary]),
      (``BLS.dlogSuccessBound, #[``Signatures.Runtime.CaliperBackend.dlogWithin,
        ``BLS.CaliperAGM.Parameters.solverCode, ``BLS.CaliperAGM.Parameters.solverMemory]),
      (``BLS.Proofs.agm_security, #[``BLS.CaliperAGM.reductions_within])] do
    let info ← getConstInfo name
    for symbol in required do
      unless (#[info.type, (info.value? true).getD info.type]).any
          (fun e => (e.find? (fun sub => sub.isConstOf symbol)).isSome) do
        throwError "{name}: missing Caliper dependency {symbol}"

-- Both public routes have four explicit inputs and one route-specific model.
run_meta do
  for name in #[``BLS.agm_security, ``BLS.cocdh_security] do
    unless (← findModuleOf? name) == some `Signatures.BLS.Statement do
      throwError "{name} must be defined in Signatures.BLS.Statement"
    forallTelescope (← getConstInfo name).type fun params _ => do
      unless params.size == 5 do
        throwError "{name} must expose four inputs and one declared model"
      for (param, expected) in params.zip #[`curve, `inst, `securityParameter, `queries, `adversary] do
        let declaration ← getFVarLocalDecl param
        if expected != `inst && declaration.userName != expected then
          throwError "{name}: expected public input {expected}, found {declaration.userName}"

-- The main statements display the game and hardness quantity directly, with
-- their time allowance. The low-level resource record stays out of the statement.
run_meta do
  for (name, visible) in #[( ``BLS.agm_security,
      #[``BLS.agmEufCmaGame, ``BLS.dlogSuccessBound, ``BLS.agmReductionTime, ``Model.PairingCurve.order]),
      (``BLS.cocdh_security,
      #[``BLS.cocdhEufCmaGame, ``BLS.coCDHSuccessBound, ``BLS.cocdhReductionTime, ``Model.coronFactor])] do
    let type := (← getConstInfo name).type
    for symbol in visible do
      unless (type.find? (fun e => e.isConstOf symbol)).isSome do
        throwError "{name}: must display {symbol}"
    if (type.find? (fun e => match e with | .letE .. => true | _ => false)).isSome then
      throwError "{name}: resource-record let-binding in the main public statement"

-- The co-CDH contract must not silently acquire algebraic attacker/output requirements.
run_meta do
  for name in #[``BLS.CoCDHSecurityModel.mk, ``BLS.GeneralCoCDH.Parameters.mk,
      ``BLS.GeneralCoCDH.Adversary.mk, ``BLS.cocdh_security] do
    let type := (← getConstInfo name).type
    for forbidden in #[``BLS.GeneralAGM.Parameters, ``BLS.GeneralAGM.AlgebraicAdversary,
        ``BLS.CaliperAGM.Parameters, ``BLS.CaliperAGM.AlgebraicAdversary,
        ``BLS.AlgebraicAdversary, ``AGM.outputTy] do
      if type.find? (fun e => e.isConstOf forbidden) |>.isSome then
        throwError "{name}: algebraic requirement in unrestricted route: {forbidden}"

open OracleComp in
example (curve : Model.PairingCurve) [BLS.AGMSecurityModel curve]
    (securityParameter : Nat) (queries : BLS.QueryAllowance)
    (adversary : BLS.AlgebraicAdversary curve securityParameter queries) :
    ∀ pk, IsQueryBoundP (adversary.source.main
      (Model.LazyAGM.Interactive.initialInput (curve.generator securityParameter) pk))
      (fun i => BLS.queryKind i.value.data = 1) queries.hash :=
  (BLS.AlgebraicAdversary.query_allowances curve securityParameter queries adversary).2.1

example (curve : Model.PairingCurve) [BLS.AGMSecurityModel curve]
    (securityParameter : Nat) (queries : BLS.QueryAllowance)
    (adversary : BLS.AlgebraicAdversary curve securityParameter queries) :
    BLS.agmEufCmaGame curve securityParameter adversary =
      Model.DirectAGM.game (Gₜ := curve.TargetGroup securityParameter) BLS.LazyAGM.terms (fun _ _ => True)
        (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary.source :=
  BLS.agmEufCmaGame_eq curve securityParameter adversary

-- The displayed supremum is the same resource-indexed hardness quantity used
-- by the native solver certificates, for every time allowance.
example (curve : Model.PairingCurve) [model : BLS.AGMSecurityModel curve]
    (securityParameter : Nat) (queries : BLS.QueryAllowance) (time : Nat) :
    BLS.dlogSuccessBound curve securityParameter queries time =
      (model.parameters securityParameter queries).dlogBound time := rfl

-- The public record provides the two original reductions' actual code/time/
-- total-memory certificates, including coverage of every sampled challenge.
example (curve : Model.PairingCurve) [model : BLS.AGMSecurityModel curve]
    (securityParameter : Nat) (queries : BLS.QueryAllowance)
    (adversary : BLS.AlgebraicAdversary curve securityParameter queries) :
    let resources := model.parameters securityParameter queries
    resources.within resources.goodTime (BLS.LazyAGM.Reduction.goodReductionList adversary.proofView) ∧
      resources.within resources.badTime (BLS.LazyAGM.Reduction.badReductionList adversary.proofView) :=
  BLS.CaliperAGM.reductions_within (model.parameters securityParameter queries) adversary

-- The common allowance is derived from both existing runtime proofs. Enlarging
-- time leaves the same Caliper layouts, stored-code and total-memory bounds in force.
example (curve : Model.PairingCurve) [model : BLS.AGMSecurityModel curve]
    (securityParameter : Nat) (queries : BLS.QueryAllowance) :
    BLS.agmReductionTime curve securityParameter queries =
      max (model.parameters securityParameter queries).goodTime
        (model.parameters securityParameter queries).badTime := rfl

example (curve : Model.PairingCurve) [model : BLS.AGMSecurityModel curve]
    (securityParameter : Nat) (queries : BLS.QueryAllowance) :
    BLS.dlogSuccessBound curve securityParameter queries
        (model.parameters securityParameter queries).goodTime ≤
      BLS.dlogSuccessBound curve securityParameter queries
        (BLS.agmReductionTime curve securityParameter queries) :=
  BLS.dlogSuccessBound_mono curve securityParameter queries (Nat.le_max_left _ _)

example (curve : Model.PairingCurve) [model : BLS.CoCDHSecurityModel curve]
    (securityParameter : Nat) (queries : BLS.QueryAllowance) :
    BLS.cocdhReductionTime curve securityParameter queries =
      (model.parameters securityParameter queries).solverTime := rfl

open OracleComp in
example (curve : Model.PairingCurve) [BLS.CoCDHSecurityModel curve]
    (securityParameter : Nat) (queries : BLS.QueryAllowance)
    (adversary : BLS.UnrestrictedAdversary curve securityParameter queries) :
    ∀ pk, IsQueryBoundP (adversary.source pk)
      (fun i => Sum.isRight i = true) queries.sign :=
  (BLS.UnrestrictedAdversary.query_allowances curve securityParameter queries adversary).2.2

example (curve : Model.PairingCurve) [model : BLS.CoCDHSecurityModel curve]
    (securityParameter : Nat) (queries : BLS.QueryAllowance)
    (adversary : BLS.UnrestrictedAdversary curve securityParameter queries) :
    BLS.ROM.AdversaryPK (model.Message securityParameter)
      (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter) := adversary.source

example (curve : Model.PairingCurve) [BLS.CoCDHSecurityModel curve]
    (securityParameter : Nat) (queries : BLS.QueryAllowance)
    (adversary : BLS.UnrestrictedAdversary curve securityParameter queries) :
    𝒟[BLS.cocdhEufCmaGame curve securityParameter adversary] =
      𝒟[BLS.CoCDH.Tight.blsEufLazyPK (F := curve.Scalar securityParameter) (Gₜ := curve.TargetGroup securityParameter)
        (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary.source] :=
  BLS.cocdhEufCmaGame_eq curve securityParameter adversary

end SignaturesTest.GeneralAGMStatement
