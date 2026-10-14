import Signatures.BLS.Statement
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
  unless (← findModuleOf? ``BLS.security) == some `Signatures.BLS.Statement do
    throwError "BLS.security must be defined in Signatures.BLS.Statement"

-- Keep both lower-level wrappers small, and the public theorem aligned with
-- curve/security parameter/query allowances/adversary. Resource proofs stay in the records.
run_meta do
  for (name, expected) in #[( ``BLS.GeneralAGM.security, 2), (``BLS.GeneralAGM.Family.security, 3),
      (``BLS.security, 4)] do
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
      ``BLS.security, ``BLS.eufCmaGame_eq, ``BLS.GeneralAGM.reductions_within,
      ``BLS.AlgebraicAdversary.query_allowances] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

run_meta do
  for name in #[``security_of_resources, ``BLS.GeneralAGM.security, ``BLS.GeneralAGM.reductions_within,
      ``BLS.GeneralAGM.Family.security, ``BLS.GeneralAGM.Parameters.mk, ``BLS.GeneralAGM.AlgebraicAdversary.mk,
      ``BLS.security, ``BLS.SecurityModel.mk, ``Model.PairingCurve.mk] do
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

-- The public theorem has exactly the requested concepts, without a preamble
-- of independently supplied fields/groups, encodings, and cost parameters.
run_meta do
  forallTelescope (← getConstInfo ``BLS.security).type fun params _ => do
    unless params.size == 5 do
      throwError "BLS.security must expose four inputs and one declared SecurityModel"
    for (param, expected) in params.zip #[`curve, `inst, `securityParameter, `queries, `adversary] do
      let declaration ← getFVarLocalDecl param
      if expected != `inst && declaration.userName != expected then
        throwError "BLS.security: expected public input {expected}, found {declaration.userName}"

open OracleComp in
example (curve : Model.PairingCurve) [BLS.SecurityModel curve]
    (securityParameter : Nat) (queries : BLS.QueryAllowance)
    (adversary : BLS.AlgebraicAdversary curve securityParameter queries) :
    ∀ pk, IsQueryBoundP (adversary.source.main pk)
      (fun i => BLS.GeneralAGM.queryKind i = 1) queries.hash :=
  (BLS.AlgebraicAdversary.query_allowances curve securityParameter queries adversary).2.1

example (curve : Model.PairingCurve) [BLS.SecurityModel curve]
    (securityParameter : Nat) (queries : BLS.QueryAllowance)
    (adversary : BLS.AlgebraicAdversary curve securityParameter queries) :
    BLS.eufCmaGame curve securityParameter adversary =
      BLS.LazyAGM.game (Gₜ := curve.TargetGroup securityParameter)
        (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary.source :=
  BLS.eufCmaGame_eq curve securityParameter adversary

-- The displayed supremum is the same resource-indexed hardness quantity used
-- by the native solver certificates, for every time allowance.
example (curve : Model.PairingCurve) [model : BLS.SecurityModel curve]
    (securityParameter : Nat) (queries : BLS.QueryAllowance) (time : Nat) :
    BLS.dlogSuccessBound curve securityParameter queries time =
      (model.parameters securityParameter queries).dlogBound time := rfl

end SignaturesTest.GeneralAGMStatement
