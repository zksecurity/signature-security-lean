import Signatures.Schnorr.Statement
import Lean.Util.CollectAxioms

/-! Guard the public Schnorr AGM interface, source-game correspondence and
resource/hardness scope. No pairing, finite message domain, arithmetic attacker
or assumed budget for the finished reduction may be added by the public wrapper. -/

open Lean Meta OracleComp
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.SchnorrAGM.Native

namespace SignaturesTest.SchnorrGeneralStatement

run_meta do
  unless (← findModuleOf? ``Schnorr.agm_security) == some `Signatures.Schnorr.Statement do
    throwError "The public Schnorr theorem must stay in Statement.lean"
  for name in #[``Schnorr.Proofs.agm_security, ``Schnorr.agmEufCmaGame_eq,
      ``Schnorr.dlogSuccessBound_mono, ``Schnorr.AlgebraicAdversary.query_allowances] do
    unless (← findModuleOf? name) == some `Signatures.Schnorr.Proofs.GeneralSecurity do
      throwError "{name}: supporting proof must stay in the separate proof file"
  forallTelescope (← getConstInfo ``Schnorr.agm_security).type fun params _ => do
    unless params.size == 5 do
      throwError "Expected four explicit inputs and one declared execution model"
    for (param, expected) in params.zip #[`curve, `inst, `securityParameter, `queries, `adversary] do
      let declaration ← getFVarLocalDecl param
      if expected != `inst then
        unless declaration.userName == expected && declaration.binderInfo == .default do
          throwError "Expected explicit public input {expected}, found {declaration.userName}"
      else
        unless declaration.binderInfo == .instImplicit do
          throwError "The execution model must be a declared instance"

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Schnorr.agm_security, ``Schnorr.GeneralAGM.reduction_within,
      ``Schnorr.GeneralAGM.security, ``Schnorr.agmEufCmaGame_eq,
      ``Schnorr.dlogSuccessBound_mono, ``Schnorr.AlgebraicAdversary.query_allowances] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

run_meta do
  for name in #[``Schnorr.agm_security, ``Schnorr.GeneralAGM.Parameters.mk,
      ``Schnorr.GeneralAGM.AlgebraicAdversary.mk, ``Schnorr.ExecutionModel.mk,
      ``Schnorr.AGMSecurityModel.mk, ``Schnorr.GeneralAGM.reduction_within,
      ``Schnorr.GeneralAGM.security, ``Model.CyclicCurve.mk] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[`Model.PairingCurve, `BilinearGroup.BilinearPairing,
            ``Bounds, ``GeneralCaller.Budget, ``Solver.program, ``Solver.terminal,
            ``Handler.caller, ``Extraction.code,
            `Signatures.Runtime.AGM.SourceCertificate, `Signatures.Runtime.Schnorr.SourceCertificate] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: forbidden public premise {forbidden}"
        forallTelescope type fun _ premise => do
          if premise.isAppOf ``Finite || premise.isAppOf ``Fintype then
            for base in params do
              let declaration ← getFVarLocalDecl base
              if declaration.userName == `M || declaration.userName == `G then
                if (premise.find? (fun e => e == base)).isSome then
                  throwError "{name}: finite message or group domain premise"

run_meta do
  let type := (← getConstInfo ``Schnorr.agm_security).type
  for visible in #[``Schnorr.agmEufCmaGame, ``Schnorr.dlogSuccessBound,
      ``Schnorr.agmReductionTime, ``Model.CyclicCurve.order,
      ``Schnorr.QueryAllowance.hash, ``Schnorr.QueryAllowance.sign] do
    unless (type.find? (fun e => e.isConstOf visible)).isSome do
      throwError "Public statement must display {visible}"
  if (type.find? (fun e => match e with | .letE .. => true | _ => false)).isSome then
    throwError "Resource records must stay out of the main public statement"
  for name in #[``Schnorr.dlogSuccessBound, ``Schnorr.agmEufCmaGame,
      ``Schnorr.GeneralAGM.Parameters.solverTime, ``Schnorr.GeneralAGM.Parameters.solverCode] do
    unless (← getConstInfo name).value?.isSome do
      throwError "{name}: definition must remain inspectable"

example (curve : Model.CyclicCurve) [Schnorr.AGMSecurityModel curve]
    (securityParameter : Nat) (queries : Schnorr.QueryAllowance)
    (adversary : Schnorr.AlgebraicAdversary curve securityParameter queries) :
    Schnorr.agmEufCmaGame curve securityParameter adversary =
      Schnorr.AGM.game (curve.generator securityParameter) adversary.source :=
  Schnorr.agmEufCmaGame_eq curve securityParameter adversary

example (curve : Model.CyclicCurve) [Schnorr.AGMSecurityModel curve]
    (securityParameter : Nat) (queries : Schnorr.QueryAllowance)
    (adversary : Schnorr.AlgebraicAdversary curve securityParameter queries) :
    ∀ pk, IsQueryBoundP (adversary.source.main (Schnorr.AGM.initial (curve.generator securityParameter) pk))
      (fun q => Schnorr.AGM.Reduction.hashRequest q = true) queries.hash :=
  (Schnorr.AlgebraicAdversary.query_allowances curve securityParameter queries adversary).2.1

example (curve : Model.CyclicCurve) [model : Schnorr.AGMSecurityModel curve]
    (securityParameter : Nat) (queries : Schnorr.QueryAllowance) (time : Nat) :
    Schnorr.dlogSuccessBound curve securityParameter queries time =
      (model.parameters securityParameter queries).dlogBound time := rfl

example (curve : Model.CyclicCurve) [model : Schnorr.AGMSecurityModel curve]
    (securityParameter : Nat) (queries : Schnorr.QueryAllowance) :
    Schnorr.agmReductionTime curve securityParameter queries =
      (model.parameters securityParameter queries).solverTime := rfl

example (curve : Model.CyclicCurve) [Schnorr.AGMSecurityModel curve]
    (securityParameter : Nat) (queries : Schnorr.QueryAllowance) (time largerTime : Nat)
    (h : time ≤ largerTime) :
    Schnorr.dlogSuccessBound curve securityParameter queries time ≤
      Schnorr.dlogSuccessBound curve securityParameter queries largerTime :=
  Schnorr.dlogSuccessBound_mono curve securityParameter queries h

end SignaturesTest.SchnorrGeneralStatement
