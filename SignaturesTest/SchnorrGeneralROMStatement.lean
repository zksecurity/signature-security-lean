import Signatures.Schnorr.Statement
import Signatures.Schnorr.GeneralROMFamilyStatement
import Lean.Util.CollectAxioms

/-! Guard the public ordinary-ROM interface and nonuniform family theorem.
Attackers remain unrestricted; complete reduction resources are derived from
original contracts, and the visible probability bound preserves the query losses. -/

open Lean Meta OracleComp PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr ListROM
open Signatures.Runtime.Schnorr.ListROM.NativeSolver.Family

namespace SignaturesTest.SchnorrGeneralROMStatement

run_meta do
  unless (← findModuleOf? ``Schnorr.rom_security) == some `Signatures.Schnorr.Statement do
    throwError "The public ROM theorem must stay in Statement.lean"
  for name in #[``Schnorr.Proofs.rom_security, ``Schnorr.romEufCmaGame_eq,
      ``Schnorr.romDLogSuccessBound_eq, ``Schnorr.romDLogSuccessBound_mono,
      ``Schnorr.UnrestrictedAdversary.query_allowances] do
    unless (← findModuleOf? name) == some `Signatures.Schnorr.Proofs.GeneralROMSecurity do
      throwError "{name}: supporting proofs must stay separate from the public statement"
  forallTelescope (← getConstInfo ``Schnorr.rom_security).type fun params conclusion => do
    unless params.size == 5 do
      throwError "Expected four explicit inputs and one declared execution model"
    for (param, expected) in params.zip #[`curve, `inst, `securityParameter, `queries, `adversary] do
      let declaration ← getFVarLocalDecl param
      if expected != `inst then
        unless declaration.userName == expected && declaration.binderInfo == .default do
          throwError "Expected explicit public input {expected}"
      else
        unless declaration.binderInfo == .instImplicit do
          throwError "The execution model must be a declared instance"
    for required in #[``Schnorr.romEufCmaGame, ``Schnorr.romDLogSuccessBound,
        ``Schnorr.romReductionTime, ``Model.CyclicCurve.order,
        ``Schnorr.QueryAllowance.hash, ``Schnorr.QueryAllowance.sign] do
      unless (conclusion.find? (fun e => e.isConstOf required)).isSome do
        throwError "Keep the game, DLog budget and original query losses visible"
    if (conclusion.find? (fun e => match e with | .letE .. => true | _ => false)).isSome then
      throwError "Resource records must stay out of the public conclusion"

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Model.forking_inverse, ``Model.negligible_sqrt, ``Model.negligible_of_forking_bound,
      ``NativeSolver.DescriptionInputs.solver_withCaller, ``Schnorr.rom_security,
      ``Schnorr.GeneralROM.reduction_within, ``Schnorr.GeneralROM.security_quadratic,
      ``Schnorr.GeneralROM.security, ``Schnorr.romEufCmaGame_eq,
      ``Schnorr.romDLogSuccessBound_eq, ``Schnorr.romDLogSuccessBound_mono,
      ``Schnorr.UnrestrictedAdversary.query_allowances,
      ``Schnorr.GeneralROM.Family.PolynomialResources.totalQueries,
      ``Schnorr.GeneralROM.Family.PolynomialResources.executionQueries,
      ``Schnorr.GeneralROM.Family.PolynomialResources.solverTime,
      ``Schnorr.GeneralROM.Family.PolynomialResources.solverCode,
      ``Schnorr.GeneralROM.Family.reduction_nonuniform,
      ``Schnorr.GeneralROM.Family.Proofs.security,
      ``Schnorr.GeneralROM.Family.security_asymptotic] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

run_meta do
  for name in #[``Schnorr.rom_security, ``Schnorr.GeneralROM.Parameters.mk,
      ``Schnorr.GeneralROM.UnrestrictedAdversary.mk, ``Schnorr.ROMExecutionModel.mk,
      ``Schnorr.ROMSecurityModel.mk, ``Schnorr.GeneralROM.reduction_within,
      ``Schnorr.GeneralROM.security, ``Schnorr.GeneralROM.Family.PolynomialResources.mk,
      ``Schnorr.GeneralROM.Family.reduction_nonuniform,
      ``Schnorr.GeneralROM.Family.security_asymptotic] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[`Model.PairingCurve, `AlgebraicGroupModel.BilinearPairing,
            ``Bounds, ``Within, ``NonuniformWithin, ``Configuration.within,
            ``Configuration.nonuniformWithin, ``NativeSolver.dlogWithin, ``dlogNonuniformWithin,
            ``GeneralCaller.Budget, ``Program, ``NativeSolver.code,
            ``NativeROMFork.code, ``NativePass.code, ``NativeHandler.code, ``NativeExtraction.code,
            `Signatures.Runtime.AGM.SourceCertificate, `Signatures.Runtime.Schnorr.SourceCertificate,
            ``Schnorr.GeneralROM.Parameters.solverTime, ``Schnorr.GeneralROM.Parameters.solverCode,
            ``NativePass.Resources.arityCap, ``NativePass.Resources.counter] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: forbidden finished budget, restricted syntax or numeric-arity premise {forbidden}"
        if (type.find? (fun e => match e with
            | .const name _ => name.toString.contains ".AGM." || name.toString.contains ".GeneralAGM."
            | _ => false)).isSome then
          throwError "The ordinary-ROM route must not require an algebraic attacker or AGM parameters"
        forallTelescope type fun _ premise => do
          if premise.isAppOf ``Finite || premise.isAppOf ``Fintype || premise.isAppOf ``Inhabited then
            for base in params do
              let declaration ← getFVarLocalDecl base
              if #[`M, `G].contains declaration.userName &&
                  (premise.find? (fun e => e == base)).isSome then
                throwError "{name}: extra finite-domain/default-message requirement"

run_meta do
  let name := ``Schnorr.GeneralROM.Family.security_asymptotic
  forallTelescope (← getConstInfo name).type fun params conclusion => do
    for required in #[`parameters, `config, `fixed, `resources, `adversary, `hardness, `fieldGrowth] do
      unless (← params.anyM fun p => return (← getFVarLocalDecl p).userName == required) do
        throwError "{name}: missing family condition {required}"
    for param in params do
      let declaration ← getFVarLocalDecl param
      let type ← inferType param
      if #[`F, `G, `M].contains declaration.userName then
        unless type.isForall && type.bindingDomain!.isConstOf ``Nat && type.bindingBody!.isSort do
          throwError "Curve/group/message types must vary with the security parameter"
      if declaration.userName == `hardness then
        unless type.isAppOf ``dlogNonuniformHardness do
          throwError "Hardness must cover native solver families in the same fixed backend"
      if declaration.userName == `fixed then
        unless (type.find? (fun e => e.isConstOf ``Schnorr.GeneralROM.Parameters.configuration)).isSome do
          throwError "The backend and cost/description convention must stay fixed across parameters"
    unless conclusion.isAppOf ``negligible &&
        (conclusion.find? (fun e => e.isConstOf ``Schnorr.ROM.game)).isSome do
      throwError "Conclude negligible success in the original ordinary-ROM game"
  unless (← findModuleOf? name) == some `Signatures.Schnorr.GeneralROMFamilyStatement do
    throwError "Keep the family statement in its statement file"
  unless (← findModuleOf? ``Schnorr.GeneralROM.Family.Proofs.security) == some `Signatures.Schnorr.Proofs.GeneralROMFamily do
    throwError "Keep the family proof separate"
  for name in #[``Schnorr.romDLogSuccessBound, ``Schnorr.romEufCmaGame,
      ``Schnorr.GeneralROM.Parameters.descriptions, ``Schnorr.GeneralROM.Parameters.solverTime,
      ``Schnorr.GeneralROM.Parameters.solverCode] do
    unless (← getConstInfo name).value?.isSome do
      throwError "Keep game, hardness and derived resources inspectable"

-- Zero hash queries still leave the explicit final-forgery slot. With zero
-- DLog success and zero inverse-field error, only the signing loss remains.
example {p loss : ENNReal} (hp : p ≠ ⊤) (h : (p - loss) * (p - loss) ≤ 0) : p ≤ loss := by
  simpa using Model.forking_inverse (inverse := 0) (epsilon := 0) 0 hp (by simp) (by simpa using h)

example (curve : Model.CyclicCurve) [model : Schnorr.ROMSecurityModel curve]
    (securityParameter : Nat) (queries : Schnorr.QueryAllowance)
    (adversary : Schnorr.UnrestrictedAdversary curve securityParameter queries) :
    Schnorr.romEufCmaGame curve securityParameter adversary =
      Schnorr.ROM.game (model.parameters securityParameter queries).generator adversary.source :=
  Schnorr.romEufCmaGame_eq curve securityParameter adversary

end SignaturesTest.SchnorrGeneralROMStatement
