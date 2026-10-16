import Signatures.Schnorr.Statement
import Signatures.Schnorr.GeneralNonzeroROMFamilyStatement
import Lean.Util.CollectAxioms

/-! Guard the public nonzero-nonce ROM interface and nonuniform family theorem.
Attackers remain unrestricted; complete reduction resources are derived from
original contracts, and the visible probability bound preserves the query losses. -/

open Lean Meta OracleComp PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr ListROM
open Signatures.Runtime.Schnorr.ListROM.NativeSolver.Family

namespace SignaturesTest.SchnorrGeneralNonzeroROMStatement

run_meta do
  unless (← findModuleOf? ``Schnorr.NonzeroNonce.rom_security) == some `Signatures.Schnorr.Statement do
    throwError "The public ROM theorem must stay in Statement.lean"
  for name in #[``Schnorr.NonzeroNonce.Proofs.rom_security, ``Schnorr.NonzeroNonce.romEufCmaGame_eq,
      ``Schnorr.NonzeroNonce.romDLogSuccessBound_eq, ``Schnorr.NonzeroNonce.romDLogSuccessBound_mono,
      ``Schnorr.NonzeroNonce.UnrestrictedAdversary.query_allowances] do
    unless (← findModuleOf? name) == some `Signatures.Schnorr.Proofs.GeneralNonzeroROMSecurity do
      throwError "{name}: supporting proofs must stay separate from the public statement"
  forallTelescope (← getConstInfo ``Schnorr.NonzeroNonce.rom_security).type fun params conclusion => do
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
    for required in #[``Schnorr.NonzeroNonce.romEufCmaGame, ``Schnorr.NonzeroNonce.romDLogSuccessBound,
        ``Schnorr.NonzeroNonce.romReductionTime, ``Model.CyclicCurve.order,
        ``Schnorr.QueryAllowance.hash, ``Schnorr.QueryAllowance.sign] do
      unless (conclusion.find? (fun e => e.isConstOf required)).isSome do
        throwError "Keep the game, DLog budget and original query losses visible"
    if (conclusion.find? (fun e => match e with | .letE .. => true | _ => false)).isSome then
      throwError "Resource records must stay out of the public conclusion"

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Model.forking_inverse, ``Model.negligible_sqrt, ``Model.negligible_of_forking_bound,
      ``NonzeroListROM.NativeSolver.DescriptionInputs.solver_withCaller, ``Schnorr.NonzeroNonce.rom_security,
      ``Schnorr.NonzeroNonce.GeneralROM.reduction_within, ``Schnorr.NonzeroNonce.GeneralROM.security_quadratic,
      ``Schnorr.NonzeroNonce.GeneralROM.security, ``Schnorr.NonzeroNonce.romEufCmaGame_eq,
      ``Schnorr.NonzeroNonce.romDLogSuccessBound_eq, ``Schnorr.NonzeroNonce.romDLogSuccessBound_mono,
      ``Schnorr.NonzeroNonce.UnrestrictedAdversary.query_allowances,
      ``Schnorr.NonzeroNonce.GeneralROM.Family.PolynomialResources.totalQueries,
      ``Schnorr.NonzeroNonce.GeneralROM.Family.PolynomialResources.executionQueries,
      ``Schnorr.NonzeroNonce.GeneralROM.Family.PolynomialResources.solverTime,
      ``Schnorr.NonzeroNonce.GeneralROM.Family.PolynomialResources.solverCode,
      ``Schnorr.NonzeroNonce.GeneralROM.Family.reduction_nonuniform,
      ``Schnorr.NonzeroNonce.GeneralROM.Family.Proofs.security,
      ``Schnorr.NonzeroNonce.GeneralROM.Family.security_asymptotic] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

run_meta do
  for name in #[``Schnorr.NonzeroNonce.rom_security, ``Schnorr.NonzeroNonce.GeneralROM.Parameters.mk,
      ``Schnorr.NonzeroNonce.GeneralROM.UnrestrictedAdversary.mk, ``Schnorr.ROMExecutionModel.mk,
      ``Schnorr.NonzeroNonce.ROMSecurityModel.mk, ``Schnorr.NonzeroNonce.GeneralROM.reduction_within,
      ``Schnorr.NonzeroNonce.GeneralROM.security, ``Schnorr.NonzeroNonce.GeneralROM.Family.PolynomialResources.mk,
      ``Schnorr.NonzeroNonce.GeneralROM.Family.reduction_nonuniform,
      ``Schnorr.NonzeroNonce.GeneralROM.Family.security_asymptotic] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[`Model.PairingCurve, `AlgebraicGroupModel.BilinearPairing,
            ``Bounds, ``Within, ``NonuniformWithin, ``Configuration.within,
            ``Configuration.nonuniformWithin, ``NativeSolver.dlogWithin, ``dlogNonuniformWithin,
            ``GeneralCaller.Budget, ``Program, ``NativeSolver.code,
            ``NativeROMFork.code, ``NativePass.code, ``NativeHandler.code, ``NativeExtraction.code,
            `Signatures.Runtime.AGM.SourceCertificate, `Signatures.Runtime.Schnorr.SourceCertificate,
            ``Schnorr.NonzeroNonce.GeneralROM.Parameters.solverTime, ``Schnorr.NonzeroNonce.GeneralROM.Parameters.solverCode,
            ``NonzeroListROM.NativePass.Resources.arityCap, ``NonzeroListROM.NativePass.Resources.counter] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: forbidden finished budget, restricted syntax or numeric-arity premise {forbidden}"
        if (type.find? (fun e => match e with
            | .const name _ => name.toString.contains ".AGM." || name.toString.contains ".GeneralAGM."
            | _ => false)).isSome then
          throwError "The nonzero-nonce ROM route must not require an algebraic attacker or AGM parameters"
        forallTelescope type fun _ premise => do
          if premise.isAppOf ``Finite || premise.isAppOf ``Fintype || premise.isAppOf ``Inhabited then
            for base in params do
              let declaration ← getFVarLocalDecl base
              if #[`M, `G].contains declaration.userName &&
                  (premise.find? (fun e => e == base)).isSome then
                throwError "{name}: extra finite-domain/default-message requirement"

run_meta do
  let name := ``Schnorr.NonzeroNonce.GeneralROM.Family.security_asymptotic
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
        unless (type.find? (fun e => e.isConstOf ``Schnorr.NonzeroNonce.GeneralROM.Parameters.configuration)).isSome do
          throwError "The backend and cost/description convention must stay fixed across parameters"
    unless conclusion.isAppOf ``negligible &&
        (conclusion.find? (fun e => e.isConstOf ``Schnorr.NonzeroNonce.game)).isSome do
      throwError "Conclude negligible success in the original nonzero-nonce ROM game"
  unless (← findModuleOf? name) == some `Signatures.Schnorr.GeneralNonzeroROMFamilyStatement do
    throwError "Keep the family statement in its statement file"
  unless (← findModuleOf? ``Schnorr.NonzeroNonce.GeneralROM.Family.Proofs.security) == some `Signatures.Schnorr.Proofs.GeneralNonzeroROMFamily do
    throwError "Keep the family proof separate"
  for name in #[``Schnorr.NonzeroNonce.romDLogSuccessBound, ``Schnorr.NonzeroNonce.romEufCmaGame,
      ``Schnorr.NonzeroNonce.GeneralROM.Parameters.descriptions, ``Schnorr.NonzeroNonce.GeneralROM.Parameters.solverTime,
      ``Schnorr.NonzeroNonce.GeneralROM.Parameters.solverCode] do
    unless (← getConstInfo name).value?.isSome do
      throwError "Keep game, hardness and derived resources inspectable"

-- Zero hash queries still leave the explicit final-forgery slot. With zero
-- DLog success and zero inverse-field error, only the signing loss remains.
example {p loss : ENNReal} (hp : p ≠ ⊤) (h : (p - loss) * (p - loss) ≤ 0) : p ≤ loss := by
  simpa using Model.forking_inverse (inverse := 0) (epsilon := 0) 0 hp (by simp) (by simpa using h)

example (curve : Model.CyclicCurve) [model : Schnorr.NonzeroNonce.ROMSecurityModel curve]
    (securityParameter : Nat) (queries : Schnorr.QueryAllowance)
    (adversary : Schnorr.NonzeroNonce.UnrestrictedAdversary curve securityParameter queries) :
    Schnorr.NonzeroNonce.romEufCmaGame curve securityParameter adversary =
      Schnorr.NonzeroNonce.game (model.parameters securityParameter queries).generator adversary.source :=
  Schnorr.NonzeroNonce.romEufCmaGame_eq curve securityParameter adversary

run_meta do
  forallTelescope (← getConstInfo ``Schnorr.NonzeroNonce.GeneralROM.Parameters.mk).type fun params _ => do
    let mut passes := #[]
    let mut nonzeroSampler := false
    let mut nonzeroLaw := false
    for param in params do
      let type ← inferType param
      let name := (← getFVarLocalDecl param).userName
      if type.isAppOf ``NonzeroListROM.NativePass.Resources then
        passes := passes.push name
      if name == `nonzeroSampler then nonzeroSampler := true
      if name == `nonzeroLaw then nonzeroLaw := true
      for forbidden in #[``ListROM.NativePass.Resources, ``Schnorr.GeneralROM.Parameters,
          ``Schnorr.ROMSecurityModel] do
        if (type.find? (fun e => e.isConstOf forbidden)).isSome then
          throwError "Do not substitute or require the full-field resources"
    unless passes == #[`first, `second] && nonzeroSampler && nonzeroLaw do
      throwError "Preserve both actual nonzero passes and the original nonzero sampler law"
  forallTelescope (← getConstInfo ``Schnorr.NonzeroNonce.rom_security).type fun _ conclusion => do
    unless (conclusion.find? (fun e => e.isAppOfArity ``HSub.hSub 6 &&
        (e.getArg! 0).isConstOf ``Nat)).isSome do
      throwError "Keep the nonzero signing denominator distinct from the full-field forking loss"
  for (name, required) in #[
      (``Schnorr.NonzeroNonce.GeneralROM.reduction_within, ``NonzeroListROM.NativeSolver.program_within),
      (``Schnorr.NonzeroNonce.GeneralROM.Family.Proofs.security, ``Model.negligible_inv_card_sub_one)] do
    let .thmInfo proof ← getConstInfo name | throwError "Expected a proved theorem"
    unless (proof.value.find? (fun e => e.isConstOf required)).isSome do
      throwError "Derive the actual nonzero certificate and nonzero-field growth internally"

-- A curve's finite scalar field supplies the semantic nonzero sampler; its
-- executable implementation and price still belong to the model contracts.
noncomputable example (curve : Model.CyclicCurve) (n : Nat) : SampleableType (curve.Scalar n)ˣ := inferInstance

end SignaturesTest.SchnorrGeneralNonzeroROMStatement
