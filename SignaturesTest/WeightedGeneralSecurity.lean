import Signatures.OOPS.Statement
import Signatures.Proximity.Statement
import Signatures.OOPS.CaliperAGMFamilyStatement
import Signatures.Proximity.CaliperAGMFamilyStatement
import Proofs.OOPS.GeneralAGM
import Proofs.Proximity.GeneralAGM
import Proofs.Runtime.WeightedSecurityModel
import Proofs.Runtime.BackendConfiguration
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Guard general-attacker coverage, source-game preservation, concrete derived
resources and the small public interfaces for weighted signatures. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.WeightedAGM
open Model.LazyAGM

namespace SignaturesTest.WeightedGeneralSecurity

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5

-- The second hash topic depends on a signing reply; signing itself depends on
-- the first hash. Both index tags and the full vector output must be renamed.
private def adaptive : Adversary F (Option (Fin 1) × Nat) ((Fin 1 → F) × Nat) F F where
  main _ := do
    let h : F ← liftM ((advSpec (Option (Fin 1) × Nat) ((Fin 1 → F) × Nat) F).query (.inl (.inr (none, 37))))
    let s : F ← liftM ((advSpec (Option (Fin 1) × Nat) ((Fin 1 → F) × Nat) F).query (.inr (fun _ => h, 37)))
    let topic := if s = 0 then 37 else 38
    let v : F ← liftM ((advSpec (Option (Fin 1) × Nat) ((Fin 1 → F) × Nat) F).query (.inl (.inr (some 0, topic))))
    return ⟨(fun _ => v, topic), 3, [h], [s]⟩

example (pk : F) : (Proximity.GeneralAGM.encodeAdversary (M := Bool) adaptive).main pk = (do
    let h : F ← liftM ((advSpec (Fin 2 × Nat) ((F × Unit) × Nat) F).query (.inl (.inr (0, 37))))
    let s : F ← liftM ((advSpec (Fin 2 × Nat) ((F × Unit) × Nat) F).query (.inr ((h, ()), 37)))
    let topic := if s = 0 then 37 else 38
    let v : F ← liftM ((advSpec (Fin 2 × Nat) ((F × Unit) × Nat) F).query (.inl (.inr (1, topic))))
    return ⟨((v, ()), topic), 3, [h], [s]⟩) := by
  rfl

open Lean Meta

run_meta do
  for (name, moduleName, dimension) in #[
      (``OOPS.agm_security, `Signatures.OOPS.Statement, `degree),
      (``Proximity.agm_security, `Signatures.Proximity.Statement, `dimension)] do
    unless (← findModuleOf? name) == some moduleName do
      throwError "{name}: public theorem must remain in the scheme's Statement module"
    forallTelescope (← getConstInfo name).type fun params _ => do
      unless params.size == 6 do
        throwError "{name}: expected five explicit inputs and one model"
      for (param, expected) in params.zip #[`curve, `inst, `securityParameter, dimension, `queries, `adversary] do
        let decl ← getFVarLocalDecl param
        if expected != `inst && decl.userName != expected then
          throwError "{name}: expected input {expected}, found {decl.userName}"
        if expected != `inst && decl.binderInfo != .default then
          throwError "{name}: public input {expected} must be explicit"
  for (name, moduleName) in #[
      (``OOPS.Proofs.agm_security, `Proofs.OOPS.GeneralSecurity),
      (``OOPS.Proofs.agm_security_common_budget, `Proofs.OOPS.GeneralSecurity),
      (``Proximity.Proofs.agm_security, `Proofs.Proximity.GeneralSecurity),
      (``Proximity.Proofs.agm_security_common_budget, `Proofs.Proximity.GeneralSecurity)] do
    unless (← findModuleOf? name) == some moduleName do
      throwError "{name}: proof must remain in its separate proof file"

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``NativeSolver.challenge_size, ``General.reductions_within,
      ``General.reduction_advantages, ``General.reduction_advantages_of_hardness,
      ``General.mapMain_query_bound, ``Proximity.GeneralAGM.encodeAdversary_query_bound,
      ``Proximity.GeneralAGM.encoded_terms, ``Proximity.GeneralAGM.goodReduction_encoded,
      ``Proximity.GeneralAGM.badReduction_encoded,
      ``OOPS.GeneralAGM.reductions_within, ``Proximity.GeneralAGM.reductions_within,
      ``OOPS.GeneralAGM.security, ``Proximity.GeneralAGM.security,
      ``OOPS.GeneralAGM.security_of_hardness, ``Proximity.GeneralAGM.security_of_hardness,
      ``OOPS.agm_security, ``Proximity.agm_security,
      ``OOPS.agmEufCmaGame_eq, ``Proximity.agmEufCmaGame_eq, ``Proximity.freshCollisionGame_eq,
      ``OOPS.dlogSuccessBound_mono, ``Proximity.dlogSuccessBound_mono,
      ``OOPS.AlgebraicAdversary.query_allowances, ``Proximity.AlgebraicAdversary.query_allowances,
      ``CaliperBackend.WeightedFull.SharedCaller.badCorrespondence,
      ``WeightedCaliper.Parameters.challenge_valid,
      ``WeightedCaliper.Parameters.pair_uniform, ``WeightedCaliper.reductions_within,
      ``WeightedCaliper.Family.reductions_nonuniform,
      ``OOPS.agm_security_asymptotic, ``Proximity.agm_security_asymptotic,
      ``Proximity.agm_security_asymptotic_up_to_collision] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

-- Inspect the constructors too: packaging cannot hide a completed solver budget,
-- finite label domain, restricted arithmetic attacker, or supplied cache condition.
run_meta do
  for name in #[``General.Parameters.mk, ``General.AlgebraicAdversary.mk,
      ``WeightedCaliper.Parameters.mk, ``WeightedCaliper.AlgebraicAdversary.mk,
      ``WeightedCaliper.Family.PolynomialResources.mk,
      ``ExecutionModel.mk, ``OOPS.AGMSecurityModel.mk, ``Proximity.AGMSecurityModel.mk,
      ``OOPS.GeneralAGM.AlgebraicAdversary.mk, ``Proximity.GeneralAGM.AlgebraicAdversary.mk,
      ``General.reductions_within, ``OOPS.GeneralAGM.reductions_within, ``Proximity.GeneralAGM.reductions_within,
      ``OOPS.GeneralAGM.security, ``Proximity.GeneralAGM.security,
      ``OOPS.agm_security, ``Proximity.agm_security] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[``Within, ``Bounds, ``GeneralCaller.Budget,
            ``NativeSolver.ExtractionReady, ``NativeHandler.ReservedState,
            ``Model.LazyAGM.WeightedReduction.TranscriptCached, ``Model.HardWithin,
            ``CaliperBackend.dlogWithin, ``CaliperBackend.dlogNonuniformWithin,
            ``CaliperBackend.Interactive.Within, ``CaliperBackend.Interactive.NonuniformWithin,
            `Signatures.Runtime.AGM.SourceCertificate, `Signatures.Runtime.Coron.SourceCertificate,
            `Signatures.Runtime.Schnorr.SourceCertificate] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: supplied reduction budget, restricted attacker or internal invariant: {forbidden}"
        forallTelescope type fun _ premise => do
          if premise.isAppOf ``Finite || premise.isAppOf ``Fintype then
            for base in params do
              let decl ← getFVarLocalDecl base
              if #[`K, `M, `G₂, `Label].contains decl.userName &&
                  (premise.find? (fun e => e == base)).isSome then
                throwError "{name}: finite topic/slot/message/public-key domain"

-- The public routes must use the actual Caliper solver class and the constructed
-- certificates. The family theorem must preserve the same source game and collision event.
run_meta do
  for (name, required) in #[
      (``OOPS.dlogSuccessBound, #[``CaliperBackend.dlogWithin]),
      (``Proximity.dlogSuccessBound, #[``CaliperBackend.dlogWithin]),
      (``OOPS.Proofs.agm_security, #[``WeightedCaliper.reductions_within]),
      (``Proximity.Proofs.agm_security, #[``WeightedCaliper.reductions_within]),
      (``WeightedCaliper.Family.dlogHardness, #[``CaliperBackend.dlogNonuniformHardness]),
      (``OOPS.agm_security_asymptotic, #[``OOPS.agmEufCmaGame]),
      (``Proximity.agm_security_asymptotic, #[``Proximity.agmEufCmaGame, ``Proximity.freshCollisionGame]),
      (``Proximity.agm_security_asymptotic_up_to_collision,
        #[``Proximity.agmEufCmaGame, ``Proximity.freshCollisionGame])] do
    let info ← getConstInfo name
    let expressions := #[info.type, (info.value? true).getD info.type]
    for symbol in required do
      unless expressions.any (fun expression =>
          (expression.find? (fun e => e.isConstOf symbol)).isSome) do
        throwError "{name}: missing Caliper certificate or original game {symbol}"
    for expression in expressions do
      for forbidden in #[``NativeSolver.dlogWithin, ``Signatures.Runtime.BackendProgram.Configuration.nonuniformWithin] do
        if (expression.find? (fun e => e.isConstOf forbidden)).isSome then
          throwError "{name}: public Caliper route regressed to {forbidden}"
  for (name, moduleName) in #[
      (``OOPS.agm_security_asymptotic, `Signatures.OOPS.CaliperAGMFamilyStatement),
      (``Proximity.agm_security_asymptotic, `Signatures.Proximity.CaliperAGMFamilyStatement),
      (``OOPS.CaliperAGM.Family.Proofs.security, `Proofs.OOPS.CaliperAGMFamily),
      (``Proximity.CaliperAGM.Family.Proofs.security, `Proofs.Proximity.CaliperAGMFamily)] do
    unless (← findModuleOf? name) == some moduleName do
      throwError "{name}: family statements and proofs must remain separate"

run_meta do
  for (name, visible) in #[
      (``OOPS.agm_security, #[``OOPS.agmEufCmaGame, ``OOPS.dlogSuccessBound,
        ``OOPS.agmReductionTime, ``Model.PairingCurve.order]),
      (``Proximity.agm_security, #[``Proximity.agmEufCmaGame, ``Proximity.dlogSuccessBound,
        ``Proximity.agmReductionTime, ``Model.PairingCurve.order, ``Proximity.freshCollisionGame])] do
    let type := (← getConstInfo name).type
    for symbol in visible do
      unless (type.find? (fun e => e.isConstOf symbol)).isSome do
        throwError "{name}: missing visible game/resource/loss term {symbol}"
    if (type.find? (fun e => match e with | .letE .. => true | _ => false)).isSome then
      throwError "{name}: resource-record let-binding in the main statement"
  forallTelescope (← getConstInfo ``Proximity.GeneralAGM.security).type fun _ conclusion => do
    let args := conclusion.getAppArgs
    let lhs := args[args.size - 2]!
    let rhs := args[args.size - 1]!
    if (lhs.find? (fun e => e.isConstOf ``Proximity.DirectAGM.collisionGame)).isSome then
      throwError "Proximity security conditioned away collisions"
    unless (rhs.find? (fun e => e.isConstOf ``Proximity.DirectAGM.collisionGame)).isSome do
      throwError "Proximity security lost its actual source collision term"

end SignaturesTest.WeightedGeneralSecurity
